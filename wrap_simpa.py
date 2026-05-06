#!/usr/bin/env python3
"""Wrap Lean declarations with `set_option ... in` to opt out of breaking
behaviour from a Lean PR being tested.

The script reads a list of `path/to/File.lean:LINE` failure sites and,
for each one, inserts a `set_option <name> <value> in` line above the
declaration that contains the failure — placed correctly above any
docstring + attribute block so the docstring/attributes still attach to
the declaration.

Designed for Mathlib `lean-pr-testing-*` adaptation work where a Lean PR
introduces a backward-compat option (e.g.
`backward.simpa.using.reducibleClose`) and you want to wrap each failing
site individually so the breakage shows up in technical-debt reports.

USAGE
=====

Read a plain list of sites from stdin (one `file:line` per line):

    grep -E '^error:.*\\.lean:[0-9]+:[0-9]+: Type mismatch: After simplification' \\
        build.log \\
      | sed -E 's/^error: ([^:]+):([0-9]+):.*/\\1:\\2/' \\
      | sort -u \\
      | python3 wrap_simpa.py

Or pass a build log directly with --from-log; the same regex extraction
runs internally:

    python3 wrap_simpa.py --from-log build.log

Override the option being applied (default is the one for Lean PR #13636):

    python3 wrap_simpa.py --option backward.foo.bar --value false < sites.txt

Run from the root of the repository the file paths are relative to (Mathlib,
Batteries, etc.) — the script edits paths as given without resolving them.

ALGORITHM
=========

For each site `file:line`, walk backward from `line`:

1. Find the declaration start: the first line beginning with `theorem`,
   `lemma`, `def`, `instance`, or `example` (optionally preceded by
   `protected`, `private`, `noncomputable`, `nonrec`).
2. Walk past any `@[...]` attribute block, including multi-line
   attributes that end with `]` (e.g. `@[to_additive /-- … -/]`).
3. Walk past any `/-- … -/` docstring block, including multi-line ones.
4. Insert `set_option <name> <value> in\\n` above the result.

Sites within the same file are applied bottom-up so that earlier line
numbers stay valid as later lines shift down.

If the line directly above the insertion point already contains a
`set_option <name>` matching ours, the wrap is skipped — so re-running
on the same input is a no-op, and multiple failing sites within one
declaration only wrap it once.

WHAT IT DOESN'T HANDLE
======================

- A `section`/`namespace` opener directly between the docstring and the
  decl (extremely rare in practice).
- Top-of-decl comments (`-- …`); they end up below the inserted wrapper.
- Stacking *different* options idempotently — the skip check is keyed on
  the option name, so different options will accumulate cleanly, but
  the same option run twice in different invocations would be caught.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

DECL_RE = re.compile(
    r'^\s*(?:protected\s+|private\s+|noncomputable\s+|nonrec\s+)*'
    r'(?:theorem|lemma|def|instance|example)\b'
)
ATTR_START_RE = re.compile(r'^\s*@\[')
DOCSTRING_START_RE = re.compile(r'^\s*/--')
DOCSTRING_END_RE = re.compile(r'-/\s*$')

# Matches the simpa-failure errors that motivated this script. Useful for
# --from-log mode. Tweak the pattern via --error-pattern if you want to
# extract sites from differently-shaped failures.
DEFAULT_ERROR_PATTERN = (
    r'^error: ([^:]+\.lean):(\d+):\d+: Type mismatch: After simplification'
)


def find_decl_start(lines: list[str], fail_line_idx: int) -> int:
    """Walk back from `fail_line_idx` (0-based) to the first declaration."""
    i = fail_line_idx
    while i >= 0:
        if DECL_RE.match(lines[i]):
            return i
        i -= 1
    return -1


def walk_back_attribute(lines: list[str], decl_idx: int) -> int:
    """Walk past any `@[...]` block immediately preceding `decl_idx`.

    Handles multi-line attributes whose closing `]` is on a later line
    than the opening `@[` (common with `@[to_additive /-- … -/]`).
    Returns the new index (the line where `@[` begins) or `decl_idx` if
    there is no attribute above.
    """
    i = decl_idx - 1
    if i < 0 or not lines[i].rstrip().endswith(']'):
        return decl_idx
    while i >= 0:
        if ATTR_START_RE.match(lines[i]) or lines[i].lstrip().startswith('@['):
            return i
        i -= 1
    return decl_idx


def walk_back_docstring(lines: list[str], idx: int) -> int:
    """Walk past any `/-- … -/` docstring block ending immediately before `idx`."""
    i = idx - 1
    if i < 0 or not DOCSTRING_END_RE.search(lines[i]):
        return idx
    while i >= 0:
        if DOCSTRING_START_RE.match(lines[i]):
            return i
        i -= 1
    return idx


def insert_wrapper(file_path: str, fail_line: int, option: str, value: str) -> bool:
    """Insert a `set_option ... in` line above the decl containing `fail_line`."""
    p = Path(file_path)
    lines = p.read_text().splitlines(keepends=True)

    fail_idx = fail_line - 1  # 0-based
    decl_idx = find_decl_start(lines, fail_idx)
    if decl_idx < 0:
        print(f"  ERROR: could not find decl for {file_path}:{fail_line}")
        return False

    insert_idx = walk_back_attribute(lines, decl_idx)
    insert_idx = walk_back_docstring(lines, insert_idx)

    set_option_line = f'set_option {option} {value} in\n'
    # Idempotency: skip if the same option is already wrapping this decl.
    if insert_idx > 0 and f'set_option {option} ' in lines[insert_idx - 1]:
        print(
            f"  SKIP (already wrapped): {file_path}:{fail_line} "
            f"(decl at {decl_idx+1}, insert at {insert_idx+1})"
        )
        return False

    preview = lines[insert_idx][:60].rstrip()
    print(
        f"  WRAP: {file_path}:{fail_line} "
        f"(decl at {decl_idx+1}, insert at {insert_idx+1}: {preview!r})"
    )

    new_lines = lines[:insert_idx] + [set_option_line] + lines[insert_idx:]
    p.write_text(''.join(new_lines))
    return True


def parse_sites_from_stdin() -> list[tuple[str, int]]:
    sites = []
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        m = re.match(r'^(.+\.lean):(\d+)$', line)
        if m:
            sites.append((m.group(1), int(m.group(2))))
    return sites


def parse_sites_from_log(log_path: str, pattern: str) -> list[tuple[str, int]]:
    text = Path(log_path).read_text()
    rgx = re.compile(pattern, re.MULTILINE)
    seen = set()
    sites = []
    for m in rgx.finditer(text):
        f, ln = m.group(1), int(m.group(2))
        key = (f, ln)
        if key in seen:
            continue
        seen.add(key)
        sites.append(key)
    return sites


def main() -> int:
    ap = argparse.ArgumentParser(
        description='Wrap Lean declarations with set_option ... in.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument(
        '--option',
        default='backward.simpa.using.reducibleClose',
        help='Option name to set (default: %(default)s)',
    )
    ap.add_argument(
        '--value',
        default='false',
        help='Option value (default: %(default)s)',
    )
    ap.add_argument(
        '--from-log',
        metavar='PATH',
        help='Extract sites from a build log instead of stdin.',
    )
    ap.add_argument(
        '--error-pattern',
        default=DEFAULT_ERROR_PATTERN,
        help='Regex (with two capture groups: file, line) used by --from-log.',
    )
    args = ap.parse_args()

    if args.from_log:
        sites = parse_sites_from_log(args.from_log, args.error_pattern)
    else:
        sites = parse_sites_from_stdin()

    if not sites:
        print('No sites found.', file=sys.stderr)
        return 1

    by_file: dict[str, list[int]] = {}
    for f, ln in sites:
        by_file.setdefault(f, []).append(ln)

    total = 0
    for f, lns in by_file.items():
        # Apply bottom-up within each file so earlier line numbers don't
        # shift as we insert lines above later sites.
        for ln in sorted(set(lns), reverse=True):
            if insert_wrapper(f, ln, args.option, args.value):
                total += 1

    print(f'\nTotal wraps applied: {total}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
