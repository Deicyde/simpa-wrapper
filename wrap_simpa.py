#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Jack McCarthy
"""Bulk-insert `set_option <name> <value> in` above Lean 4 declarations
named in a build log, for Mathlib `lean-pr-testing-*` adaptation work.

For each `path/to/File.lean:LINE` site, walks backward from `LINE` past
any `@[...]` attributes and `/-- ... -/` docstring above the enclosing
decl, then inserts the wrapper. Bottom-up within each file; idempotent.

See README.md for the full reference.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# --- Patterns ---------------------------------------------------------------

DECL_RE = re.compile(
    r'^\s*'
    # Optional inline attribute(s): `@[simp] ` or `@[simp] @[norm_cast] `.
    r'(?:@\[[^\]]*\]\s+)*'
    # Optional declaration modifiers.
    r'(?:protected\s+|private\s+|noncomputable\s+|nonrec\s+)*'
    # The actual declaration keyword.
    r'(?:theorem|lemma|def|instance|example)\b'
)
ATTR_START_RE = re.compile(r'^\s*@\[')
ATTR_END_RE = re.compile(r'\]\s*$')
DOCSTRING_START_RE = re.compile(r'^\s*/--')
DOCSTRING_END_RE = re.compile(r'-/\s*$')

# Default --error-pattern: matches the simpa "After simplification"
# type-mismatch errors that motivated this script.
DEFAULT_ERROR_PATTERN = (
    r'^error: ([^:]+\.lean):(\d+):\d+: Type mismatch: After simplification'
)

EPILOG = """\
examples:
  python3 wrap_simpa.py --from-log build.log
  python3 wrap_simpa.py --from-log build.log --dry-run
  python3 wrap_simpa.py --option backward.foo.bar --value true < sites.txt
"""


# --- Walk-back helpers ------------------------------------------------------

def find_decl_start(lines: list[str], fail_idx: int) -> int:
    """Index of the first line at-or-above `fail_idx` matching `DECL_RE`, or -1."""
    return next(
        (i for i in range(fail_idx, -1, -1) if DECL_RE.match(lines[i])), -1
    )


def _walk_back_block(
    lines: list[str], idx: int,
    end_re: re.Pattern[str], start_re: re.Pattern[str],
) -> int:
    """If `lines[idx-1]` matches `end_re`, return the index of the line above
    that matches `start_re` (the opener). Else (or if no opener is found)
    return `idx` unchanged.
    """
    if idx <= 0 or not end_re.search(lines[idx - 1]):
        return idx
    for i in range(idx - 1, -1, -1):
        if start_re.match(lines[i]):
            return i
    return idx  # malformed: end-marker without opener


def walk_back_attributes(lines: list[str], idx: int) -> int:
    """Walk past every `@[...]` block immediately preceding `idx`.

    Handles single-line, multi-line (`@[to_additive /-- … -/]`), and
    stacked attribute blocks in any combination. A blank line above an
    attribute terminates the walk.
    """
    while (new := _walk_back_block(lines, idx, ATTR_END_RE, ATTR_START_RE)) < idx:
        idx = new
    return idx


def walk_back_docstring(lines: list[str], idx: int) -> int:
    """Walk past one `/-- … -/` docstring block immediately preceding `idx`."""
    return _walk_back_block(lines, idx, DOCSTRING_END_RE, DOCSTRING_START_RE)


# --- Wrap operation ---------------------------------------------------------

def insert_wrapper(
    file_path: str, fail_line: int, option: str, value: str,
    *, dry_run: bool = False,
) -> bool:
    """Insert (or report) one `set_option ... in` wrap. Returns True if a
    wrap was applied or would be applied; False on skip/error.
    """
    p = Path(file_path)
    lines = p.read_text(encoding='utf-8').splitlines(keepends=True)

    decl_idx = find_decl_start(lines, fail_line - 1)
    if decl_idx < 0:
        print(f"  ERROR: could not find decl for {file_path}:{fail_line}",
              file=sys.stderr)
        return False

    insert_idx = walk_back_docstring(lines, walk_back_attributes(lines, decl_idx))

    # Idempotency: tight prefix match against the line above the insertion
    # point, so the option name only counts when it's actually wrapping.
    prefix = f'set_option {option} '
    if insert_idx > 0 and lines[insert_idx - 1].lstrip().startswith(prefix):
        print(f"  SKIP (already wrapped): {file_path}:{fail_line} "
              f"(decl {decl_idx+1}, insert {insert_idx+1})")
        return False

    preview = lines[insert_idx][:60].rstrip()
    print(f"  {'WOULD WRAP' if dry_run else 'WRAP'}: {file_path}:{fail_line} "
          f"(decl {decl_idx+1}, insert {insert_idx+1}: {preview!r})")

    if not dry_run:
        wrapper = f'set_option {option} {value} in\n'
        p.write_text(
            ''.join(lines[:insert_idx] + [wrapper] + lines[insert_idx:]),
            encoding='utf-8',
        )
    return True


# --- Site extraction --------------------------------------------------------

def _dedupe(sites: list[tuple[str, int]]) -> list[tuple[str, int]]:
    return list(dict.fromkeys(sites))


def parse_sites_from_stdin() -> list[tuple[str, int]]:
    sites = []
    for line in sys.stdin:
        if m := re.match(r'^(.+\.lean):(\d+)$', line.strip()):
            sites.append((m.group(1), int(m.group(2))))
    return _dedupe(sites)


def parse_sites_from_log(log_path: str, pattern: str) -> list[tuple[str, int]]:
    # errors='replace': build logs may carry stray bytes from ANSI escapes;
    # we only care about regex matches against the structured prefix.
    text = Path(log_path).read_text(encoding='utf-8', errors='replace')
    rgx = re.compile(pattern, re.MULTILINE)
    return _dedupe([(m.group(1), int(m.group(2))) for m in rgx.finditer(text)])


# --- CLI --------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description='Wrap Lean declarations with set_option ... in.',
        epilog=EPILOG,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument('--option', default='backward.simpa.using.reducibleClose',
                    help='Option name to set (default: %(default)s)')
    ap.add_argument('--value', default='false',
                    help='Option value (default: %(default)s)')
    ap.add_argument('--from-log', metavar='PATH',
                    help='Extract sites from a build log instead of stdin.')
    ap.add_argument('--error-pattern', default=DEFAULT_ERROR_PATTERN,
                    help='Regex with two groups (file, line) for --from-log.')
    ap.add_argument('--dry-run', action='store_true',
                    help='Print what would be wrapped without modifying files.')
    args = ap.parse_args()

    sites = (parse_sites_from_log(args.from_log, args.error_pattern)
             if args.from_log else parse_sites_from_stdin())
    if not sites:
        print('No sites found.', file=sys.stderr)
        return 1

    by_file: dict[str, list[int]] = {}
    for f, ln in sites:
        by_file.setdefault(f, []).append(ln)

    total = 0
    for f, lns in by_file.items():
        # Bottom-up so earlier line numbers don't shift as we insert above
        # later sites. Sites are already deduped per (file, line) globally.
        for ln in sorted(lns, reverse=True):
            total += insert_wrapper(f, ln, args.option, args.value,
                                    dry_run=args.dry_run)

    label = 'wraps that would be applied' if args.dry_run else 'wraps applied'
    print(f'\nTotal {label}: {total}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
