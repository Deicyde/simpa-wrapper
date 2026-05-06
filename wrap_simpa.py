#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Jack McCarthy
"""Bulk-insert `set_option <name> <value> in` above Lean 4 declarations
named in a build log, for Mathlib `lean-pr-testing-*` adaptation work.

For each `path/to/File.lean:LINE` site, walks backward from `LINE` past
any lone-line decl modifiers (`noncomputable`, `private`, …), `@[...]`
attributes, existing `set_option ... in` wrappers, and `/-- ... -/`
docstring above the enclosing decl, then inserts the wrapper. Bottom-up
within each file; idempotent.

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
    r'(?:theorem|lemma|def|abbrev|instance|example)\b'
)
# `/-` opens a block comment; `/--` opens a docstring. We need to
# distinguish them when walking back from a line ending in `-/`.
BLOCK_COMMENT_START_RE = re.compile(r'^\s*/-(?!-)')
ATTR_START_RE = re.compile(r'^\s*@\[')
ATTR_END_RE = re.compile(r'\]\s*$')
DOCSTRING_START_RE = re.compile(r'^\s*/--')
DOCSTRING_END_RE = re.compile(r'-/\s*$')
# Existing `set_option NAME VALUE in` lines that already prefix a decl.
# We must walk past these — Lean rejects an attribute followed by a
# `set_option … in <decl>` (the new wrapper) where it expects the bare
# decl that the attribute attaches to.
SET_OPTION_IN_RE = re.compile(r'^\s*set_option\s+\S+\s+\S+\s+in\s*$')
# Decl modifiers may sit on their own line(s) above the keyword:
#     noncomputable
#     def foo := …
# Lean rejects `noncomputable set_option ... in def foo`, so the wrapper
# has to be inserted *above* any such modifier line, not between it and
# the decl. Matches one or more whitespace-separated modifier tokens with
# nothing else on the line.
_MOD_TOKEN = r'(?:protected|private|noncomputable|nonrec)'
MODIFIER_RE = re.compile(rf'^\s*{_MOD_TOKEN}(?:\s+{_MOD_TOKEN})*\s*$')

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


_LINE_COMMENT_RE = re.compile(r'^\s*--')


def _strip_trailing_line_comment(line: str) -> str:
    """Strip a trailing `-- ...` line comment, if any. Conservatively skips
    when `--` lies inside a string or bracket pair to avoid false positives."""
    depth = 0
    in_string = False
    escape = False
    i = 0
    while i < len(line):
        c = line[i]
        if escape:
            escape = False
        elif c == '\\':
            escape = True
        elif c == '"':
            in_string = not in_string
        elif not in_string:
            if c in '([{':
                depth += 1
            elif c in ')]}':
                depth -= 1
            elif depth == 0 and c == '-' and i + 1 < len(line) and line[i + 1] == '-':
                prefix = line[:i].rstrip()
                return prefix + '\n' if line.endswith('\n') else prefix
        i += 1
    return line


def _is_attribute_end(line: str) -> bool:
    """True iff `line` plausibly closes an `@[...]` attribute block.

    Just checking `endswith(']')` is too loose: line comments like
    `-- see Note [lower instance priority]` end with `]` but are not
    attributes. Reject `--`-comments and lines whose `:=` or `;` lies at
    the *top level* (i.e. not inside any bracket pair) — those tokens
    only appear at top level in declaration bodies, never in attributes.
    Crucially, `@[to_additive (attr := simp)]` and similar named-argument
    attributes contain `:=` inside parentheses, which is fine.

    Also strips a trailing `-- comment` so that
    `@[ext high] -- This should have higher precedence than X.` is still
    recognised as ending an attribute.
    """
    if _LINE_COMMENT_RE.match(line):
        return False
    stripped = _strip_trailing_line_comment(line)
    if not ATTR_END_RE.search(stripped):
        return False
    # Attributes that begin on this line are unambiguous, regardless of
    # what `:=`/`;` they contain inside brackets.
    if stripped.lstrip().startswith('@['):
        return True
    # Otherwise, look for `:=` or `;` *outside* any bracketing, which
    # would indicate this is a declaration body line ending in `]`.
    depth = 0
    i = 0
    while i < len(stripped):
        c = stripped[i]
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0:
            if c == ';':
                return False
            if c == ':' and i + 1 < len(stripped) and stripped[i + 1] == '=':
                return False
        i += 1
    return True


def walk_back_attributes(lines: list[str], idx: int) -> int:
    """Walk past every `@[...]` block immediately preceding `idx`.

    Handles single-line, multi-line (`@[to_additive /-- … -/]`), and
    stacked attribute blocks in any combination. Blank lines, line
    comments, and lines that obviously aren't attribute content
    terminate the walk — important because Lean files routinely contain
    comments like `-- see Note [lower instance priority]` whose trailing
    `]` would otherwise look like an attribute closing.
    """
    while idx > 0 and _is_attribute_end(lines[idx - 1]):
        # Walk back to the `@[...]` opener. Multi-line attributes like
        # `@[to_additive /-- multi-paragraph
        # docstring with blank lines
        # -/]` may contain blank lines (paragraph breaks inside the
        # docstring). Bail only on `--` comments or `set_option … in`/
        # decl-keyword lines, which can't appear inside an attribute.
        opener = -1
        for j in range(idx - 1, -1, -1):
            if ATTR_START_RE.match(lines[j]):
                opener = j
                break
            if (_LINE_COMMENT_RE.match(lines[j]) or
                    SET_OPTION_IN_RE.match(lines[j]) or
                    DECL_RE.match(lines[j])):
                break
        if opener < 0:
            return idx
        idx = opener
    return idx


def walk_back_modifiers(lines: list[str], idx: int) -> int:
    """Walk past lone-line `noncomputable` / `private` / `protected` /
    `nonrec` modifiers immediately preceding `idx`.

    Modifiers between attributes and the decl keyword can sit on their
    own line:
        @[simp]
        noncomputable
        def foo := …
    Lean rejects `noncomputable set_option ... in def foo`, so the
    wrapper has to live above the modifier, not between it and the decl.
    """
    while idx > 0 and MODIFIER_RE.match(lines[idx - 1]):
        idx -= 1
    return idx


def walk_back_docstring(lines: list[str], idx: int) -> int:
    """Walk past one `/-- … -/` docstring block immediately preceding `idx`.

    Carefully distinguishes docstrings (`/-- … -/`, attached to the next
    decl) from regular block comments (`/- … -/`, free-floating). Both
    end in `-/`, but only docstrings should be moved past — a `/-` block
    comment is unrelated commentary and the `set_option ... in` should
    land *between* the comment and the decl (which keeps the comment
    associated with whatever it was originally documenting).
    """
    if idx <= 0 or not DOCSTRING_END_RE.search(lines[idx - 1]):
        return idx
    for i in range(idx - 1, -1, -1):
        if DOCSTRING_START_RE.match(lines[i]):
            return i
        if BLOCK_COMMENT_START_RE.match(lines[i]):
            # It was a `/-`, not `/--`: leave the wrap below the comment.
            return idx
    return idx  # malformed: end-marker without opener


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

    # Walk back through every layer of decoration above the decl, in order
    # from innermost to outermost:
    #
    #   1. lone-line decl modifiers (`noncomputable\n`, `private\n`, …) —
    #      Lean rejects `<modifier> set_option … in <decl>`,
    #   2. existing `set_option … in` wrappers and `@[…]` attribute blocks,
    #      interleaved (Lean rejects `@[…] set_option … in <decl>`, so the
    #      new wrapper must sit at the outermost layer),
    #   3. a `/-- … -/` docstring above all of that.
    #
    # Track whether we walk past our own wrapper at any point — that's what
    # idempotency actually cares about, regardless of where in the chain
    # the existing wrapper sits.
    prefix = f'set_option {option} '
    already_wrapped = False
    insert_idx = decl_idx
    # Iterate until no further movement. Within each iteration, walk past
    # every kind of decoration that can sit above a decl in any order,
    # because Mathlib mixes them freely:
    #   - `set_option … in` wrappers
    #   - lone-line decl modifiers (`noncomputable`, `private`, …)
    #   - `@[…]` attribute blocks (single- and multi-line)
    #   - `/-- … -/` docstrings (single- and multi-line)
    #   - `--` line comments (transparent to Lean)
    # Stop only at blank lines (decl-boundary) or content that doesn't fit
    # any of the above. The wrapper has to sit above the *entire* chain
    # because Lean rejects e.g. `/-- doc -/ set_option … in <decl>`.
    while True:
        prev = insert_idx
        insert_idx = walk_back_attributes(lines, insert_idx)
        insert_idx = walk_back_modifiers(lines, insert_idx)
        while insert_idx > 0:
            above = lines[insert_idx - 1]
            if SET_OPTION_IN_RE.match(above):
                if above.lstrip().startswith(prefix):
                    already_wrapped = True
                insert_idx -= 1
                continue
            if _LINE_COMMENT_RE.match(above):
                insert_idx -= 1
                continue
            break
        insert_idx = walk_back_docstring(lines, insert_idx)
        if insert_idx == prev:
            break

    # Idempotency: skip if the same option already wraps this decl,
    # whether immediately above the insertion point or farther up in the
    # decoration chain.
    if not already_wrapped and insert_idx > 0 and \
            lines[insert_idx - 1].lstrip().startswith(prefix):
        already_wrapped = True
    if already_wrapped:
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
