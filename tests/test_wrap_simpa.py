#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Regression tests for wrap_simpa.py.

Each test sets up a temporary .lean fixture, runs wrap_simpa.py against
explicit line numbers, and asserts on the resulting file content (for
positive wraps) or that the file is unchanged (for idempotency).

Run from the repo root:
    python3 -m unittest tests.test_wrap_simpa -v
or directly:
    python3 tests/test_wrap_simpa.py
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / 'wrap_simpa.py'
WRAPPER = 'set_option backward.simpa.using.reducibleClose false in'


def run_wrap(file_path: Path, lines: list[int],
             *extra_args: str) -> subprocess.CompletedProcess[str]:
    """Pipe `<file>:<line>` sites into wrap_simpa.py and return the result."""
    sites = '\n'.join(f'{file_path}:{n}' for n in lines)
    return subprocess.run(
        [sys.executable, str(SCRIPT), *extra_args],
        input=sites, text=True, capture_output=True, check=False,
    )


class _FixtureCase(unittest.TestCase):
    """Shared setUp/tearDown: each test gets a fresh temp .lean file."""

    def setUp(self) -> None:
        self._tmpdir = tempfile.TemporaryDirectory()
        self.path = Path(self._tmpdir.name) / 'test.lean'

    def tearDown(self) -> None:
        self._tmpdir.cleanup()

    def write(self, content: str) -> None:
        """Write a dedented fixture; line 1 is the first non-empty line."""
        self.path.write_text(textwrap.dedent(content).lstrip())


class WrapPositionTests(_FixtureCase):
    """Verify the wrapper lands at the right position for each layer
    of decoration the script knows how to walk past."""

    def test_inline_attribute_on_decl_line(self) -> None:
        """Bug #1: `@[simp] theorem foo` matches DECL_RE on its own line.

        Before the fix, the walk-back silently targeted the prior decl.
        """
        self.write("""\
            theorem prev := rfl
            @[simp] theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        body = self.path.read_text()
        self.assertIn(f'{WRAPPER}\n@[simp] theorem foo', body)
        self.assertNotIn(f'{WRAPPER}\ntheorem prev', body)

    def test_stacked_attribute_blocks(self) -> None:
        """Wrapper sits above an entire stack of @[…] blocks."""
        self.write("""\
            @[simp]
            @[to_additive]
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [3])
        body = self.path.read_text()
        self.assertEqual(body.splitlines()[0], WRAPPER)
        self.assertIn('@[simp]\n@[to_additive]\ntheorem foo', body)

    def test_multiline_attribute_with_blank_lines(self) -> None:
        """Bug #7: `@[to_additive /-- multi-paragraph -/]` with blank lines.

        Walk-back used to abort on the first blank line; now it only
        bails on `--` comments / `set_option … in` / decl-keyword lines.
        """
        self.write("""\
            @[to_additive /--
            First paragraph.

            Second paragraph after a blank line.
            -/]
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [6])
        # Wrapper lands at the very top (before the @[to_additive line).
        self.assertEqual(self.path.read_text().splitlines()[0], WRAPPER)

    def test_attribute_with_trailing_line_comment(self) -> None:
        """Bug: `@[ext high] -- This should have higher precedence than X.`
        is still recognised as ending an attribute despite the trailing
        comment. `_strip_trailing_line_comment` handles it so ATTR_END_RE
        sees the `]` after the comment is stripped.

        Without this, the wrapper lands between `@[ext high] -- comment`
        and the decl, which Lean rejects."""
        self.write("""\
            @[ext high] -- This should have higher precedence than `Foo.ext`.
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        body = self.path.read_text()
        # Wrapper goes above the @[ext high] line, comment preserved.
        self.assertEqual(body.splitlines()[0], WRAPPER)
        self.assertIn('@[ext high] -- This should have higher precedence', body)

    def test_attribute_close_with_string_containing_dashes(self) -> None:
        """`--` inside a string literal in an attribute must not be
        mistaken for a trailing line comment."""
        self.write("""\
            @[my_attr "value with -- in it"]
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        body = self.path.read_text()
        # Wrapper at top, attribute line preserved verbatim with its embedded `--`.
        self.assertEqual(body.splitlines()[0], WRAPPER)
        self.assertIn('@[my_attr "value with -- in it"]\ntheorem foo', body)

    def test_attribute_with_named_args(self) -> None:
        """Bug #6: `@[reassoc (attr := simp)]` keeps `:=` inside parens."""
        self.write("""\
            @[reassoc (attr := simp)]
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        body = self.path.read_text()
        self.assertEqual(body.splitlines()[0], WRAPPER)
        self.assertIn('@[reassoc (attr := simp)]\ntheorem foo', body)

    def test_docstring_above_decl(self) -> None:
        """Wrapper goes above a `/-- … -/` docstring."""
        self.write("""\
            /-- A docstring. -/
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        self.assertEqual(self.path.read_text().splitlines()[0], WRAPPER)

    def test_block_comment_is_not_walked_past(self) -> None:
        """Bug #3: `/- regular block comment -/` is not a docstring; the
        wrapper lands BETWEEN the comment and the decl."""
        self.write("""\
            /- A regular block comment. -/
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        lines = self.path.read_text().splitlines()
        self.assertEqual(lines[0], '/- A regular block comment. -/')
        self.assertEqual(lines[1], WRAPPER)

    def test_line_comment_with_brackets_is_not_an_attribute(self) -> None:
        """Bug #2: `-- see Note [lower instance priority]` ends in `]` but
        must not be mis-identified as an attribute close — that would walk
        the wrapper past it onto the wrong (previous) decl.

        The comment is itself walked past as transparent decoration (line
        comments are whitespace to Lean), so the wrapper sits above it.
        The crucial assertion is that `theorem prev` is *not* the one
        getting wrapped."""
        self.write("""\
            @[simp] theorem prev := rfl

            -- see Note [lower instance priority]
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [4])
        body = self.path.read_text()
        # Wrapper goes above the comment; comment stays attached to `theorem foo`.
        self.assertIn(f'{WRAPPER}\n'
                      '-- see Note [lower instance priority]\n'
                      'theorem foo', body)
        # `theorem prev` must not have been touched.
        self.assertNotIn(f'{WRAPPER}\n@[simp] theorem prev', body)

    def test_abbrev_and_example_recognised(self) -> None:
        """Bug #4: `abbrev` and `example` are valid decl kinds."""
        self.write("""\
            abbrev MyNat := Nat
            example : True := by simpa using trivial
        """)
        run_wrap(self.path, [2])
        self.assertIn(f'{WRAPPER}\nexample :', self.path.read_text())

    def test_lone_line_modifier(self) -> None:
        """Bug #8: `noncomputable\\ndef foo` — wrapper must sit above the
        modifier, not between it and the decl. Lean rejects
        `noncomputable set_option ... in def foo`.
        """
        self.write("""\
            noncomputable
            def foo : Nat := by simpa using 0
        """)
        run_wrap(self.path, [2])
        self.assertEqual(self.path.read_text().splitlines()[0], WRAPPER)

    def test_stacked_lone_line_modifiers(self) -> None:
        """Multiple modifiers on consecutive lines, all walked past."""
        self.write("""\
            private
            noncomputable
            def foo : Nat := by simpa using 0
        """)
        run_wrap(self.path, [3])
        self.assertEqual(self.path.read_text().splitlines()[0], WRAPPER)

    def test_multi_token_modifier_line(self) -> None:
        """Several modifiers on a single line (`private noncomputable`)
        as one lone-line block above the decl."""
        self.write("""\
            private noncomputable
            def foo : Nat := by simpa using 0
        """)
        run_wrap(self.path, [2])
        self.assertEqual(self.path.read_text().splitlines()[0], WRAPPER)

    def test_modifier_between_attribute_and_decl(self) -> None:
        """Attribute, then lone modifier, then decl: wrapper above attr."""
        self.write("""\
            @[simp]
            noncomputable
            def foo : Nat := by simpa using 0
        """)
        run_wrap(self.path, [3])
        body = self.path.read_text()
        self.assertEqual(body.splitlines()[0], WRAPPER)
        self.assertIn('@[simp]\nnoncomputable\ndef foo', body)

    def test_modifier_with_existing_set_option(self) -> None:
        """Existing `set_option ... in` above a lone modifier: new wrapper
        goes at the very top, original chain preserved."""
        self.write("""\
            set_option some.other false in
            noncomputable
            def foo : Nat := by simpa using 0
        """)
        run_wrap(self.path, [3])
        body = self.path.read_text()
        self.assertEqual(body.splitlines()[0], WRAPPER)
        self.assertIn(
            f'{WRAPPER}\n'
            'set_option some.other false in\n'
            'noncomputable\n'
            'def foo', body)

    def test_existing_set_option_wrapper_above_attribute(self) -> None:
        """Bug #5: an existing `set_option … in` between an attribute
        and the decl must be walked past, so the new wrapper lands at
        the outermost layer (Lean rejects `@[…] set_option … in <decl>`).
        """
        self.write("""\
            @[simp]
            set_option some.other false in
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [3])
        body = self.path.read_text()
        # New wrapper at the very top; attribute and existing set_option preserved.
        self.assertIn(f'{WRAPPER}\n@[simp]\nset_option some.other false in\ntheorem foo', body)


class IdempotencyTests(_FixtureCase):
    """Re-running the script on already-wrapped decls must SKIP, regardless
    of where in the decoration chain our wrapper sits. Regression test for
    the cascade where adding the set_option walk-back broke the immediate-
    prefix idempotency check."""

    def assertIdempotent(self, lines: list[int]) -> None:
        """Run the script and assert the file is byte-for-byte unchanged."""
        before = self.path.read_text()
        result = run_wrap(self.path, lines)
        after = self.path.read_text()
        self.assertEqual(before, after,
                         f'file was modified;\nstdout was:\n{result.stdout}')
        self.assertIn('SKIP', result.stdout)

    def test_our_wrapper_is_outermost(self) -> None:
        self.write(f"""\
            {WRAPPER}
            set_option some.other false in
            @[simp]
            theorem foo : True := by simpa using trivial
        """)
        self.assertIdempotent([4])

    def test_our_wrapper_in_middle_of_chain(self) -> None:
        """Hits the in-loop `already_wrapped` flag."""
        self.write(f"""\
            set_option backward.foo true in
            {WRAPPER}
            @[simp]
            theorem foo : True := by simpa using trivial
        """)
        self.assertIdempotent([4])

    def test_our_wrapper_innermost(self) -> None:
        """Hits the immediate-prefix path (now via the in-loop check)."""
        self.write(f"""\
            set_option backward.foo true in
            @[simp]
            {WRAPPER}
            theorem foo : True := by simpa using trivial
        """)
        self.assertIdempotent([4])

    def test_our_wrapper_above_docstring(self) -> None:
        """Hits the post-docstring defensive check."""
        self.write(f"""\
            {WRAPPER}
            /-- doc -/
            theorem foo : True := by simpa using trivial
        """)
        self.assertIdempotent([3])

    def test_simple_immediate_prefix(self) -> None:
        """Plain immediate-prefix idempotency — the original case."""
        self.write(f"""\
            {WRAPPER}
            theorem foo : True := by simpa using trivial
        """)
        self.assertIdempotent([2])

    def test_our_wrapper_above_modifier(self) -> None:
        """Bug #8 idempotency: re-running on a decl whose wrapper sits
        above a lone-line `noncomputable` must SKIP."""
        self.write(f"""\
            {WRAPPER}
            noncomputable
            def foo : Nat := by simpa using 0
        """)
        self.assertIdempotent([3])


class CLIBehaviourTests(_FixtureCase):
    """End-to-end checks of CLI flags that don't fit the wrap-position grid."""

    def test_dry_run_does_not_modify_file(self) -> None:
        self.write("""\
            theorem foo : True := by simpa using trivial
        """)
        before = self.path.read_text()
        result = run_wrap(self.path, [1], '--dry-run')
        self.assertEqual(self.path.read_text(), before)
        self.assertIn('WOULD WRAP', result.stdout)

    def test_custom_option_and_value(self) -> None:
        self.write("""\
            theorem foo : True := by simpa using trivial
        """)
        run_wrap(self.path, [1], '--option', 'backward.foo.bar', '--value', 'true')
        self.assertEqual(self.path.read_text().splitlines()[0],
                         'set_option backward.foo.bar true in')

    def test_no_sites_returns_nonzero(self) -> None:
        result = subprocess.run(
            [sys.executable, str(SCRIPT)],
            input='', text=True, capture_output=True, check=False,
        )
        self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
