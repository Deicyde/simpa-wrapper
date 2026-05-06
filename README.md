# wrap-simpa

Bulk-wrap Lean 4 declarations with `set_option … in` to opt out of breaking
behaviour from a Lean PR being tested. Built for Mathlib `lean-pr-testing-*`
adaptation work, where a Lean PR introduces a backward-compat option (e.g.
`backward.simpa.using.reducibleClose` from
[lean4#13636](https://github.com/leanprover/lean4/pull/13636)) and you want
the breakage logged at each failing site for the technical-debt reports
rather than fixed inline.

## Usage

From the root of the repo whose paths the build log mentions
(Mathlib, Batteries, …):

```bash
# Easiest: feed a build log directly.
python3 wrap_simpa.py --from-log build.log

# Or pipe a list of file:line sites via stdin.
grep -E '^error:.*\.lean:[0-9]+:[0-9]+: Type mismatch: After simplification' build.log \
  | sed -E 's/^error: ([^:]+):([0-9]+):.*/\1:\2/' \
  | sort -u \
  | python3 wrap_simpa.py
```

Override the option being applied:

```bash
python3 wrap_simpa.py --option backward.foo.bar --value false --from-log build.log
```

Override the failure-extraction regex (default matches the `simpa using …`
"After simplification" type-mismatch errors):

```bash
python3 wrap_simpa.py --from-log build.log \
    --error-pattern '^error: ([^:]+\.lean):(\d+):\d+: …'
```

The script edits the files in place. Re-running on the same input is a
no-op (idempotency check matches existing `set_option <name>` wrappers).

## What it does

For each `file:LINE` site it walks backward from the failing line:

1. Find the start of the enclosing declaration (`theorem`, `lemma`, `def`,
   `instance`, `example`, optionally preceded by `protected`, `private`,
   `noncomputable`, `nonrec`).
2. Walk past any `@[…]` attribute block above it (handles multi-line
   attributes that close with `]` on a later line, common with
   `@[to_additive /-- … -/]`).
3. Walk past any `/-- … -/` docstring block above that.
4. Insert `set_option <name> <value> in\n` above the result.

Sites within the same file are applied bottom-up so line numbers above the
current edit stay stable.

## Where this came from

Written during the lean-pr-testing-13636 Mathlib + Batteries adaptation —
restricting `simpa using h` to reducible transparency surfaces ~150 failure
sites that are individually correct but rely on β/δ-reduction at the
`simpa` close. Manually wrapping each was a mechanical-but-tedious job; the
script did the last ~70 sites in two batched passes with no manual fixups.

The pattern (Lean PR introduces a backward-compat option, Mathlib needs
many small wraps recorded as tech debt) recurs, so the script is worth
keeping around.

## Caveats

- Doesn't handle `section`/`namespace` openers between docstring and decl
  (rare in practice).
- Top-of-decl line comments (`-- …`) end up *below* the inserted wrapper —
  ugly but harmless.
- The idempotency check is keyed on the option name, so different options
  stack cleanly, but the same option run twice in different invocations is
  caught.
