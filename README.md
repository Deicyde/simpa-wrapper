# wrap-simpa

Bulk-insert `set_option <name> <value> in` above Lean 4 declarations
named in a build log. Intended for Mathlib `lean-pr-testing-*` work
where a Lean PR introduces a backward-compat option and each failing
site needs to be wrapped individually.

## Install

```bash
git clone https://github.com/Deicyde/simpa-wrapper
```

Requires Python 3.9+. No dependencies.

## Usage

Run from the root of the repo the build log's paths are relative to.

```bash
# From a build log:
python3 wrap_simpa.py --from-log build.log

# From a list of file:line sites on stdin:
python3 wrap_simpa.py < sites.txt
```

### Flags

| Flag | Default | Purpose |
| --- | --- | --- |
| `--option NAME` | `backward.simpa.using.reducibleClose` | Option to set. |
| `--value VAL` | `false` | Option value. |
| `--from-log PATH` | — | Extract sites from a build log instead of stdin. |
| `--error-pattern RE` | matches `Type mismatch: After simplification` | Regex with two groups (file, line) used by `--from-log`. |
| `--dry-run` | off | Print `WOULD WRAP: …` lines without modifying files. |

### Stdin format

One `path/to/File.lean:LINE` per line. Blank lines and non-matching
lines are ignored.

## Behaviour

For each site, walks backward from `LINE` and inserts
`set_option <name> <value> in\n` above:

1. the enclosing decl (`theorem` / `lemma` / `def` / `abbrev` /
   `instance` / `example`, optionally preceded by inline `@[…]`
   attributes and/or
   `protected` / `private` / `noncomputable` / `nonrec`),
2. any stack of `@[…]` attribute blocks above the decl (single-line,
   multi-line `@[to_additive /-- … -/]`, or several stacked blocks),
3. any `/-- … -/` docstring above that.

Block comments (`/- … -/`) and line comments (`-- …`) directly above
the decl are *not* walked past — they stay in place, with the wrapper
landing between them and the decl. This keeps unrelated commentary
attached to wherever it originally was.

Files are edited in place. Sites in the same file are applied
bottom-up so line numbers stay stable. Re-runs are idempotent: a wrap
is skipped if the line above the insertion point already starts with
`set_option <name> `.

## Caveats

- A `section` / `namespace` opener between docstring and decl is not
  recognised.
- A blank line between stacked `@[…]` blocks stops the walk-back; the
  upper attribute then attaches to the wrapper instead of the decl
  (benign).
- The idempotency check is keyed on the option name, so different
  options stack cleanly but the same option run twice is a no-op.

## License

MIT. © 2026 Jack McCarthy. See [LICENSE](LICENSE).
