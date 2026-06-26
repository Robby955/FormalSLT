# Copilot Instructions

FormalSLT is a Lean 4 statistical-learning-theory library. Optimize for small,
reviewable proof steps and accurate theorem statements.

## Proof rules

- Never introduce `sorry`, `admit`, custom `axiom`, or custom `constant`
  declarations.
- Keep public theorem assumptions explicit in the statement.
- Do not broaden a theorem beyond the finite/sample/class/topological scope
  already proved by the code.
- Prefer existing local lemmas and Mathlib APIs before adding a new helper.
- Add helper lemmas only when they remove real duplication or clarify the next
  theorem.

## Style

- Theorem and lemma names follow nearby Mathlib/FormalSLT APIs, including
  descriptive camelCase segments such as `finiteClassUniformDeviationUnionBound`.
- Definitions use `camelCase`.
- Module names use `PascalCase`.
- Public modules need docstrings that state what is proved, proof strategy,
  assumptions, and current boundaries.
- Avoid promotional or apologetic wording. Use precise labels such as "Scope",
  "Assumptions", and "Current boundaries".

## Checks

Before suggesting a PR is ready, run:

```bash
lake exe cache get
lake build FormalSLT
lake env lean examples/CheckShowcaseTheorems.lean
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
git diff --check
```

In a fresh worktree, run `lake exe cache get` before the first build. If
`lake` is not on `PATH`, use `~/.elan/bin/lake` directly. Do not cold-build
Mathlib from source unless cache retrieval fails and the failure is reported.

For a new public theorem, also run:

```bash
printf 'import FormalSLT\n#print axioms <THEOREM_NAME>\n' | lake env lean --stdin
```

The expected public axiom set is `[propext, Classical.choice, Quot.sound]`.

## Scope reminders

- Finite Rademacher, VC, contraction, linear predictor, stability, and
  PAC-Bayes layers are real proved theorem families.
- Dudley/chaining currently has finite entropy-budget and total-bounded
  finite-net bridge infrastructure. Do not call it full continuous Dudley
  unless the exact continuous theorem is present.
- Sharp McDiarmid, continuous-posterior PAC-Bayes, arbitrary infinite classes,
  separability, and measurable suprema over arbitrary classes remain future
  theorem work unless a later module proves them.
