# Proof Frontier Manifest

`docs/proof-frontier-manifest.json` is a generated index of the current
FormalSLT proof surface. It records source counts, proof-debt scan results,
curated theorem-map entries, and the documented next proof lanes.

The manifest is for review and tooling. It does not replace the Lean checker,
and it does not infer new mathematical dependency structure.

## Regenerate

```bash
python3 scripts/generate_proof_frontier_manifest.py
```

## Check

```bash
python3 scripts/generate_proof_frontier_manifest.py --check
lake build FormalSLT
lake env lean examples/CheckShowcaseTheorems.lean
```

The generated audit section should report empty `sorry_or_admit` and
`custom_axiom_or_constant` arrays. Public theorem axioms should remain limited
to `[propext, Classical.choice, Quot.sound]`, as checked by the Lean example
files.

## Current Next Lanes

- `localized-rademacher-finite-concentration`: finite, reviewable, and now
  packaged through the iid product-weight bad-event adapter with a
  bounded-excess MGF instantiation, fixed-threshold event payoff, and named
  fixed-threshold high-confidence finite-class statement. The sample-dependent
  fast-rate event interface is also named, and a conservative fixed-`ε`
  lower-envelope bridge now controls its bad-event mass under the same
  bounded-excess finite product assumptions. The sample-dependent union-bound
  and shifted exponential-moment adapters are also available, including a
  generic high-confidence wrapper from supplied shifted-moment budgets. A
  conservative bounded-excess shifted-moment instantiation for the named
  fast-rate event is now available through the fixed-`ε` lower envelope. An
  algebraic "centered" interface factors the fixed slack `ε` out of the shifted
  moment, leaving the empirical localized complexity term syntactically inside
  it. This interface is conservative-only: because the localized complexity is
  nonnegative, each per-hypothesis centered moment is pointwise at most the
  fixed moment, so the union bound over it cannot beat the conservative bound.
  It names — but does not discharge — the whole-supremum random-threshold
  obligation for `localizedUpperDeviation - 2·R̂_loc` (localized symmetrization
  plus McDiarmid/Azuma). Separately, the finite Bernstein
  variance-localization route is now closed locally through
  `localizedFiniteClassBernsteinHighConfidence_empirical_nonpos`, which uses a
  Bennett/Bernstein MGF layer, an averaged Bernstein tail, the localized
  variance proxy `c·r`, a finite union bound, and the fixed-threshold payoff.
  The next deeper theorem target is the whole-supremum bound, not a broader
  claim about the finite Bernstein theorem.
- `continuous-dudley-entropy-integral`: requires analytic and measurability
  assumptions beyond the current finite-scale wrappers.
- `pac-bayes-all-real-lambda`: finite-grid extension toward all-real lambda
  optimization.
- `sharp-mcdiarmid-product-kernel`: blocked until the product-kernel
  conditional-expectation route is available.
