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
lake env lean examples/CheckUnitIntervalDudley.lean
```

The generated audit section should report empty `sorry_or_admit` and
`custom_axiom_or_constant` arrays. Public theorem axioms should remain limited
to `[propext, Classical.choice, Quot.sound]`, as checked by the Lean example
files.

## Current Next Lanes

- `finite-markov-prequential-risk`: the finite-state, deterministic-start
  path-law bridge, sharp universal `1/4` variance proxy, fixed-predictor
  finite-grid certificate, and fixed-tilt finite-catalog PAC-Bayes certificate
  for `0 < λ < 3` are checked. The PAC-Bayes event is measurable and
  simultaneous over every positive time and posterior PMF, so the posterior
  may be selected after the path is observed. The next reviewable extensions
  are a supplied initial law, predictable or independently trained catalogs,
  and declared finite or normalized countable tilt selection. The result is
  not a same-trajectory fitting theorem, an arbitrary real-tilt optimization
  theorem, a stationarity or mixing theorem, or a continuous-state
  stochastic-dynamics result.

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
  assumptions beyond the current finite-scale wrappers. The unit-interval
  example now verifies the total-bounded bridge on a concrete non-finite
  metric index space, with explicit half/quarter meshes and a supplied
  supremum bound through the projected quarter-mesh Dudley theorem.
- `pac-bayes-all-real-lambda`: the base fixed-tilt, fixed-posterior
  spherical-Gaussian i.i.d. specialization and finite fixed catalogs with
  sample-dependent selection are checked. The finite indicator-Bernstein lane
  additionally has a posterior-uniform weighted tilt catalog; countable or
  all-real lambda optimization and posterior-uniform general continuous
  families remain open.
- `pac-bayes-empirical-bernstein`: the finite per-hypothesis foundation,
  random-matching representation, and source-normalized lower-tail MGF are
  checked for `[0,1]` losses under the explicit finite IID product law and
  sample size at least two. A normalized prior moment now yields one
  fixed-sample, fixed-tilt bad set of mass at most `delta`; outside it, every
  posterior on the finite hypothesis type satisfies the checked comparison
  between its average of per-hypothesis population variances and the
  corresponding empirical average. A separate general bounded-loss Bernstein event now combines with
  that variance event; their union has mass at most the sum of the two declared
  budgets, and outside it every finite posterior satisfies the observable
  fixed-parameter empirical-Bernstein risk bound. Separate finite weighted
  catalogs for the two tilts now support sample- and posterior-dependent
  selection on one shared event. The variance catalog is independently exposed
  and witnessed with unequal weights and two selected branches; the final risk
  layer reuses it rather than duplicating its event. A retained-Bennett joint
  mean/Bessel-variance score and one-event finite joint-pair posterior catalog
  are also checked. The zero-residual coefficient branch now gives an explicit
  selected posterior-risk bound using empirical risk, empirical variance, and
  one KL-plus-catalog-weight confidence term. The other residual branches are
  now closed by an exact attained three-piece maximum on `[0,1/4]`, yielding
  the explicit `xi / t` penalty on the same event. A support-aware countable
  normalized master event and per-entry prior-moment extraction are also
  checked, but their posterior/`xi` selector lift remains open. The current
  result is not all-real tilt optimization or time-uniform inference.
- `sharp-mcdiarmid-product-kernel`: blocked until the product-kernel
  conditional-expectation route is available.
