# Formal Statistical Learning Theory in Lean 4

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.30.0--rc2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-25b7ac7-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![Zero sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#audit-commands)
[![Axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-brightgreen.svg)](#audit-commands)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

FormalSLT is a compact Lean 4 library for the finite-sample statistical
learning theory route from empirical risk minimization to VC-style
generalization bounds, with recent extensions for contraction, linear
predictors, finite sub-Gaussian chaining, algorithmic stability, and
finite PAC-Bayes confidence bounds, an initial total-bounded finite-net bridge
for the Dudley lane, a concrete unit-interval Dudley example, and conditional
sub-Gamma probability infrastructure for bounded, conditionally centered
increments.

**56 `FormalSLT/` Lean modules. Zero `sorry`. Zero `admit`. Zero custom axioms.**

Axioms used by the public theorem spine:
`[propext, Classical.choice, Quot.sound]`.

![FormalSLT theorem chain](./docs/theorem-chain.svg)

The core path runs from ERM through Rademacher symmetrization,
high-probability Rademacher bounds, Massart, Sauer-Shelah, the binary VC
bridge, finite contraction, linear predictors, finite sub-Gaussian chaining,
finite Dudley entropy-budget wrappers, finite algorithmic stability, finite
localized-Rademacher scaffolding, finite PAC-Bayes KL/DV/MGF and bounded-loss
confidence bounds, conditional sub-Gamma MGF extraction, and total-bounded
finite-net adapters for the next Dudley steps. The Dudley lane now includes a
unit-interval example with explicit rounded finite meshes, plus a packaged
finite dyadic Dudley API used by the two-point and `Fin n` discrete examples.
The unit-interval supplied supremum has its least-upper-bound property proved
over the full unit interval.

## Where to start

- **For the v0.1 proof surface:** start with
  [FormalSLT v0.1 quickstart](./docs/formalslt-v0.1-quickstart.md).
- **For ML readers:** start with [How to read the proofs](./docs/how-to-read-the-proofs.md),
  then [Intuition](./docs/intuition.md).
- **For proof structure:** see [Diagrams](./docs/diagrams.md).
- **For exact theorem names:** use [Theorem map](./docs/theorem-map.md).
- **For the conditional sub-Gamma extractor:** see
  [Conditional Sub-Gamma Extractor](./docs/subgamma-extractor.md).
- **For the non-finite unit-interval Dudley example:** see
  [Unit-Interval Dudley Example](./docs/unit-interval-dudley.md).
- **For the second reusable dyadic-net instantiation:** see
  [the two-point handoff note](./docs/formalslt-goal7-second-dyadic-net-instantiation-2026-06-01.md).
- **For the finite discrete dyadic-net family:** see
  [FormalSLT v0.1 quickstart](./docs/formalslt-v0.1-quickstart.md).
- **For a generated proof-surface index:** see
  [Proof frontier manifest](./docs/proof-frontier.md).
- **For scope and assumptions:** read
  [Scope and assumptions](./docs/assumptions-and-nonclaims.md).
- **For contributors:** read [Contributing](./CONTRIBUTING.md), then
  [Good first issues](./docs/good-first-issues.md).
- **For related Lean projects:** see [Related work](./docs/related-work.md).
  FormalSLT is scoped as a finite-class theorem spine and is complementary to
  existing empirical-process and Rademacher-generalization formalizations.

## Checked theorem spine

FormalSLT records finite-sample statistical learning bounds as Lean theorems
with explicit hypotheses and constants. The current public spine includes:

- finite-class ERM, symmetrization, Massart, Sauer-Shelah, and VC-style
  sample-complexity bounds;
- high-probability Rademacher bounds with the Azuma `8B²` exponent;
- finite contraction, linear-predictor, chaining, stability, and PAC-Bayes
  components;
- a conditional sub-Gamma MGF extractor for bounded, conditionally centered
  real increments with an explicit conditional second-moment proxy.

## Theorem families

| Family | Main modules | Representative result | Status |
|---|---|---|---|
| Finite-class ERM | `Risk`, `ERM`, `Rademacher.ERMGeneralization` | Excess risk controlled by uniform deviation | Verified |
| Rademacher symmetrization | `GhostSample`, `Rademacher.Symmetrization` | `E[genGap] ≤ 2 * E[Rad]` | Verified |
| High-probability Rademacher | `Azuma.*`, `Rademacher.HighProbability` | `P(genGap ≥ 2 * E[Rad] + ε) ≤ exp(-ε² n / (8B²))` | Verified |
| Massart finite-class bound | `Rademacher.Massart` | `Rad(H,S) ≤ B * sqrt(2 * log card(H) / n)` | Verified |
| Binary VC route | `VC.SauerShelah`, `VC.BinaryVCBridge`, `VC.SampleComplexity` | VC-style ERM excess-risk tail and closed sample-complexity form via effective classes | Verified |
| Finite contraction | `Rademacher.Contraction` | `Rad_S(φ ∘ F) ≤ L * Rad_S(F)` for scalar finite samples/classes | Verified |
| Linear predictors | `Rademacher.LinearPredictor` | `Rad ≤ R * n⁻¹ * sqrt(∑ k, ‖z k‖²)` and `Rad ≤ R * B / sqrt n` | Verified |
| Finite Bernstein concentration | `Probability.BernsteinMGF`, `Rademacher.Localized` | finite Bennett/Bernstein MGF, averaged Bernstein tail, and finite localized Bernstein high-confidence theorem | Verified finite route |
| Conditional sub-Gamma extraction | `Concentration.SubGamma.*` | `condSubGammaMGF_of_bounded_centered_condVariance`: bounded, conditionally centered increments with a conditional second-moment proxy satisfy a conditional sub-Gamma MGF bound | Verified probability infrastructure |
| Localized Rademacher scaffold | `Rademacher.Localized` | Bernstein localization, localized upper-deviation events, shifted-moment adapters, bounded-excess MGF instantiation, finite product-weight bad-event adapters, and event-facing wrappers | Verified finite scaffold |
| Finite covering and two-scale chaining | `Covering.Rademacher`, `Covering.DudleyChaining` | ε-net peeling and two-scale finite chaining | Verified |
| Finite sub-Gaussian chaining foundation | `Covering.FiniteSubGaussianChaining` | finite-max entropy bounds, finite Dudley-style entropy-budget sums, and the packaged `FiniteDyadicDudleyInstance` API | Verified finite infrastructure |
| Total-bounded Dudley bridge | `Covering.TotalBoundedDudley` | totally bounded metric spaces yield dyadic finite-net schedules, projected finite-net wrappers, truncated interval-integral entropy comparisons, and supplied-supremum / finite-skeleton / pathwise-modulus / epsilonized boundary adapters | Verified bridge |
| Unit-interval Dudley example | `Covering.UnitIntervalDudley` | `[0,1]` as a non-finite index space with rounded dyadic meshes, projection-pair entropy, and a supplied-supremum projected-mesh Dudley bound for `X(b,t)=sign(b)*t` | Verified example |
| Two-point dyadic-net example | `Covering.TwoPointDudley` | second concrete `FiniteDyadicDudleyInstance`, showing the packaged finite Dudley wrapper is not tied to `[0,1]` | Verified example |
| Finite discrete dyadic-net family | `Covering.FiniteDiscreteDudley` | general `FiniteDyadicDudleyInstance` for `Fin n` with the discrete metric, an embedded Rademacher process, and explicit `n * n` cover-count envelope | Verified API example |
| Algorithmic stability | `AlgorithmicStability`, `Stability.BousquetElisseeff` | bounded-differences constants, finite and product-measure expected-gap wrappers with bound `β`, bounded-loss measurability adapters, and bounded-loss Azuma-constant concentration wrappers | Verified finite scaffold |
| PAC-Bayes finite confidence layer | `PACBayesKL`, `PACBayesMcAllester`, `PACBayesFiniteProductMGF`, `PACBayesBoundedLoss` | finite KL/DV change-of-measure, bounded-loss Catoni-style bound, closed PAC-Bayes good-event payoff, fixed-budget McAllester corollary, and finite-grid McAllester peeling wrapper | Verified finite layer |

## Scope and assumptions

The main generalization theorems are intentionally finite and explicit.

| Scope item | Current state |
|---|---|
| Hypothesis classes | Finite index types unless a theorem states a separate finite net/family |
| Samples | Finite iid samples through product measures |
| Losses/processes | Scalar real-valued, with boundedness or finite sub-Gaussian MGF assumptions |
| Conditional MGF layer | Bounded, conditionally centered real increments with an explicit conditional second-moment proxy |
| Constants | High-probability Rademacher bounds use the Azuma `8B²` exponent |
| Chaining | Finite nets/images, finite support/outcome spaces, finite entropy sums; the unit-interval example instantiates the bridge on a non-finite metric index space with explicit finite meshes |
| Public axiom target | `[propext, Classical.choice, Quot.sound]` only |

## Open work

Short version:

- The main Rademacher and VC results are finite-class and finite-sample
  theorems.
- High-probability Rademacher bounds use the Azuma `8B²` exponent; the sharper
  McDiarmid constant is not yet implemented.
- The chaining layer proves finite entropy-budget infrastructure and an initial
  total-bounded finite-net extraction bridge, not the continuous Dudley
  integral.
- PAC-Bayes includes a finite `[0,1]` bounded-loss Catoni-style confidence
  bound, a closed high-confidence good-event theorem, a fixed-budget
  McAllester-style square-root corollary, and a
  finite-grid peeling wrapper for posterior-dependent penalties. Exact
  all-real-`λ`, infinite-hypothesis, and continuous-posterior variants are not
  yet implemented.
- Algorithmic stability includes finite iid and measure-theoretic iid
  expected-gap wrappers, plus bounded-loss high-probability wrappers for
  finite measurable hypothesis interfaces.

For the full scope statement, see
[Scope and assumptions](./docs/assumptions-and-nonclaims.md).

## Installation

This project requires [elan](https://github.com/leanprover/elan), the Lean
toolchain manager. `elan` will read [`lean-toolchain`](./lean-toolchain) and
fetch the pinned Lean version automatically.

```bash
git clone https://github.com/Robby955/FormalSLT.git
cd FormalSLT
lake exe cache get      # download pre-built Mathlib oleans
lake build FormalSLT    # build the library
```

If `lake` is not on your shell path, use the elan binary directly:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build FormalSLT
```

The first build takes a few minutes (downloading the Mathlib cache); after
that, builds are incremental.

## Release-candidate checks

Run these before treating a branch as a showcase candidate:

```bash
lake exe cache get
lake build FormalSLT
lake env lean examples/CheckV01Usability.lean
lake env lean examples/CheckShowcaseTheorems.lean
lake env lean examples/CheckSubGammaExtractor.lean
lake env lean examples/CheckUnitIntervalDudley.lean
lake env lean examples/CheckTwoPointDudley.lean
lake env lean examples/CheckFiniteDiscreteDudley.lean
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/check_doc_anchors.py \
  docs/formalslt-v0.1-technical-note.md \
  docs/formalslt-v0.1-artifact-map-2026-06-01.md \
  docs/formalslt-v0.1-release-review-2026-06-01.md \
  docs/theorempath-formalslt-v0.1-page-draft.mdx
```

## Audit commands

Use the release-candidate checks above, then run the proof-debt and whitespace
audits:

```bash
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/check_doc_anchors.py \
  docs/formalslt-v0.1-technical-note.md \
  docs/formalslt-v0.1-artifact-map-2026-06-01.md \
  docs/formalslt-v0.1-release-review-2026-06-01.md \
  docs/theorempath-formalslt-v0.1-page-draft.mdx
git diff --check
```

The expected result is:

- `lake build FormalSLT` exits successfully;
- `examples/CheckV01Usability.lean` resolves the v0.1 citation targets and
  prints standard Lean/Mathlib axioms for the bundled confidence-sequence API,
  the dyadic-net sequence API, and the concrete dyadic-net instances;
- `examples/CheckShowcaseTheorems.lean` prints standard Lean/Mathlib axioms
  for selected public theorems;
- `examples/CheckSubGammaExtractor.lean` prints standard Lean/Mathlib axioms
  for the conditional sub-Gamma extractor and its helper lemmas;
- `examples/CheckUnitIntervalDudley.lean` prints standard Lean/Mathlib axioms
  for the concrete unit-interval Dudley example;
- `examples/CheckTwoPointDudley.lean` prints standard Lean/Mathlib axioms
  for the second dyadic-net example;
- `examples/CheckFiniteDiscreteDudley.lean` prints standard Lean/Mathlib
  axioms for the finite discrete embedded Rademacher dyadic-net family;
- the `rg` commands find no executable `sorry`, no executable `admit`, and no
  custom axioms/constants in `FormalSLT` or `examples`;
- the proof-frontier manifest is in sync with the theorem map and source counts;
- documented `FormalSLT/...lean:line` anchors point at the named declarations;
- `git diff --check` reports no whitespace errors.

## Module map

| Layer | Modules |
|---|---|
| Core definitions | `Risk`, `ERM`, `UniformConvergence`, `GhostSample` |
| Probability utilities | `Probability.Concentration`, `Probability.FiniteUnionBound`, `Probability.FiniteExpectation` |
| Conditional sub-Gamma infrastructure | `Concentration.SubGamma.BennettBound`, `Concentration.SubGamma.BoundedExpIntegrable`, `Concentration.SubGamma.CondExpProduct`, `Concentration.SubGamma.CondJensen`, `Concentration.SubGamma.CondMarkov`, `Concentration.SubGamma.CondVarianceFromSquare`, `Concentration.SubGamma.Extractor` |
| Rademacher route | `Rademacher.FiniteSample`, `Rademacher.FiniteSampleSymmetrization`, `Rademacher.ProbabilityBridge`, `Rademacher.Decoupling`, `Rademacher.Symmetrization`, `Rademacher.Massart`, `Rademacher.HighProbability`, `Rademacher.FiniteClassHighProb`, `Rademacher.UniformDeviation`, `Rademacher.ERMGeneralization`, `Rademacher.Contraction`, `Rademacher.LinearPredictor`, `Rademacher.Localized` |
| Azuma infrastructure | `Azuma.ExposureMartingale`, `Azuma.BoundedDifferences`, `Azuma.BoundedDiffMartingale`, `Azuma.BoundedDiffsAzumaInput`, `Azuma.BoundedIncrementBound`, `Azuma.HasBoundedDifferences`, `Azuma.ExposureIncrementHoeffding`, `Azuma.ExposureIncrementCondMGF`, `Azuma.GenGapTail` |
| VC route | `VC.Dimension`, `VC.PACBridge`, `VC.SauerShelah`, `VC.Rademacher`, `VC.SampleComplexity`, `VC.BinaryVCBridge` |
| Covering and chaining | `Covering.Rademacher`, `Covering.DudleyChaining`, `Covering.FiniteSubGaussianChaining`, `Covering.TotalBoundedDudley`, `Covering.UnitIntervalDudley`, `Covering.TwoPointDudley`, `Covering.FiniteDiscreteDudley` |
| Stability and PAC-Bayes foundations | `AlgorithmicStability`, `Stability.BousquetElisseeff`, `PACBayesKL`, `PACBayesMcAllester`, `PACBayesFiniteProductMGF`, `PACBayesBoundedLoss` |

## Roadmap

- [x] Finite-sample Rademacher definitions
- [x] Rademacher symmetrization
- [x] Massart finite-class bound
- [x] Azuma-Hoeffding genGap tail
- [x] High-probability Rademacher bound
- [x] Sauer-Shelah polynomial bound
- [x] VC-style pointwise Rademacher
- [x] VC uniform deviation and ERM excess-risk tail
- [x] VC closed-form ERM sample-complexity theorem
- [x] Binary-class VC to effective loss-pattern bridge
- [x] Finite-sample scalar contraction
- [x] Finite-dimensional linear predictor Rademacher bound
- [x] Finite localized Rademacher/Bernstein variance-localization scaffold
- [x] Conditional sub-Gamma MGF extractor from boundedness, conditional
  centering, and a conditional second-moment proxy
- [x] Covering number peeling and two-scale chaining
- [x] Finite sub-Gaussian max and finite chaining entropy budgets
- [x] Algorithmic stability bounded-differences scaffold
- [x] Finite algorithmic stability expected-gap adapter under coordinate-swap identity
- [x] Finite iid coordinate-swap identity and literal expected-generalization-gap specialization
- [x] Finite iid two-sided algorithmic stability expected-gap wrappers
- [x] PAC-Bayes KL divergence and Donsker-Varadhan variational inequality
- [x] PAC-Bayes finite iid product MGF bridge for empirical-risk deviations
- [x] PAC-Bayes bounded-loss MGF, Markov confidence, and finite Catoni-style bound
- [x] PAC-Bayes closed high-confidence generalization payoff theorem
- [x] PAC-Bayes fixed-budget McAllester-style square-root corollary
- [x] PAC-Bayes finite-grid McAllester peeling and optimized finite-grid wrapper
- [x] Finite Dudley discrete entropy-bound refinements: annulus, integral-budget,
  and prefix-envelope wrappers
- [x] Total-bounded finite-net extraction bridge for the continuous Dudley lane
- [x] Projected-sup total-bounded dyadic Dudley wrapper
- [x] Projected finite-net total-bounded dyadic Dudley wrapper without finite
  ambient index type
- [x] Finite dyadic-budget to entropy-at-radius upper-sum comparison
- [x] Shifted finite-annulus entropy budget collapsed to one truncated interval
  integral
- [x] Supplied-supremum boundary adapter with explicit terminal approximation
  error
- [x] Finite-skeleton/dense-net boundary adapter with explicit separability and
  terminal projection errors
- [x] Pathwise-modulus and finite-skeleton witness lemmas that discharge the
  continuous-boundary adapter hypotheses
- [x] Epsilonized finite-choice boundary adapter: every positive error budget
  can be discharged by a finite skeleton and terminal dyadic scale certificate
- [x] Finite-cover/pathwise-modulus certificate for the epsilonized
  total-bounded Dudley boundary layer
- [x] Dudley boundary epsilon elimination under a uniform global finite-budget
  hypothesis
- [x] Separable-terminal Dudley boundary adapter under explicit finite-skeleton
  and terminal-projection hypotheses
- [x] Pathwise terminal-modulus constructor for separable-terminal Dudley
  boundary certificates
- [x] Finite-cover/pathwise-modulus bridge into the separable-terminal Dudley
  boundary interface
- [x] Finite-terminal total-bounded dyadic Dudley wrapper
- [x] Concrete unit-interval Dudley example with explicit half/quarter meshes
  and a supplied-supremum projected-mesh bound
- [ ] Continuous Dudley entropy-integral theorem over total-bounded classes
- [x] Measure-theoretic iid algorithmic stability expected bound, with explicit
  integrability assumptions
- [x] Bounded-loss measurability adapters for the measure-theoretic stability
  expected-gap theorem
- [x] Bounded-loss high-probability stability wrappers for finite measurable
  hypothesis interfaces
- [ ] PAC-Bayes all-real-`λ` or continuous-posterior extensions
- [ ] Sharp McDiarmid/product-kernel decomposition
- [ ] Continuous Dudley-style entropy integral

## Dependencies

- [Lean 4](https://lean-lang.org/) v4.30.0-rc2
- [Mathlib4](https://github.com/leanprover-community/mathlib4) @ `25b7ac7`

## Contributing

Contributions are welcome. Please read [CONTRIBUTING.md](./CONTRIBUTING.md)
before opening a PR. The short version: one theorem per PR, no `sorry` / no
`admit`, only the standard `[propext, Classical.choice, Quot.sound]` axioms,
and assumptions stated in the type signature rather than buried in
hypotheses.

For ideas, see the [open-formalization-problems](./docs/open-formalization-problems.md)
list, [good first issues](./docs/good-first-issues.md), and the unchecked items
in the roadmap above. Before a public release, maintainers can use the
[public release checklist](./docs/public-release-checklist.md).

## Citation

If you use FormalSLT in academic work, please cite:

```bibtex
@software{formal_slt,
  title  = {FormalSLT: Formal Statistical Learning Theory in Lean 4},
  author = {Sneiderman, Robert},
  year   = {2026},
  url    = {https://github.com/Robby955/FormalSLT},
  note   = {Lean 4 formalization of finite-sample SLT bounds.}
}
```

## License

This project is released under the [MIT License](./LICENSE).
