# Formal Statistical Learning Theory in Lean 4

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.30.0--rc2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-25b7ac7-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![Zero sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#audit-commands)
[![Axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-brightgreen.svg)](#audit-commands)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

FormalSLT is a Lean 4 library for checking finite-sample statistical learning
theory proof chains. The current v0.1 surface is organized around two checked
endpoints:

1. a finite-class, countable-time Hoeffding confidence sequence for `[0,1]`
   losses; and
2. a finite-net Dudley bridge for a concrete process indexed by the non-finite
   unit interval `[0,1]`.

The repository also packages reusable dyadic Dudley API instances for a
two-point metric space and for finite discrete spaces `Fin n`. Those examples
are API checks: they show that the finite-net wrapper is reusable outside the
unit-interval file.

The concentration layer now carries the sharp McDiarmid bounded-differences
inequality over a homogeneous product measure. For a function whose value
changes by at most `c k` when coordinate `k` is altered, the library proves the
one-sided tail `exp(-2ε²/∑ₖcₖ²)` (`mcdiarmid_of_hasBoundedDifferences_sharp`),
its lower-tail form (`mcdiarmid_of_hasBoundedDifferences_sharp_lower`), and the
two-sided bound `2·exp(-2ε²/∑ₖcₖ²)`
(`mcdiarmid_twoSided_of_hasBoundedDifferences_sharp`). The sharp `2B²` exponent
is propagated into the high-probability Rademacher, finite-class, VC, and
algorithmic-stability wrappers listed below, replacing the looser Azuma `8B²`
constant on those paths. The localized-Rademacher wrapper still uses the older
Azuma constant. The bounded-differences theorem is stated for the same product
law in each coordinate, not for arbitrary non-iid product spaces.

The PAC-Bayes layer now includes a finite Bernstein margin-proxy shell. It
adds a supplied per-hypothesis variance proxy, a normalized Bernstein
prior-moment certificate, fixed-`λ` finite bad-event bounds, and a
posterior-dependent square-root-plus-linear wrapper. This is a supplied-proxy
finite shell: it is not yet a concrete classifier-margin extractor, an
all-real-`λ` optimization theorem, or a continuous hypothesis-space theorem.

**60 `FormalSLT/` Lean files. 85 checked Lean files under `FormalSLT/` and
`examples/`. 33,427 lines. Zero `sorry`. Zero `admit`. Zero custom axioms.**

Counts are generated with `find FormalSLT -name '*.lean'`, `find FormalSLT
examples -name '*.lean'`, and `find FormalSLT examples -name '*.lean' -print0 |
xargs -0 wc -l`.

The printed axiom profile for the v0.1 headline surface stays inside:
`[propext, Classical.choice, Quot.sound]`.

![FormalSLT theorem chain](./docs/theorem-chain.svg)

## What v0.1 Proves

| Surface | Main checked endpoint | Checker |
|---|---|---|
| Finite-class Hoeffding confidence sequence | `FiniteClassConfidenceSequence.failure_probability_le` | `examples/CheckUniformConvergence.lean` |
| Unit-interval finite-net Dudley bridge | `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree` | `examples/CheckUnitIntervalDudley.lean` |
| Packaged finite dyadic Dudley API | `FiniteDyadicDudleyInstance.suppliedSup_dudley_bound` | `examples/CheckV01Usability.lean` |
| Two-point dyadic Dudley instance | `twoPointDudleyInstance` | `examples/CheckTwoPointDudley.lean` |
| `Fin n` discrete dyadic Dudley instance | `finDiscreteDudleyInstance` | `examples/CheckFiniteDiscreteDudley.lean` |
| Two-sided sharp McDiarmid over a homogeneous product measure | `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp` | `FormalSLT/Test/SharpMcDiarmidTest.lean` |
| PAC-Bayes Bernstein supplied margin-proxy shell | `finitePACBayesBernsteinMargin_badEventMass_le_delta` | `examples/CheckPACBayesBernstein.lean` |

The confidence-sequence chain makes the finite-class and countable-time union
bound explicit. The Dudley chain connects finite sub-Gaussian chaining to a
non-finite metric index space by constructing rounded dyadic finite nets and
checking the supplied supremum for the concrete process
`X(b,t) = signOfBool b * t`.

## Fast Verification

From the repository root:

```bash
lake exe cache get
lake build FormalSLT
lake env lean examples/CheckV01Usability.lean
lake env lean examples/CheckUniformConvergence.lean
lake env lean examples/CheckUnitIntervalDudley.lean
lake env lean examples/CheckTwoPointDudley.lean
lake env lean examples/CheckFiniteDiscreteDudley.lean
lake env lean examples/CheckPACBayesBernstein.lean
python3 scripts/generate_proof_frontier_manifest.py --check
```

If `lake` is not on the shell path, use `~/.elan/bin/lake`.

## What v0.1 Does Not Prove

- No full continuous Dudley entropy-integral theorem.
- No arbitrary measurable-supremum construction over non-finite classes.
- No general separability theorem.
- No infinite-class confidence sequence.
- No martingale or e-process stopping theorem in the v0.1 confidence-sequence
  surface.
- No neural-network generalization theorem.

## Where to start

- **For the v0.1 proof surface:** start with
  [FormalSLT v0.1 quickstart](./docs/formalslt-v0.1-quickstart.md).
- **For the v0.1 technical note:** read
  [FormalSLT v0.1 technical note](./docs/formalslt-v0.1-technical-note.md).
- **For TheoremPath packaging:** read
  [TheoremPath FormalSLT v0.1 draft](./docs/theorempath-formalslt-v0.1-page-draft.mdx).
- **For the live walkthrough:** see
  [theorempath.com/theorems/formalslt-v0-1](https://theorempath.com/theorems/formalslt-v0-1).
- **For ML readers:** start with [How to read the proofs](./docs/how-to-read-the-proofs.md),
  then [Intuition](./docs/intuition.md).
- **For proof structure:** see [Diagrams](./docs/diagrams.md).
- **For exact theorem names:** use [Theorem map](./docs/theorem-map.md).
- **For the conditional sub-Gamma extractor:** see
  [Conditional Sub-Gamma Extractor](./docs/subgamma-extractor.md).
- **For the non-finite unit-interval Dudley example:** see
  [Unit-Interval Dudley Example](./docs/unit-interval-dudley.md).
- **For reusable dyadic Dudley API packaging:** see
  [FormalSLT v0.1 quickstart](./docs/formalslt-v0.1-quickstart.md).
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
- **For current library state (modules, lines, open PRs, roadmap):** see
  [STATUS.md](./STATUS.md).

## Adjacent repositories

| Repository | What it covers |
|---|---|
| [Robby955/formal-martingales](https://github.com/Robby955/formal-martingales) | Lean 4 library for martingale inequalities, anytime-valid inference, and concentration (Ville's inequality, sub-Gaussian / sub-Exp MGF scaffolding). Adjacent to FormalSLT's PAC-Bayes work. Apache 2.0. |

## Key terms

Brief definitions for readers from outside statistical learning theory:

- **PAC-Bayes** (Probably Approximately Correct Bayes): a framework for bounding the risk of a randomized classifier (a posterior over hypotheses) in terms of a KL divergence to a prior. The bounds hold with high probability over the training sample.
- **Rademacher complexity**: a measure of how well a hypothesis class can fit random ±1 labels on a training set. Larger complexity → harder to generalize.
- **McDiarmid's inequality**: a concentration result. If changing one coordinate of a random input shifts a function's output by at most `c`, then the function concentrates around its mean with tail probability `exp(-2ε²/∑cᵢ²)`. FormalSLT proves the sharp constant (the `2` in the exponent).
- **VC dimension**: the size of the largest finite set that a hypothesis class can "shatter" (correctly label in all 2^n ways). Controls sample complexity for binary classifiers.
- **sub-Gaussian / sub-Exponential**: distributions whose tails decay at least as fast as a Gaussian or Exponential. FormalSLT's chaining layer uses MGF (moment-generating function) bounds to handle such distributions.
- **Dudley chaining**: a technique for bounding the supremum of a stochastic process by summing covering-number integrals at successive scales. FormalSLT instantiates this for a non-finite metric space using explicit finite dyadic nets.
- **Algorithmic stability**: a property of a learning algorithm that says similar training sets produce similar outputs. Bounded stability implies generalization.

## Library Map

FormalSLT records finite-sample statistical learning bounds as Lean theorems
with explicit hypotheses and constants. Beyond the v0.1 headline chains, the
library contains checked finite routes for:

- finite-class ERM, Rademacher symmetrization, Massart, Sauer-Shelah, and
  VC-style sample-complexity wrappers;
- high-probability Rademacher and VC sample-complexity bounds carrying the
  sharp McDiarmid `2B²` exponent;
- the sharp bounded-differences/McDiarmid concentration module
  (`Concentration.SharpMcDiarmid`): one-sided, lower-tail, and two-sided
  homogeneous product-measure tails, plus the additive independent special case;
- finite contraction and linear-predictor Rademacher bounds;
- finite Bennett/Bernstein and localized-Rademacher scaffolding;
- conditional sub-Gamma MGF extraction for bounded, conditionally centered
  increments with an explicit conditional second-moment proxy;
- finite covering, finite sub-Gaussian chaining, and finite Dudley
  entropy-budget wrappers;
- finite algorithmic stability expected-gap and high-probability wrappers;
- finite PAC-Bayes KL/DV/MGF, bounded-loss confidence bounds, and finite-grid
  peeling wrappers;
- finite PAC-Bayes Bernstein margin-proxy bounds with a supplied
  per-hypothesis variance proxy.

## Scope and assumptions

The main generalization theorems are intentionally finite and explicit.

| Scope item | Current state |
|---|---|
| Hypothesis classes | Finite index types unless a theorem states a separate finite net/family |
| Samples | Finite iid samples through product measures |
| Losses/processes | Scalar real-valued, with boundedness or finite sub-Gaussian MGF assumptions |
| Conditional MGF layer | Bounded, conditionally centered real increments with an explicit conditional second-moment proxy |
| Constants | High-probability Rademacher and VC sample-complexity bounds use the sharp McDiarmid `2B²` exponent; the localized-Rademacher wrapper still cites the Azuma `8B²` constant |
| PAC-Bayes Bernstein layer | Finite posterior/prior setting with supplied variance proxy and normalized prior-moment certificate |
| Chaining | Finite nets/images, finite support/outcome spaces, finite entropy sums; the unit-interval example instantiates the bridge on a non-finite metric index space with explicit finite meshes |
| Public axiom target | `[propext, Classical.choice, Quot.sound]` only |

## Open work

Short version:

- The main Rademacher and VC results are finite-class and finite-sample
  theorems.
- The sharp McDiarmid constant `exp(-2t²/∑cᵢ²)` is proved for the additive
  independent case (`mcdiarmid_additive_independent`), for Doob martingale
  increments with conditional sub-Gaussian MGF control
  (`sharp_mcdiarmid_of_doob_increments`), and for a general bounded-differences
  function over a homogeneous product measure, one-sided
  (`mcdiarmid_of_hasBoundedDifferences_sharp`) and two-sided
  (`mcdiarmid_twoSided_of_hasBoundedDifferences_sharp`). The high-probability
  Rademacher and VC sample-complexity wrappers now use this sharp `2B²`
  exponent; the localized-Rademacher wrapper still uses the older Azuma `8B²`
  constant. The bounded-differences theorem is stated for the same product law
  in each coordinate, not for arbitrary non-iid product spaces.
- The chaining layer proves finite entropy-budget infrastructure and an initial
  total-bounded finite-net extraction bridge, not the continuous Dudley
  integral.
- PAC-Bayes includes a finite `[0,1]` bounded-loss Catoni-style confidence
  bound, a closed high-confidence good-event theorem, a fixed-budget
  McAllester-style square-root corollary, a finite-grid peeling wrapper for
  posterior-dependent penalties, and a finite Bernstein margin-proxy shell with
  a supplied per-hypothesis variance proxy. Exact all-real-`λ`, concrete
  classifier-margin extractors, infinite-hypothesis, and continuous-posterior
  variants are not yet implemented.
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

Run these before treating a branch as a release candidate:

```bash
lake exe cache get
lake build FormalSLT
lake env lean examples/CheckV01Usability.lean
lake env lean examples/CheckSubGammaExtractor.lean
lake env lean examples/CheckUnitIntervalDudley.lean
lake env lean examples/CheckTwoPointDudley.lean
lake env lean examples/CheckFiniteDiscreteDudley.lean
lake env lean examples/CheckPACBayesBernstein.lean
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
| Stability and PAC-Bayes foundations | `AlgorithmicStability`, `Stability.BousquetElisseeff`, `PACBayesKL`, `PACBayesMcAllester`, `PACBayesFiniteProductMGF`, `PACBayesBoundedLoss`, `PACBayesBernstein` |

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
- [x] PAC-Bayes finite Bernstein margin-proxy wrapper with supplied variance
  proxy and normalized prior-moment certificate
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
- [ ] PAC-Bayes concrete margin-loss Bernstein extractor, all-real-`λ`, or
  continuous-posterior extensions
- [x] Sharp McDiarmid constant for the additive independent case and for Doob
  martingale increments with conditional sub-Gaussian MGF control
- [x] Sharp McDiarmid for a general bounded-differences function over a
  homogeneous product measure: one-sided, lower-tail, and two-sided
  (`mcdiarmid_twoSided_of_hasBoundedDifferences_sharp`), with the sharp `2B²`
  exponent propagated into the high-probability Rademacher and VC wrappers
- [ ] Sharp McDiarmid over arbitrary non-iid product spaces (different law per
  coordinate)
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
