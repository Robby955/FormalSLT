# FormalSLT

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Docs](https://github.com/Robby955/FormalSLT/actions/workflows/docs.yml/badge.svg?branch=main)](https://robby955.github.io/FormalSLT/)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-81a5d25-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

[![theorems and lemmas](https://img.shields.io/badge/theorems%2Flemmas-1%2C791-brightgreen.svg)](#checked-surfaces)
[![FormalSLT modules](https://img.shields.io/badge/FormalSLT%20modules-172-blue.svg)](#module-map)
[![Lean lines](https://img.shields.io/badge/Lean%20lines-74%2C218-brightgreen.svg)](#audit-commands)
[![Zero sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#audit-commands)
[![Axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-brightgreen.svg)](#audit-commands)

> **Finite-sample statistical learning theory, checked in Lean 4.**
> FormalSLT records theorem statements, constants, and scope boundaries in the
> type signatures, where downstream users can inspect them.

**[Browse the searchable API documentation](https://robby955.github.io/FormalSLT/)**
without installing Lean.

FormalSLT is a Lean 4 library for finite-sample learning theory. It connects
concentration, Rademacher and VC theory, metric entropy, stability, sequential
inference, and PAC-Bayes analysis through reusable machine-checked theorems.

[FormalSLT v0.1.0](https://github.com/Robby955/FormalSLT/tree/v0.1.0) was
publicly released on May 8, 2026. A verifier-gated formalization route built on
the library was accepted at the ICML 2026 AI for Math workshop; see
[*From Agents to Axioms: Verifier-Gated Lean Formalization for Statistical
Learning Theory*](https://openreview.net/pdf?id=EsEqPLc0ef).

## Current results

- **Finite-sample learning bounds:** finite-class concentration, Rademacher
  symmetrization, VC bounds, bounded differences, algorithmic stability, and
  PAC-Bayes routes with explicit constants.
- **Metric-entropy generalization:** mean and high-probability bounds obtained
  by combining Rademacher symmetrization with uniform finite Dudley budgets.
  A checked two-point witness makes both the entropy budget and tail factor
  nontrivial.
- **Sharp McDiarmid concentration:** one-sided, lower-tail, and two-sided
  bounds with exponent `-2ε² / ∑ k, (c k)²` for coordinate sensitivities
  `c k`, including independent coordinates with heterogeneous marginal laws.
  For a common per-coordinate sensitivity bound `B`, the denominator is
  `nB²`. The sharper constant reaches the
  high-probability finite-class, Rademacher, VC, and algorithmic-stability
  wrappers.
- **Time-uniform PAC-Bayes:** finite-class i.i.d. bounds simultaneous over all
  posteriors, finite-grid data-dependent tilt selection, a process-level
  theorem over arbitrary measurable hypothesis spaces, and an end-to-end i.i.d.
  bounded-loss theorem over finite-dimensional spherical-Gaussian hypotheses
  with a checked closed-form KL penalty and a stochastic fair-Bernoulli
  product-stream certificate.
- **Test-time PAC-Bayes certificate:** a finite-horizon, five-component
  population-risk bound assembled from a conditional sub-Gamma increment
  model, with a worked instance proving all five contributions strictly
  positive.
- **Probability and statistics foundations:** scoped interfaces for measure
  convergence, laws of large numbers, moments, finite estimation, Fisher
  information, Cramer-Rao, finite exponential families, and asymptotic
  statistics.

The Dudley development is finite by design. The general continuous PAC-Bayes
theorem remains process-level; the i.i.d. specialization currently covers
finite-dimensional spherical Gaussian priors and posteriors. The statistics
interfaces preserve the hypotheses of the Mathlib results they expose. See
[Scope and open boundaries](#scope-and-open-boundaries) for the exact limits.

**Zero `sorry`. Zero `admit`. Zero custom axioms.** The public checker files
print only `[propext, Classical.choice, Quot.sound]`.

Badge counts are generated from the source tree by
[`scripts/generate_badge_counts.py`](./scripts/generate_badge_counts.py) and
checked in CI.

![FormalSLT theorem chain](./docs/theorem-chain.svg)

## Checked surfaces

Each item below names a public endpoint and a small checker that resolves the
declaration and prints its axiom profile.

### Learning bounds and sequential inference

- **Finite-class Hoeffding confidence sequence** —
  `FiniteClassConfidenceSequence.failure_probability_le`;
  [`CheckUniformConvergence.lean`](./examples/CheckUniformConvergence.lean)
- **Five-component PAC-Bayes population-risk certificate** —
  `flagshipFiveComponent_certificate_from_incrementModel` and
  `pacBayesTestTimeFlagship_theorem`, with non-vacuity witness
  `flagshipFiveComponent_five_slots_positive`;
  [`CheckFlagshipFiveComponentAssembly.lean`](./examples/CheckFlagshipFiveComponentAssembly.lean)
- **Fixed-`λ` countable-time sub-Gamma confidence boundary** —
  `atTop_time_uniform_confidence_sequence_subGamma`;
  [`CheckAnytimeAtTopCS.lean`](./examples/CheckAnytimeAtTopCS.lean)
- **Finite fixed-`λ` Catoni change-of-measure posterior-risk bound** —
  `catoni_changeOfMeasure_bound`;
  [`CheckPACBayesChangeOfMeasure.lean`](./examples/CheckPACBayesChangeOfMeasure.lean)

### Concentration and metric entropy

- **Sharp two-sided McDiarmid inequality** —
  `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp`;
  [`CheckSharpMcDiarmid.lean`](./examples/CheckSharpMcDiarmid.lean)
- **Sharp heterogeneous-product McDiarmid inequality** —
  `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp_hetero`;
  [`CheckHeterogeneousMcDiarmid.lean`](./examples/CheckHeterogeneousMcDiarmid.lean)
- **PAC-Bayes Bernstein supplied margin-proxy shell** —
  `finitePACBayesBernsteinMargin_badEventMass_le_delta`;
  [`CheckPACBayesBernstein.lean`](./examples/CheckPACBayesBernstein.lean)
- **Exact finite indicator-loss variance** —
  `indicatorDeviation_secondMoment_eq`, for arbitrary Boolean predicates under
  an arbitrary finite PMF;
  [`CheckIndicatorVariance.lean`](./examples/CheckIndicatorVariance.lean)
- **Hypothesis-specific finite-product indicator Bernstein MGF** —
  `indicator_product_normalizedMGF_le_one`, with exact `R(1-R)` variance and
  explicit fixed-tilt range `0 < lambda < 3n`;
  [`CheckFiniteProductBernstein.lean`](./examples/CheckFiniteProductBernstein.lean)
- **Prior-averaged finite indicator Bernstein moment** —
  `indicator_expectedPriorBernsteinExpMoment_le_one`, matching the abstract
  PAC-Bayes Bernstein adapter with scale `1/(3n)` and variance proxy
  `R_i(1-R_i)/n`;
  [`CheckIndicatorBernsteinMoment.lean`](./examples/CheckIndicatorBernsteinMoment.lean)
- **Mean and high-probability metric-entropy generalization** —
  `metricEntropy_generalization_mean` and
  `metricEntropy_generalization_highProb`;
  [`CheckMetricEntropyGeneralization.lean`](./examples/CheckMetricEntropyGeneralization.lean),
  [`CheckMetricEntropyHighProbability.lean`](./examples/CheckMetricEntropyHighProbability.lean)

### Dudley and finite chaining

- **Unit-interval finite-net bridge** —
  `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree`;
  [`CheckUnitIntervalDudley.lean`](./examples/CheckUnitIntervalDudley.lean)
- **Packaged finite dyadic API** —
  `FiniteDyadicDudleyInstance.suppliedSup_dudley_bound`;
  [`CheckV01Usability.lean`](./examples/CheckV01Usability.lean)
- **Two-point dyadic bound** — `twoPointRademacherSup_dudley_m_bound`;
  [`CheckTwoPointDudley.lean`](./examples/CheckTwoPointDudley.lean)
- **`Fin n` discrete dyadic bound** —
  `finDiscreteRademacherSup_dudley_m_bound`;
  [`CheckFiniteDiscreteDudley.lean`](./examples/CheckFiniteDiscreteDudley.lean)
- **Finite entropy-integral endpoint** —
  `dudley_entropy_integral_of_antitone_coveringNumber`;
  [`CheckDudleyEntropyIntegral.lean`](./examples/CheckDudleyEntropyIntegral.lean)
- **Two-point Rademacher entropy-integral instance** —
  `twoPointRademacher_centered_dudley_entropy_integral`;
  [`CheckTwoPointDudleyIntegral.lean`](./examples/CheckTwoPointDudleyIntegral.lean)

### Time-uniform PAC-Bayes

- **Gaussian KL identification** — `diagonalGaussianMeasure_klDiv_toReal_eq`
  and `sphericalGaussianMeasure_klDiv_toReal_eq`;
  [`CheckGaussianMeasureKL.lean`](./examples/CheckGaussianMeasureKL.lean)
- **Continuous process-level bound** —
  `timeUniformContinuousPACBayes_bound`;
  [`CheckTimeUniformContinuousPACBayes.lean`](./examples/CheckTimeUniformContinuousPACBayes.lean)
- **Spherical-Gaussian specialization** —
  `timeUniformSphericalGaussianPACBayes_bound`;
  [`CheckTimeUniformGaussianPACBayes.lean`](./examples/CheckTimeUniformGaussianPACBayes.lean)
- **End-to-end i.i.d. continuous Gaussian bound** —
  `timeUniformIIDGaussianPACBayes_bound`, with `N(1,1)` versus `N(0,1)` KL
  evaluated to `1/2`; the fair-Bernoulli product-stream example has a
  nonconstant Gaussian-threshold loss, population risk `1/2`, a time-100
  penalty `54/275`, and a first-100-true cylinder of probability `2⁻¹⁰⁰`
  contained in the failure event. This proves strictly positive failure-event
  mass without claiming that either bound is tight;
  [`CheckIIDContinuousGaussianPACBayes.lean`](./examples/CheckIIDContinuousGaussianPACBayes.lean)
- **Finite Gaussian posterior/tilt catalog** —
  `timeUniformIIDGaussianPACBayes_grid_bound` controls a finite catalog of
  fixed spherical-Gaussian posterior/tilt pairs simultaneously, while
  `timeUniformIIDGaussianPACBayes_selected_bound` permits an arbitrary
  sample-dependent catalog selector. The worked two-entry fair-Bernoulli
  certificate uses `N(0,1)` at tilt `1/2` and `N(1,1)` at tilt `1/4` with
  total failure budget `exp(-1)`;
  [`CheckIIDContinuousGaussianGridPACBayes.lean`](./examples/CheckIIDContinuousGaussianGridPACBayes.lean)
- **Finite-class i.i.d. bound, simultaneous over all posteriors** —
  `timeUniformIIDPACBayes_allPosteriors_bound`;
  [`CheckTimeUniformIIDPACBayes.lean`](./examples/CheckTimeUniformIIDPACBayes.lean)
- **Finite-grid i.i.d. bound** —
  `timeUniformIIDPACBayes_grid_allPosteriors_bound`;
  [`CheckTimeUniformIIDGridPACBayes.lean`](./examples/CheckTimeUniformIIDGridPACBayes.lean)

### Probability and statistics interfaces

- **Claim-facing wrappers** for probability, statistics, and learning theory;
  [`CheckWrapperPort.lean`](./examples/CheckWrapperPort.lean)

## Where to start

- **Find a theorem:** use the searchable [HTML theorem index](./docs/INDEX.html)
  or grep-friendly [Markdown index](./docs/INDEX.md). Each entry links to the
  declaration's source line.
- **Use a theorem:** run the three
  [getting-started tutorials](./examples/tutorials) for a concrete tail bound,
  PAC-Bayes bound, and anytime-valid confidence sequence.
- **Review the v0.1 surface:** read the
  [quickstart](./docs/formalslt-v0.1-quickstart.md) and
  [technical note](./docs/formalslt-v0.1-technical-note.md).
- **Understand the proof structure:** start with
  [Architecture](./ARCHITECTURE.md),
  [How to read the proofs](./docs/how-to-read-the-proofs.md),
  [Intuition](./docs/intuition.md), and [Diagrams](./docs/diagrams.md).
- **Trace mathematical provenance:** use the
  [source-to-theorem-family map](./docs/references.md), then consult
  [TheoremPath's broader curriculum references](https://theorempath.com/references)
  for chapter-level learning context.
- **Audit public claims:** use the generated
  [proof-frontier manifest](./docs/proof-frontier.md) and
  [scope statement](./docs/assumptions-and-nonclaims.md).
- **Contribute:** read [CONTRIBUTING.md](./CONTRIBUTING.md) and the
  [good first issues](./docs/good-first-issues.md).

The companion library
[formal-martingales](https://github.com/Robby955/formal-martingales) develops
martingale inequalities, anytime-valid inference, and concentration.

## Fast verification

From the repository root:

```bash
lake exe cache get
lake build FormalSLT
lake env lean examples/CheckV01Usability.lean
lake env lean examples/CheckTimeUniformIIDPACBayes.lean
lake env lean examples/CheckWrapperPort.lean
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/generate_badge_counts.py --check
```

If `lake` is not on the shell path, use `~/.elan/bin/lake`. The complete
release check is in [Audit commands](#audit-commands).

## For researchers

- Import the finite-class, Rademacher, VC, stability, or PAC-Bayes statements
  directly; constants and hypotheses are visible in their Lean signatures.
- Reuse `twoPointDudleyInstance`, `finDiscreteDudleyInstance`, and
  `FiniteDyadicDudleyInstance` as templates for new metric-index examples.
- Use `FormalSLT.Rademacher.MetricEntropyGeneralization` and
  `FormalSLT.Rademacher.MetricEntropyHighProbability` when an application has
  a uniform finite Dudley budget almost everywhere over samples.
- Use the finite i.i.d. time-uniform PAC-Bayes endpoints for finite hypothesis
  classes with `[0,1]` losses. Use the grid theorem when the tilt is selected
  from a fixed finite family after observing the data.
- Use the continuous process-level PAC-Bayes endpoint only with a supplied
  prior-mixture supermartingale. The spherical-Gaussian specialization replaces
  its abstract KL term with the checked closed form.
- Use `timeUniformIIDGaussianPACBayes_bound` when the hypotheses are
  finite-dimensional real vectors, the prior and posterior are spherical
  Gaussians, and the jointly measurable loss lies in `[0,1]`; its proof derives
  the process obligations from the i.i.d. sample model. The confidence and tilt
  parameters must satisfy `0 < delta` and `0 < lam < 3`.

See [Mathematical sources](./docs/references.md) for textbook and primary-paper
provenance, and [Related work](./docs/related-work.md) for the relationship to
adjacent Lean empirical-process and learning-theory developments.

## Module map

The generated [theorem index](./docs/INDEX.md) lists public declarations;
[`FormalSLT.lean`](./FormalSLT.lean) is the complete import map.

- **Core learning definitions:** `Risk`, `ERM`, `UniformConvergence`,
  `GhostSample`, `GlivenkoCantelli`
- **Probability and convergence:** `Probability.Concentration`,
  `Probability.KolmogorovAxioms`, `Probability.BorelCantelli`,
  `Probability.LawOfLargeNumbers`, `Probability.MeasureConvergence`,
  `Probability.Martingale`, `Probability.Moments`
- **Statistics:** `Statistics.Bernoulli`, `Statistics.SampleStatistics`,
  `Statistics.ClassicalEstimation`, `Statistics.FisherInformation`,
  `Statistics.CramerRao`, `Statistics.ExponentialFamily`,
  `Statistics.AsymptoticStatistics`
- **Concentration and sequential inference:** `Azuma.*`,
  `Concentration.SharpMcDiarmid`, `Concentration.SubGamma.*`,
  `AnytimeValid.*`
- **Rademacher and metric entropy:** `Rademacher.FiniteSample`,
  `Rademacher.Symmetrization`, `Rademacher.Massart`,
  `Rademacher.HighProbability`, `Rademacher.Contraction`,
  `Rademacher.LinearPredictor`, `Rademacher.Localized`,
  `Rademacher.MetricEntropyGeneralization`,
  `Rademacher.MetricEntropyHighProbability`
- **VC theory:** `VC.Dimension`, `VC.PACBridge`, `VC.SauerShelah`,
  `VC.Rademacher`, `VC.SampleComplexity`, `VC.BinaryVCBridge`
- **Covering and chaining:** `Covering.DudleyChaining`,
  `Covering.FiniteSubGaussianChaining`, `Covering.TotalBoundedDudley`,
  `Covering.DudleyEntropyIntegral`, `Covering.UnitIntervalDudley`,
  `Covering.TwoPointDudleyIntegral`
- **Stability:** `AlgorithmicStability`, `Stability.BousquetElisseeff`,
  `Stability.RKHSRegularisedERM`
- **PAC-Bayes:** `PACBayesKL`, `PACBayesMcAllester`,
  `PACBayesBoundedLoss`, `PACBayesBernstein`, `PACBayes.ChangeOfMeasure`,
  `PACBayes.GaussianMeasureKL`, `PACBayes.TimeUniformPACBayes`,
  `PACBayes.TimeUniformContinuousPACBayes`,
  `PACBayes.TimeUniformGaussianPACBayes`, `PACBayes.TimeUniformIID`,
  `PACBayes.TimeUniformIIDGrid`, `PACBayes.IIDContinuousGaussian`,
  `PACBayes.IIDContinuousGaussianGrid`

## Scope and open boundaries

The main learning-theory results are deliberately finite and explicit.

### Assumptions

- **Hypothesis classes:** finite index types unless a theorem states a finite
  net or the process-level continuous PAC-Bayes interface
- **Samples:** finite i.i.d. samples through product measures for the main
  learning spine; the heterogeneous McDiarmid theorem allows a separate
  probability law in each independent coordinate
- **Losses and processes:** real-valued, with boundedness or finite
  sub-Gaussian MGF assumptions
- **Sharp bounded differences:** independent finite product measures, including
  heterogeneous coordinate laws, with a common coordinate state space
- **PAC-Bayes Bernstein:** finite priors and posteriors with a supplied variance
  proxy and normalized prior-moment certificate
- **Time-uniform PAC-Bayes:** finite-class and finite-dimensional
  spherical-Gaussian i.i.d. bounded-loss theorems at discrete sample times;
  process-level for a fully arbitrary measurable hypothesis space
- **Chaining:** finite nets, images, supports, outcome spaces, and entropy sums
- **Public axiom profile:** `[propext, Classical.choice, Quot.sound]`

### Not yet proved

- A general continuous Dudley entropy-integral theorem with arbitrary
  measurable suprema
- A general measurable-supremum or separability construction for non-finite
  classes
- An infinite-class confidence sequence
- A concrete classifier-margin extractor or all-real-`λ` PAC-Bayes Bernstein
  optimization theorem
- An end-to-end i.i.d. bounded-loss PAC-Bayes specialization beyond the current
  finite-dimensional spherical Gaussian family
- A neural-network generalization theorem

For the full statement, see
[Scope and assumptions](./docs/assumptions-and-nonclaims.md).

## Installation

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads [`lean-toolchain`](./lean-toolchain) and fetches the pinned Lean
version.

```bash
git clone https://github.com/Robby955/FormalSLT.git
cd FormalSLT
lake exe cache get
lake build FormalSLT
```

If `lake` is not on the shell path:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build FormalSLT
```

The first command downloads the prebuilt Mathlib cache; later builds are
incremental.

## Audit commands

Run the complete release check from the repository root:

```bash
lake exe cache get
lake build FormalSLT
for f in examples/*.lean; do
  echo "$f"
  lake env lean "$f"
done
make tutorials
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/generate_badge_counts.py --check
python3 scripts/check_doc_anchors.py --self-test
git ls-files -z -- '*.md' '*.mdx' | \
  xargs -0 python3 scripts/check_doc_anchors.py
git diff --check
```

Expected results:

- the root build, example sweep, and tutorials finish successfully;
- public checkers print only standard Lean/Mathlib axioms;
- the proof-debt scans find no executable `sorry`, `admit`, or custom axiom;
- generated proof-frontier, badge, and documentation anchors are current; and
- `git diff --check` reports no whitespace errors.

The badge script counts declarations under `FormalSLT/`, modules under
`FormalSLT/`, and Lean lines under `FormalSLT/` and `examples/`. Running it
without `--check` updates the JSON files under `docs/badges/`.

## Roadmap

Completed work is indexed in [Checked surfaces](#checked-surfaces) and the
[theorem index](./docs/INDEX.md). The remaining public boundaries are:

- [ ] Continuous Dudley entropy integral over total-bounded classes
- [ ] Concrete PAC-Bayes margin extractor and all-real-`λ` optimization
- [ ] Extend end-to-end i.i.d. bounded-loss PAC-Bayes beyond finite-dimensional
  spherical Gaussian priors and posteriors

## Dependencies

- [Lean 4](https://lean-lang.org/) v4.32.0
- [Mathlib4](https://github.com/leanprover-community/mathlib4) @ `81a5d257`

## Contributing

Read [CONTRIBUTING.md](./CONTRIBUTING.md) before opening a pull request. The
short version: one theorem per pull request, no `sorry` or `admit`, only the
standard `[propext, Classical.choice, Quot.sound]` axioms, and assumptions in
the theorem signature. New modules should also follow the subject ownership and
import direction in [ARCHITECTURE.md](./ARCHITECTURE.md).

For candidate contributions, see
[open formalization problems](./docs/open-formalization-problems.md) and
[good first issues](./docs/good-first-issues.md). Maintainers can use the
[public release checklist](./docs/public-release-checklist.md).

## Citation

If you use FormalSLT in academic work, cite the library and, where relevant,
the ICML 2026 AI for Math workshop paper.

```bibtex
@software{formal_slt,
  title  = {FormalSLT: Formal Statistical Learning Theory in Lean 4},
  author = {Sneiderman, Robert},
  year   = {2026},
  url    = {https://github.com/Robby955/FormalSLT},
  note   = {Lean 4 formalization of finite-sample SLT bounds.}
}

@inproceedings{sneiderman2026agents,
  title     = {From Agents to Axioms: Verifier-Gated Lean Formalization for Statistical Learning Theory},
  author    = {Sneiderman, Robert},
  booktitle = {ICML 2026 Workshop on AI for Math (AI4Math)},
  year      = {2026},
  url       = {https://openreview.net/pdf?id=EsEqPLc0ef}
}
```

## License

FormalSLT is released under the [MIT License](./LICENSE).
