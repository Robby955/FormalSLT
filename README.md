# FormalSLT

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Docs](https://github.com/Robby955/FormalSLT/actions/workflows/docs.yml/badge.svg?branch=main)](https://robby955.github.io/FormalSLT/)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-81a5d25-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

[![theorems and lemmas](https://img.shields.io/badge/theorems%2Flemmas-2%2C279-brightgreen.svg)](#checked-surfaces)
[![FormalSLT modules](https://img.shields.io/badge/FormalSLT%20modules-193-blue.svg)](#module-map)
[![Lean lines](https://img.shields.io/badge/Lean%20lines-86%2C372-brightgreen.svg)](#audit-commands)
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
- **Finite Markov prequential risk:** an actual Ionescu--Tulcea path law for a
  finite transition PMF, a derived next-step conditional-risk identity, the
  sharp universal `1/4` conditional-variance proxy for `[0,1]` losses, an
  anytime two-sided fixed-predictor certificate, and a fixed-tilt PAC-Bayes
  certificate for `0 < λ < 3` simultaneous over all positive times and all
  posteriors on a finite predictor catalog.
- **Test-time PAC-Bayes certificate:** a finite-horizon, five-component
  population-risk bound assembled from a conditional sub-Gamma increment
  model, with a worked instance proving all five contributions strictly
  positive.
- **Probability and statistics foundations:** scoped interfaces for measure
  convergence, laws of large numbers, moments, finite estimation, Fisher
  information, Cramer-Rao, finite exponential families, and asymptotic
  statistics.
- **Finite empirical-Bernstein PAC-Bayes:** Bessel-corrected loss variance, its
  exact second-order pair representation and finite-i.i.d. unbiasedness, a
  source-normalized lower-tail MGF proved by random matching and finite Jensen,
  and a fixed-sample, fixed-tilt confidence event simultaneous over every
  finite posterior. A separate bounded-loss Bernstein event and a finite union
  bound now give the observable fixed-parameter risk theorem, with distinct
  variance and risk failure budgets. Separately weighted finite `eta` and
  `lambda` catalogs now permit both tilts to be selected after seeing the
  sample and posterior. The variance catalog is also exposed as its own API,
  with unequal weights, two selector branches, positive-mass samples, and both
  concrete certificates below `1/4`. A fixed-sample joint mean/variance layer
  adds the normalized joint MGF with the retained Bennett factor inside the
  logarithm and a one-event weighted joint-pair posterior catalog with one KL
  term per selected entry. On the checked zero-residual coefficient branch,
  the retained logarithm is absorbed and the selected posterior risk is bounded
  explicitly by empirical risk, empirical variance, and that one KL term. For
  every admissible entry with `t > 0`, nonnegative `kappa`, and failed balance,
  the exact maximum of the retained residual on `[0,1/4]` is checked and
  contributes the explicit penalty `xi / t`. All-real or
  countable tilt optimization and time-uniform empirical-Bernstein risk remain
  open.

The Dudley core is finite by design. The finite-outcome endpoint
`continuous_dudley_entropy_integral` assumes a finite sub-Gaussian process on a
nonempty pseudometric index, a totally bounded universal index set, positive
`radiusScale` and process variance proxy, agreement of the process and ambient
distances, an antitone nonnegative interval-integrable entropy profile, and
supplied separable-terminal boundary certificates. The measure-side endpoint is
instead an expectation-operator lift from a supplied `MeasureChainingBudget`;
it does not construct those metric or chaining hypotheses. Arbitrary measurable
suprema remain out of scope. The general continuous PAC-Bayes
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
- **Finite Markov trajectory prequential-risk certificate** —
  `markovPrequentialRiskExceptionalEvent_mass_le_delta` and
  `averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem`,
  with a persistent two-state receipt at `n = 1024` whose failure probability
  is at most `1/20`, whose boundary radius (half-width) is below `1/20`, and
  whose good-path empirical risk lies in the displayed open interval
  `(11/80, 19/80)`, which has endpoint width exactly `1/10`;
  [`CheckMarkovRisk.lean`](./examples/CheckMarkovRisk.lean)
- **Finite-catalog Markov PAC-Bayes certificate** —
  `markovPACBayes_prequentialRisk_certificate` gives one measurable event of
  probability at most `delta` on whose complement the prequential-risk bound
  holds at every positive time for every posterior PMF, for one fixed declared
  tilt satisfying `0 < λ < 3`. The asymmetric two-state receipt selects a point
  posterior from the first `1024` transitions, has exact KL cost `log 2`,
  empirical risk at most `1/2`, and posterior-average conditional risk below
  `11/20` at confidence `19/20`;
  [`CheckMarkovPACBayes.lean`](./examples/CheckMarkovPACBayes.lean)

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
- **Finite indicator PAC-Bayes Bernstein confidence theorem** —
  `indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta`, bounding
  the i.i.d. product mass where any finite posterior violates the explicit
  fixed-tilt bound, with
  `indicator_posteriorGeneralizationGap_le_of_not_mem` as the pointwise
  all-posteriors companion. The concrete classifier receipt proves an all-true
  sample belongs to the bad set and sandwiches its mass between `2^-20` and
  `1/2`;
  [`CheckIndicatorBernsteinConfidence.lean`](./examples/CheckIndicatorBernsteinConfidence.lean),
  [`CheckIIDIndicatorPACBayesBernstein.lean`](./examples/CheckIIDIndicatorPACBayesBernstein.lean)
- **Observable low-risk indicator PAC-Bayes--Bernstein corollary** —
  `indicator_posteriorRisk_le_twoThirds_of_not_mem`, at the fixed sample-level
  tilt `lambda = 2n/3`, gives
  `R(rho) <= (7/4) Rhat(rho) + (21/(8n))(KL(rho||pi) + log(1/delta))`;
  `indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem` truncates this at
  one. The concrete balanced sample of size `40` discharges the good-event
  premise and yields the checked certificate `R(rho) <= 301/320 < 1`;
  [`CheckIndicatorBernsteinLowRisk.lean`](./examples/CheckIndicatorBernsteinLowRisk.lean)
- **Finite weighted indicator-Bernstein tilt catalog** —
  `indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta`
  allocates confidence budget `delta * w_j` across a fixed finite tilt family,
  while
  `indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem`
  permits the selected entry to depend on both the observed sample and
  posterior. The four-entry unequal-weight receipt proves catalog mass at most
  `1/2` and an empirical-risk-selected certificate `R(rho) <= 13/14 < 1`.
  This remains finite, fixed-sample, and population-variance self-bounding; it
  is not empirical sample variance or all-real tilt optimization;
  [`CheckIndicatorBernsteinTiltCatalog.lean`](./examples/CheckIndicatorBernsteinTiltCatalog.lean)
- **Finite empirical loss variance and fixed-parameter PAC-Bayes risk** —
  `finiteEmpiricalVariance_eq_pairwise` identifies the Bessel-corrected
  variance with its ordered off-diagonal second-order statistic, while
  `finiteEmpiricalVariance_unbiased_finiteProduct` proves that its expectation
  under the finite IID product law is the per-hypothesis population variance.
  `finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` proves the
  source-normalized exponential moment for every `n >= 2`, and
  `finiteEmpiricalVariancePACBayes_badEventMass_le_delta` gives one fixed-tilt
  bad set of mass at most `delta`. Outside it,
  `posteriorPopulationVariance_le_empiricalVariance_of_not_mem` holds for every
  finite posterior, including one selected after observing the sample.
  `finiteBoundedLossBernstein_badEventMass_le_delta` supplies the separate
  population-risk event, and
  `posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem` combines
  them with total failure at most `deltaVariance + deltaRisk`. The
  three-level loss receipt separately evaluates population variance `1/6`, one
  displayed empirical variance `1/4`, and the full `3^3`-sample expectation
  `1/6`. An asymmetric two-hypothesis receipt proves that the posterior selector
  takes both values on positive-mass samples and gives both branches a checked
  certificate at most `202/825 < 1/4`. A fair nonconstant-loss receipt uses
  separate `1/4` budgets, proves combined bad mass at most `1/2`, and derives a
  good-sample final-risk witness. The theorem has two declared tilts and one
  fixed sample size; it is not tilt-grid, all-real optimized, or time-uniform;
  [`CheckFiniteEmpiricalVariance.lean`](./examples/CheckFiniteEmpiricalVariance.lean),
  [`CheckFiniteEmpiricalVariancePACBayes.lean`](./examples/CheckFiniteEmpiricalVariancePACBayes.lean),
  [`CheckFiniteEmpiricalVarianceTiltCatalog.lean`](./examples/CheckFiniteEmpiricalVarianceTiltCatalog.lean),
  [`CheckFiniteEmpiricalBernsteinRisk.lean`](./examples/CheckFiniteEmpiricalBernsteinRisk.lean),
  [`CheckFiniteEmpiricalBernsteinRiskCatalog.lean`](./examples/CheckFiniteEmpiricalBernsteinRiskCatalog.lean),
  [`FiniteEmpiricalVarianceMGF.lean`](./FormalSLT/PACBayes/FiniteEmpiricalVarianceMGF.lean),
  [`FiniteEmpiricalVariancePACBayes.lean`](./FormalSLT/PACBayes/FiniteEmpiricalVariancePACBayes.lean),
  [`FiniteBoundedLossBernstein.lean`](./FormalSLT/PACBayes/FiniteBoundedLossBernstein.lean),
  [`FiniteEmpiricalBernsteinRisk.lean`](./FormalSLT/PACBayes/FiniteEmpiricalBernsteinRisk.lean)
- **Finite exponential tilting and variance transport** —
  `finiteExponentialTilt_changeOfMeasure` and
  `finiteProductExponentialTilt_changeOfMeasure` give exact coordinate and
  product identities. The bounded-loss specialization proves the retained
  Bennett normalizer and `exp (-t) * V_p <= V_{q_t}` without full support;
  [`CheckFiniteExponentialTilt.lean`](./examples/CheckFiniteExponentialTilt.lean),
  [`CheckFiniteExponentialTiltProduct.lean`](./examples/CheckFiniteExponentialTiltProduct.lean),
  [`CheckFiniteBoundedLossExponentialTilt.lean`](./examples/CheckFiniteBoundedLossExponentialTilt.lean)
- **Fixed-sample joint mean/Bessel-variance MGF core** —
  `finiteJointMeanVarianceMGF_le` combines the lower-tail mean score and
  Bessel empirical-variance score by an exact finite exponential tilt, while
  `finiteJointMeanVariance_normalizedMGF_le_one` moves the Bennett and
  transported-variance corrections inside one normalized exponential. The
  fair-Boolean receipt uses the nonconstant loss `0, 1`, `n = 2`, and positive
  tilts `t = eta = 1/2`, for which the joint variance coefficient is `1/2`.
  This core theorem is a per-hypothesis fixed-sample moment; the next checked
  layer lifts it to a prior mixture and posterior-uniform finite catalog, but
  neither layer is a time-uniform process;
  [`CheckFiniteJointMeanVarianceMGF.lean`](./examples/CheckFiniteJointMeanVarianceMGF.lean),
  [`FiniteJointMeanVarianceMGF.lean`](./FormalSLT/PACBayes/FiniteJointMeanVarianceMGF.lean)
- **One-event joint mean/variance posterior catalog** —
  `finiteJointMeanVariance_catalogBadSamples_mass_le_delta` thresholds one
  prior-and-catalog master mixture at `1 / delta` to get a single bad-sample
  set of mass at most `delta`, and
  `finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem` gives every
  posterior a retained-variance inequality with one KL term at a catalog
  entry selected after seeing the sample and the posterior. Under the explicit
  coefficient balance, the zero-residual selector endpoint removes the unknown
  population variance and leaves empirical risk plus empirical variance and
  one KL/confidence term. The Bennett log in the parent theorem is stated at
  the posterior-averaged variance via concavity. Fixed-sample, finite, and
  declared in advance: the score is not an e-process, and
  time-uniform empirical-Bernstein PAC-Bayes results exist in prior work
  (Jang et al., COLT 2023; Chugg, Wang, and Ramdas, JMLR 2023). The receipt
  drives two unequal-weight entries with a selector attaining both and,
  separately, checks a balanced `n = 6` good sample whose zero-residual
  ceiling is `7/10 + log 2 / 3 < 1`;
  [`CheckFiniteJointMeanVariancePACBayes.lean`](./examples/CheckFiniteJointMeanVariancePACBayes.lean),
  [`FiniteJointMeanVariancePACBayes.lean`](./FormalSLT/PACBayes/FiniteJointMeanVariancePACBayes.lean)
- **Exact joint residual envelope** —
  `finiteJointMeanVarianceXi_isGreatest` proves the exact three-branch maximum
  of the retained population-variance residual on `[0, 1/4]`, including its
  zero, endpoint, and interior maximizers.
  `finiteJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem`
  adds the resulting `xi / t` penalty to the same one-event, one-KL selected
  posterior-risk bound. The receipt uses `n = 6`, `t = 1`, and `eta = 1/2`
  to activate a genuinely positive endpoint residual. This remains
  fixed-sample and finite-catalog;
  [`CheckFiniteJointMeanVarianceResidual.lean`](./examples/CheckFiniteJointMeanVarianceResidual.lean),
  [`FiniteJointMeanVarianceResidual.lean`](./FormalSLT/PACBayes/FiniteJointMeanVarianceResidual.lean)
- **Mean and high-probability metric-entropy generalization** —
  `metricEntropy_generalization_mean` and
  `metricEntropy_generalization_highProb`;
  [`CheckMetricEntropyGeneralization.lean`](./examples/CheckMetricEntropyGeneralization.lean),
  [`CheckMetricEntropyHighProbability.lean`](./examples/CheckMetricEntropyHighProbability.lean)

### Dudley and finite chaining

- **Continuous Dudley entropy integral under a supplied boundary certificate** —
  `continuous_dudley_entropy_integral` bounds the expected supremum of a
  finite sub-Gaussian process over a nonempty pseudometric index whose universal
  set is totally bounded. It assumes positive `radiusScale` and
  `P.varianceProxy`, with `P.dist` equal to the ambient distance, and bounds by
  `coarseBudget` plus the product of `4 * sqrt (2 * varianceProxy)` with the
  full interval integral of the entropy profile on `(0, radiusScale / 2)`;
  the coarse budget is added, not multiplied. The finite
  outcome support `[Fintype Ω]`, the antitone nonnegative integrable entropy
  profile, and the separable-terminal boundary certificate at every positive
  tolerance are caller-supplied hypotheses stated in the signature; arbitrary
  measurable suprema remain out of scope;
  [`CheckContinuousDudley.lean`](./examples/CheckContinuousDudley.lean)
- **Measure-side continuous Dudley variant** —
  `continuous_dudley_entropy_integral_of_measure` is an expectation-operator
  lift on a measurable space with a probability measure. It assumes a positive
  `radiusScale`, nonnegative `varianceProxy` and entropy profile, interval
  integrability on `[0, radiusScale / 2]`, and a supplied
  `MeasureChainingBudget`; it does not inherit the finite-process or
  topological hypotheses above;
  [`CheckMeasureDudley.lean`](./examples/CheckMeasureDudley.lean)
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
- Use `FormalSLT.PACBayes.IndicatorBernsteinLowRisk` for a posterior-uniform
  finite indicator-loss bound with an observable empirical-risk right-hand
  side. It self-bounds population Bernoulli variance by risk; it is not an
  empirical sample-variance theorem.
- Use `FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog` when a fixed finite
  family of indicator-Bernstein tilts should be selected after observing the
  sample. Positive weights with finite total mass `∑ j, w_j ≤ 1` allocate the
  confidence budget, and the selected entry may also depend on the posterior;
  the catalog itself must be fixed in advance.
- Use `FormalSLT.PACBayes.FiniteEmpiricalVariance` for the Bessel-corrected
  per-hypothesis loss variance, its exact pairwise form, bounded-loss
  estimates, and finite-product unbiasedness.
- Use `FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching` and
  `FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF` for the random-matching,
  disjoint-pair factorization, finite-Jensen proof of the fixed-hypothesis
  source MGF. Use `FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes` when one
  declared positive tilt should give a fixed-sample event simultaneous over
  every finite posterior. This endpoint averages each hypothesis's variance;
  it does not take the variance of a posterior-averaged loss.
- Use `FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog` and
  `FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog` when variance and
  risk tilts are selected from finite, predeclared weighted catalogs after the
  sample and posterior are observed.
- Use `FormalSLT.PACBayes.FiniteExponentialTilt` and
  `FormalSLT.PACBayes.FiniteExponentialTiltProduct` for exact finite
  change-of-measure identities. Use
  `FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt` for the lower-tail
  bounded-loss normalizer and variance-transport comparison.
- Use `FormalSLT.PACBayes.FiniteJointMeanVarianceMGF` for the fixed-sample,
  per-hypothesis exponential moment coupling the lower-tail mean score to the
  Bessel empirical variance. The normalized endpoint has expectation at most
  one but does not itself quantify over priors, posteriors, or tilt catalogs.
- Use `FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes` for the one-event
  finite joint-pair catalog with one KL term at the selected entry. Its
  zero-residual selector theorem gives an explicit empirical-Bernstein risk
  bound when every selectable entry satisfies the stated coefficient balance.
- Use `FormalSLT.PACBayes.FiniteJointMeanVarianceResidual` for admissible
  positive-`t`, nonnegative-`kappa` entries outside that balance branch. It
  proves the exact piecewise residual maximum on `[0,1/4]` and adds the explicit
  `xi / t` penalty without changing the shared event or finite-catalog selector
  semantics.
- Use `FormalSLT.PACBayes.FiniteBoundedLossBernstein` for the separate
  fixed-`lambda` population-risk Bernstein event. Use
  `FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk` to combine it with the
  empirical-variance event. The two confidence budgets are added; no
  independence or single-event reuse is claimed.
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
  `PACBayes.IndicatorBernsteinLowRisk`,
  `PACBayes.IndicatorBernsteinTiltCatalog`,
  `PACBayes.FiniteEmpiricalVariance`,
  `PACBayes.FiniteEmpiricalVarianceMatching`,
  `PACBayes.FiniteEmpiricalVarianceMGF`,
  `PACBayes.FiniteEmpiricalVariancePACBayes`,
  `PACBayes.FiniteEmpiricalVarianceTiltCatalog`,
  `PACBayes.FiniteExponentialTilt`,
  `PACBayes.FiniteExponentialTiltProduct`,
  `PACBayes.FiniteBoundedLossExponentialTilt`,
  `PACBayes.FiniteBoundedLossBernstein`,
  `PACBayes.FiniteEmpiricalBernsteinRisk`,
  `PACBayes.FiniteEmpiricalBernsteinRiskCatalog`,
  `PACBayes.FiniteJointMeanVarianceMGF`,
  `PACBayes.FiniteJointMeanVariancePACBayes`,
  `PACBayes.FiniteJointMeanVarianceResidual`,
  `PACBayes.GaussianMeasureKL`, `PACBayes.TimeUniformPACBayes`,
  `PACBayes.TimeUniformScorePACBayes`,
  `PACBayes.TimeUniformContinuousPACBayes`,
  `PACBayes.TimeUniformGaussianPACBayes`, `PACBayes.TimeUniformIID`,
  `PACBayes.TimeUniformIIDGrid`, `PACBayes.IIDContinuousGaussian`,
  `PACBayes.IIDContinuousGaussianGrid`
- **Stochastic dynamics:** `StochasticDynamics.MarkovRisk` and
  `StochasticDynamics.MarkovPACBayes`, re-exported by the stable topic import
  `FormalSLT.StochasticDynamics`

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
  proxy and normalized prior-moment certificate; the indicator specialization
  also has a fixed finite weighted tilt catalog with simultaneous validity.
  The empirical-variance specialization assumes a finite IID product law,
  sample size at least two, `[0,1]` losses, one fixed positive tilt, and
  `0 < delta`. Its one bad set is simultaneous over all posteriors on a finite
  hypothesis type and bounds the posterior average of per-hypothesis variances.
  A finite weighted empirical-variance tilt catalog makes a family of such
  tilts simultaneously valid under one event and supports sample- and
  posterior-dependent selection. The joint master-mixture mass theorem uses
  nonnegative catalog weights with total at most one and `0 < delta`; its
  entrywise posterior bounds require every catalog weight to be strictly
  positive and the prior to have full support.
- **Time-uniform PAC-Bayes:** finite-class and finite-dimensional
  spherical-Gaussian i.i.d. bounded-loss theorems at discrete sample times;
  process-level for a fully arbitrary measurable hypothesis space
- **Finite Markov prequential risk:** finite state space, transition PMFs,
  deterministic initial state, and a fixed `[0,1]` observable and finite
  catalog of fixed `[0,1]`-valued predictors with a full-support prior; the
  PAC-Bayes endpoint is simultaneous over every positive time and posterior at
  one fixed declared tilt satisfying `0 < λ < 3`, and targets
  posterior-average one-step conditional squared risk along the realized path
- **Chaining:** finite nets, images, supports, outcome spaces, and entropy sums
- **Public axiom profile:** `[propext, Classical.choice, Quot.sound]`

### Not yet proved

- A general continuous Dudley entropy-integral theorem with arbitrary
  measurable suprema
- A general measurable-supremum or separability construction for non-finite
  classes
- An infinite-class confidence sequence
- All-real or countable tilt optimization and a time-uniform
  empirical-Bernstein risk theorem. The fixed rational two-event theorem,
  separately weighted finite `eta`/`lambda` catalogs, one-event finite
  joint-pair catalog, zero-residual specialization, and all three branches of
  the exact finite-catalog `xi` residual are checked.
- An end-to-end i.i.d. bounded-loss PAC-Bayes specialization beyond the current
  finite-dimensional spherical Gaussian family
- Same-trajectory-trained or online-updated predictors, random initial laws,
  continuous-state dynamics, and stationary or mixing-based long-run risk
  guarantees
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

The badge script counts theorem and lemma declarations under `FormalSLT/` and
`examples/`, modules under `FormalSLT/`, and Lean lines under both trees.
Running it without `--check` updates the JSON files under `docs/badges/`.

## Roadmap

Completed work is indexed in [Checked surfaces](#checked-surfaces) and the
[theorem index](./docs/INDEX.md). The remaining public boundaries are:

- [ ] Extend the checked Dudley boundary-certificate theorem to arbitrary
  measurable suprema and non-finite outcome constructions
- [ ] Extend the checked exact piecewise `xi` residual from finite catalogs to
  countable weighted tilt mixtures
- [ ] Countable weighted `λ` catalogs beyond the checked finite selector layer
- [ ] Extend fixed-sample joint scores to a normalized hypothesis--tilt
  e-process mixture, then study conditional e-variable composition and
  composite nulls
- [ ] Extend end-to-end i.i.d. bounded-loss PAC-Bayes beyond finite-dimensional
  spherical Gaussian priors and posteriors
- [ ] Extend the finite Markov PAC-Bayes certificate to random initial laws,
  predictable or independently trained predictor catalogs, and declared
  selectable tilt families

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
