# FormalSLT

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Docs](https://github.com/Robby955/FormalSLT/actions/workflows/docs.yml/badge.svg?branch=main)](https://robby955.github.io/FormalSLT/)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-905b958-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

[![theorems and lemmas](https://img.shields.io/badge/theorems%2Flemmas-3%2C989-brightgreen.svg)](#checked-surfaces)
[![FormalSLT modules](https://img.shields.io/badge/FormalSLT%20modules-258-blue.svg)](#module-map)
[![Lean lines](https://img.shields.io/badge/Lean%20lines-134%2C586-brightgreen.svg)](#audit-commands)
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

## Flagship results

These are the results to start with. For each one, the README first says what
it proves in statistical terms, then links the exact Lean theorem and a concrete
checker. The underlying statistical ideas come from the literature; FormalSLT's
contribution is the machine-checked specialization or derived endpoint.

### All-sample-size empirical-Bernstein PAC-Bayes

For finite-valued IID observations, an arbitrary measurable hypothesis space,
strongly measurable $[0,1]$ loss sections, and a probability prior fixed before
seeing the data, one posterior-independent event has probability at most
$\delta$. Outside that event, the following bound holds simultaneously for
**every** sample size $n \ge 2$ and **every** posterior probability measure
$\rho$ that is absolutely continuous with respect to the prior and has an
integrable log-likelihood ratio:

$$
R(\rho) < \widehat R_n(\rho)
       + \frac{5}{2} \sqrt{\frac{\widehat V_n(\rho) L_n(\rho)}{n}}
       + \frac{5 L_n(\rho)}{n}
$$

Here $R$ is population risk, $\widehat R_n$ is empirical risk, and $\rho$ is the
posterior. $\widehat V_n(\rho)$ is the posterior integral of the
per-hypothesis Bessel sample variance, and
$L_n(\rho) = \mathrm{KL}(\rho \| \mathrm{prior}) + \log(r(r+1)^2 / \delta)$ with
$r = \lfloor \log_2 n \rfloor$ (written `Nat.log 2 n` in Lean). The result uses
one measure-theoretic KL term. Because the event is uniform over all admissible
posteriors, a posterior may be substituted pointwise after observing the data.

- **Lean theorem:**
  `exists_continuousInfiniteEmpiricalBernstein_event` in
  [`ContinuousInfiniteEmpiricalBernsteinStitch.lean`](./FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean)
- **Axiom checker:**
  [`CheckContinuousInfiniteEmpiricalBernsteinStitch.lean`](./examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean)
  checks the public endpoint and its load-bearing event and risk theorems.
- **Concrete continuous receipt:**
  [`CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean`](./examples/CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean)
  pairs a one-dimensional Gaussian coordinate with a fair Boolean coordinate.
  The prior uses `N(0,1)` and the fixed posterior uses `N(1/4,1)`. The checker
  proves that the posterior gives every finite set mass zero, verifies
  `KL = 1/32`, and uses a genuine zero-one loss that depends on both
  coordinates and attains both `0` and `1`. At `n = 2^20` and `delta = 1/2`,
  the theorem-produced right-hand side is below the trivial ceiling `1`, and
  `gaussianPosterior_goodPath_exists` proves that at least one path lies outside
  the exceptional event.
  This receipt fixes the posterior; it does not exercise data-dependent
  continuous-posterior selection.
- **Finite specialization:**
  `exists_infiniteEmpiricalBernstein_event` and
  [`CheckInfiniteEmpiricalBernsteinStitch.lean`](./examples/CheckInfiniteEmpiricalBernsteinStitch.lean)
  instantiate one all-`n` event for a fair-Boolean stream and a posterior
  selected from the first observation on a fixed finite hypothesis type.
- **Numerical comparison:**
  [identical-input benchmark](./benchmark/output/empirical_bernstein_flagship.md),
  where the exact stitched ceiling first falls below one at even `n = 128` in
  the reported scan.

### Fixed-sample empirical-Bernstein foundation

For finite IID data, $[0,1]$ losses, $n \ge 2$, and $0 < \delta < 1$, one event
controls every data-selected posterior over a fixed finite hypothesis catalog.
The theorem uses a fixed full-support prior, one KL term, the posterior average
of per-hypothesis Bessel variances, and a predeclared dyadic scale grid of depth
`ceil(log_2 n)` (written `Nat.clog 2 n` in Lean).

- **Lean theorems:**
  `finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta` and
  `finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem` in
  [`FiniteEmpiricalBernsteinSqrt.lean`](./FormalSLT/PACBayes/FiniteEmpiricalBernsteinSqrt.lean)
- **Checked example:**
  [`CheckFiniteEmpiricalBernsteinSqrt.lean`](./examples/CheckFiniteEmpiricalBernsteinSqrt.lean)
  checks `delta = 1/20`, `KL = log 2 > 0`, empirical variance
  `16/63 > 0`, an explicit positive-mass good sample, and a final ceiling below
  `99/100`.

### Time-uniform PAC-Bayes

One common event controls every positive time and every finite posterior PMF
for IID $[0,1]$ losses and one fixed declared tilt.

- **Lean theorem:** `timeUniformIIDPACBayes_allPosteriors_bound` in
  [`TimeUniformIID.lean`](./FormalSLT/PACBayes/TimeUniformIID.lean)
- **Verification:**
  [`CheckTimeUniformIIDPACBayes.lean`](./examples/CheckTimeUniformIIDPACBayes.lean)
  discharges the IID process obligations. A dedicated positive-KL subunit
  numerical receipt remains planned.

### Finite-tilt time-uniform PAC-Bayes

For finite hypothesis and tilt types, full-support priors, and measurable IID
$[0,1]$ losses, one event is shared by every positive time, every finite
posterior PMF, and every predeclared tilt atom.

- **Lean theorems:**
  `timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec` and
  `timeUniformIIDPACBayes_tiltMixture_selected_of_not_mem_measurableExceptionalEvent`
  in
  [`TimeUniformIIDTiltMixture.lean`](./FormalSLT/PACBayes/TimeUniformIIDTiltMixture.lean)
- **Checked example:**
  [`CheckTimeUniformIIDTiltMixture.lean`](./examples/CheckTimeUniformIIDTiltMixture.lean)
  checks `delta = 1/16`, point-posterior `KL = log 2`, both tilt boundaries at
  most `3/8`, and an existential good path with selected risk below `7/8`.
  Its explicit selector-branch exercises are not proved good.

### Forward-Bessel time-uniform PAC-Bayes

For bounded observations with a fixed conditional mean, FormalSLT starts from
the standard predictable-residual empirical-Bernstein e-process. It proves two
Bessel-variance upper envelopes for that process's quadratic penalty and uses
their smaller value separately for each hypothesis. The finite-hypothesis,
finite-tilt PAC-Bayes layer mixes the actual e-processes into one master
process. One outer-mass event then works for every time `n >= 2`, every
post-data posterior PMF, and every declared tilt atom. The selected atom may
depend on the path, time, and posterior. Its boundary pays one hypothesis KL
term and the selected atom's `log (1 / (delta * weight))` cost.

For finite hypotheses, a separate normalized `Nat`-indexed tilt mixture is an
actual master e-process. Its geometric tilt schedule permits post-path atom and
posterior substitution and gives an explicit selected boundary tending to
zero. The finite-state full-prefix trajectory adapter obtains the analogous
all-time vanishing conclusion by countable confidence allocation across
singleton events; it does not claim that this union is itself an e-process.

A separate continuous-prior engine integrates the actual parameterized
predictable-residual processes over an arbitrary measurable hypothesis space.
Its full-prefix trajectory adapter also permits an arbitrary measurable state
space, a deterministic initial state, and a `[0,1]` score jointly strongly
measurable in the hypothesis, complete prefix, and next state. That single
score contract derives the filtered and ambient product measurability. One
outer-mass event is simultaneous over every `n >= 2`, every eligible posterior
probability measure, and every atom of a finite positive predeclared tilt prior
with `0 < lambda_j < 1`.

- **Lean theorems:** `exists_forwardBesselPACBayes_event` and the IID endpoint
  `exists_forwardIIDBesselPACBayes_event` in
  [`ForwardBesselPACBayes.lean`](./FormalSLT/PACBayes/ForwardBesselPACBayes.lean)
  and
  [`ForwardBesselPACBayesIID.lean`](./FormalSLT/PACBayes/ForwardBesselPACBayesIID.lean)
- **Countable-tilt Lean theorems:**
  `exists_geometricForwardBesselPACBayes_allTime_vanishing_event` in
  [`ForwardBesselPACBayesCountable.lean`](./FormalSLT/PACBayes/ForwardBesselPACBayesCountable.lean)
  and the full-prefix trajectory endpoint
  `exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event`
  in
  [`TrajectoryEmpiricalBernsteinPACBayesCountable.lean`](./FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.lean)
- **Continuous Lean theorems:**
  `exists_continuousForwardPredictableMeanBesselPACBayes_event` in
  [`ContinuousForwardPredictableMeanBesselPACBayes.lean`](./FormalSLT/PACBayes/ContinuousForwardPredictableMeanBesselPACBayes.lean)
  and the arbitrary-state trajectory capstone
  `exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event` in
  [`ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean`](./FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean)
- **Checked example:**
  [`CheckForwardBesselPACBayesIID.lean`](./examples/CheckForwardBesselPACBayesIID.lean)
  uses a fair-Boolean IID stream, a posterior selected from the observed label,
  and a path/time/posterior-dependent tilt selector. It checks event mass at
  most `1/2`, `KL = log 2`, and existence of a good path.
- **Informative receipt:**
  [`CheckForwardBesselPACBayesIIDInformative.lean`](./examples/CheckForwardBesselPACBayesIIDInformative.lean)
  uses a biased Boolean IID stream at `n = 32` and `delta = 1/160`. It proves
  positive Bessel sample variance `1/32`, `KL = log 2`, a theorem-produced
  good path in a prefix cylinder of mass greater than `delta`, and a selected
  risk ceiling below `343/1000`. On the same prefix, the checked
  empirical-Bernstein boundary lies in `(0.3117, 0.3118)`, while the
  fixed-proxy sub-Gamma boundary lies in `(0.7599, 0.7600)`.
- **Continuous-hypothesis, real-state receipt:**
  [`CheckContinuousMeasurableTrajectoryGaussianWitness.lean`](./examples/CheckContinuousMeasurableTrajectoryGaussianWitness.lean)
  uses `Theta = (Fin 1 -> Real) x Bool`, state space `Real`, a
  standard-Gaussian/fair-Boolean prior, a Gaussian mean-shift `1/4` posterior,
  and a fair-Rademacher state kernel. It proves posterior finite-set mass zero,
  `KL = 1/32`, posterior conditional and empirical risks both `1/2`, and, at
  `n = 64`, `delta = 1/8`, and `lambda = 1/2`, boundary
  `<= 489/1024 < 1/2`. Each opposite-sign two-step cylinder has mass `1/4`
  and contains a path in the same theorem-produced good event; every fixed
  hypothesis has positive observed Bessel sample variance there, and the
  complete right-hand side is below one.

The displayed hybrid Bessel expression is only a checked lower envelope of the
actual predictable-residual e-process; it is not itself proved to be an
e-process. The informative receipt compares boundary formulas on one selected
prefix; it does not assert that this path lies outside the fixed-proxy lane's
separate exceptional event. The checked countable result is finite-hypothesis
and uses an explicit geometric selector; it is not all-real optimization or a
predictable tilt rule. The continuous-prior and arbitrary-state event remains
finite-tilt and is
posterior-uniform but does not construct a measurable posterior selector or a
selected process, and its trajectory adapter starts deterministically. The
arbitrary-state endpoint requires a supplied jointly measurable score family;
it does not learn that family from the scored path. The continuous-hypothesis
receipt fixes its posterior and tilt, and its real-state dynamics have only two
atoms; it is not an atomless-dynamics receipt or a matched boundary comparison.
No novelty or priority claim is made.

### Finite Markov prequential PAC-Bayes

For a finite-state Markov transition kernel, a supplied finite-state initial
PMF, fixed finite predictor catalog, and predeclared full-support finite tilt
prior, one tilt atom may be selected after the trajectory. The initial PMF
need not have full support, and a point mass recovers the deterministic-start
law. The target is encountered one-step conditional risk, not stationary risk.

- **Lean theorems:**
  `markovPACBayes_tiltMixture_prequentialRisk_certificate` and
  `markovPACBayes_tiltMixture_prequentialRisk_certificate_initialLaw` in
  [`MarkovPACBayesTiltMixture.lean`](./FormalSLT/StochasticDynamics/MarkovPACBayesTiltMixture.lean)
  and
  [`MarkovPACBayesTiltMixtureInitialLaw.lean`](./FormalSLT/StochasticDynamics/MarkovPACBayesTiltMixtureInitialLaw.lean)
- **Checked example:**
  [`CheckMarkovPACBayes.lean`](./examples/CheckMarkovPACBayes.lean) uses an
  asymmetric two-state chain, a path-selected point posterior and tilt atom,
  exact `KL = log 2`, two selected boundaries below `1/20`, and conditional
  risk below `11/20`. Its random-initial receipt has masses `1/3` and `2/3`,
  exceptional mass at most `1/20`, and measurable good-complement mass at
  least `19/20`. The explicit selector-branch paths are not proved good or
  positive-probability.

### Supplied-Poisson stationary PAC-Bayes

For a finite-state homogeneous Markov kernel, a deterministic initial state,
a supplied invariant PMF, and a finite catalog of bounded transition scores
with supplied bounded Poisson potentials, one outer-mass event controls the
posterior stationary risk at every `n >= 2` and every declared finite tilt
atom. Exact Poisson solutions leave only the empirical-Bernstein width of the
corrected score and a telescoping endpoint price bounded by `B / n`;
approximate solutions additionally retain an explicit residual envelope.

- **Lean theorem:**
  `exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_span_event` in
  [`StationaryPoissonPACBayes.lean`](./FormalSLT/StochasticDynamics/StationaryPoissonPACBayes.lean)
- **Checked example:**
  [`CheckStationaryPoissonPACBayes.lean`](./examples/CheckStationaryPoissonPACBayes.lean)
  proves invariance of the asymmetric Boolean chain with stationary PMF
  `(2/3, 1/3)`, verifies two nonconstant exact potentials, checks that the
  corrected score attains both `0` and `1`, and instantiates the all-time,
  all-posterior theorem at `delta = 1/20`.

The invariant PMF and potentials are theorem inputs. This module does not
infer an invariant law, solve a Poisson equation, estimate an unknown kernel,
derive a span bound from contraction or mixing, or assert measurability of the
outer-mass event. State, hypothesis, and tilt types remain finite.

### Finite-depth Poisson construction and computed contraction

For a known finite transition kernel and a supplied invariant PMF, the library
now constructs the depth-`m` truncated potential
`h_m = sum_{t < m} T^t (g - R)`. Under oscillation contraction by
`0 <= alpha < 1` and centered row-risk oscillation at most `D`, its potential
span is at most `D * (1 - alpha^m) / (1 - alpha)` and its pointwise Poisson
residual is at most `alpha^m * D`. Substituting these bounds into the supplied
bridge gives one outer-mass stationary-risk event shared by every `n >= 2`,
posterior PMF, and declared finite tilt atom.

For finite kernels, `finiteDobrushinCoefficient` computes `alpha` as the
maximum pairwise row total variation under the `TV = L1 / 2` convention. The
sharp finite-PMF duality theorem proves that this coefficient contracts
oscillation, so the public Dobrushin capstone requires no separately supplied
potential or contraction proof.

- **Lean theorem:**
  `exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_unit_event`
  in
  [`StationaryPoissonDobrushin.lean`](./FormalSLT/StochasticDynamics/StationaryPoissonDobrushin.lean)
- **Checked example:**
  [`CheckStationaryPoissonContraction.lean`](./examples/CheckStationaryPoissonContraction.lean)
  computes coefficient `1/4` for an asymmetric Boolean kernel, proves the
  oscillation bound is attained by an indicator, checks the depth-two
  potential and residual exactly, and instantiates the stationary certificate.

The fixed-depth capstones keep the kernel, invariant PMF, and `m` as inputs.
They do not estimate an unknown kernel, construct or prove uniqueness of an
invariant law, or claim irreducibility, a mixing time, or a measurable
confidence event. The next module confidence-allocates over all finite depths.

### Confidence-allocated Poisson depth selection

For a known finite kernel, supplied invariant PMF, strict oscillation
contraction `0 <= alpha < 1`, and finite score catalog, one outer-mass event is
simultaneous over every finite Poisson depth, geometric tilt atom, time
`n >= 2`, and posterior PMF. Depth `m` receives weight
`1 / ((m + 1) * (m + 2))`, so the exact nested confidence price is
`log (((m+1)(m+2)(j+1)(j+2))/delta)`. A depth, tilt, and posterior may then be
chosen after observing the path by substitution into this common event.

The deterministic choices `m(n) = floor(log_2 n)` and the all-time geometric
tilt give a complete stationary-risk width that tends to zero for every path
and every time-varying finite posterior. The width retains all three terms:
the empirical-Bernstein trajectory contribution, the endpoint span divided by
`n`, and the geometric residual `alpha^m D`.

- **Lean theorem:**
  `exists_stationaryPoissonDepthSelection_allTime_vanishing_event` in
  [`StationaryPoissonDepthSelection.lean`](./FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.lean)
- **Checked examples:**
  [`CheckStationaryPoissonDepthSelection.lean`](./examples/CheckStationaryPoissonDepthSelection.lean)
  instantiates the common event and vanishing-width theorem; and
  [`CheckStationaryPoissonContraction.lean`](./examples/CheckStationaryPoissonContraction.lean)
  evaluates nonconstant depth-one and depth-two potentials on one asymmetric
  Boolean prefix, exposes confidence prices `log 240` and `log 480`, and proves
  that the finite post-path argmin is no worse than either declared depth.

This is confidence allocation, not a selected e-process: neither the
envelope-penalized boundary nor the countable depth union is claimed to be a
master e-process. The event is controlled by outer mass, with no separate
measurability theorem. The kernel and invariant PMF remain supplied, and the
result remains finite-state and finite-hypothesis.

### Candidate-kernel robustness and invariant-target uniqueness

The stationary bridge also permits a fixed candidate kernel `Q` to supply the
Poisson correction when the trajectory is generated by a different true
kernel `P`. If each true row is within probabilists' total variation `eta` of
the corresponding candidate row, the score lies in `[0,1]`, and the candidate
potential has span at most `B`, the true and candidate Poisson drifts differ by
at most `(1 + B) * eta`. Centering at a supplied invariant PMF of `P` gives the
uniform residual envelope
`oscillation(g_Q) + 2 * (1 + B) * eta`. A path-adaptive theorem replaces the
candidate oscillation term by an observed max-minus-running-mean correction.

For the depth-`m` potential constructed from `Q`, the capstone uses the
explicit residual price
`alpha_Q^m * D + 2 * (1 + B_m) * eta`. Separately, the deterministic
perturbation theorem proves
`Dobrushin(P) <= Dobrushin(Q) + 2 * eta`. Thus the checkable strict inequality
`Dobrushin(Q) + 2 * eta < 1` certifies contraction of `P`, uniqueness among
supplied invariant PMFs of `P`, and independence of the stationary-risk target
from the supplied invariant witness.

- **Lean theorems:**
  `exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event` in
  [`StationaryPoissonRobustCandidate.lean`](./FormalSLT/StochasticDynamics/StationaryPoissonRobustCandidate.lean)
  and `stationaryPosteriorMarkovRisk_eq_of_candidate_rowTV` in
  [`StationaryPoissonRobustInvariant.lean`](./FormalSLT/StochasticDynamics/StationaryPoissonRobustInvariant.lean)
- **Checked examples:**
  [`CheckStationaryPoissonRobustCandidate.lean`](./examples/CheckStationaryPoissonRobustCandidate.lean)
  exhibits the necessary factor two, its sharpness, and both uniform and
  path-adaptive robust certificates; and
  [`CheckStationaryPoissonRobustInvariant.lean`](./examples/CheckStationaryPoissonRobustInvariant.lean)
  verifies the contraction certificate, invariant uniqueness, and target
  independence for distinct Boolean kernels.

The candidate kernel, row-TV radius, reference PMF, invariant PMF, and depth
are supplied deterministic inputs. These modules do not estimate a kernel or
row-TV radius, construct an invariant PMF, justify post-data candidate or
depth selection, or cover continuous state spaces.

### Empirical transition confidence and plug-in contraction

For an unknown finite homogeneous kernel `P`, the visit-gated indicators
`1{x_k = z, x_{k+1} = y}` and their complements form one finite score catalog.
The forward empirical-Bernstein trajectory theorem then gives one outer-mass
event, shared by every `n >= 2`, declared tilt atom, source, and destination,
with two-sided confidence bands for the predictable transition masses. A
visited row can be normalized by its observed visit count to give coordinate
confidence radii and a row-total-variation certificate.

The candidate kernel is universally quantified inside this common event. It
may therefore be selected after observing the path without an additional
candidate-selection penalty. When every row has been visited, the maximum
empirical row discrepancy plus the simultaneous statistical radius gives a
uniform row-TV budget. Combining it with the robust Dobrushin lemmas certifies
`Dobrushin(P) <= Dobrushin(Q) + 2 * eta`, true-kernel oscillation contraction,
and uniqueness among supplied invariant PMFs whenever the displayed factor is
strictly below one.

- **Lean theorem:**
  `exists_selectedEmpiricalKernelContraction_event` in
  [`EmpiricalTransitionConfidence.lean`](./FormalSLT/StochasticDynamics/EmpiricalTransitionConfidence.lean)
- **Checked example:**
  [`CheckEmpiricalTransitionConfidence.lean`](./examples/CheckEmpiricalTransitionConfidence.lean)
  instantiates the all-time event for a Boolean kernel and proves a separate
  balanced-prefix arithmetic receipt at `n = 1024`: every row is visited 512
  times, the fair candidate has zero empirical discrepancy, the certified
  kernel-TV budget is below `1/4`, and the candidate perturbation factor is
  below one.

The normalized claims require positive visit mass, and the all-row contraction
certificate requires every source row to have been visited. The balanced path
receipt proves deterministic arithmetic conditional on membership in the
statistical good event; it does not prove that named path belongs to the event
or that their intersection has positive probability. The module does not
estimate an invariant PMF, prove invariant-law existence, produce a mixing
time, or justify constructing a Poisson potential from the same data without
a separately uniformized catalog or sample split. Its event is an outer-mass
package; no measurability theorem for that event is claimed.

### Same-trajectory stationary catalogs and finite invariant targets

For an unknown finite homogeneous kernel `P` with deterministic initial state,
the stationary catalog theorem fixes a finite candidate-kernel catalog,
reference PMFs, centered-risk envelopes, and full-support candidate weights
before observing the path. Its risk event allocates simultaneously over every
candidate, finite Poisson depth, countable geometric risk-tilt atom, time
`n >= 2`, and finite-class posterior. Intersecting that event with the
transition-coordinate event from the preceding section costs exactly
`deltaRisk + deltaTransition`; both events use the same trajectory and require
neither independence nor sample splitting.

When every source row has positive visit mass, the candidate, depth, risk and
transition tilts, and posterior may depend on the observed path and time by
substitution into the common event. The resulting certificate targets the
chosen invariant law `finiteInvariantPMF P` and combines the observed
hybrid-Bessel/KL term, endpoint term, candidate contraction residual, and
same-path row-TV transfer. It also returns a plug-in Dobrushin bound and makes
invariant-law uniqueness conditional on the selected strict contraction
certificate.

Every kernel on a nonempty finite state space has an invariant PMF:
`exists_invariantPMF` proves existence from Cesaro averages and compactness of
the real probability simplex. `finiteInvariantPMF` is a noncomputable chosen
witness. A Dobrushin coefficient below one, or a strict candidate row-TV
certificate, upgrades existence to a unique invariant PMF.

- **Lean theorems:**
  `exists_selectedCanonicalEmpiricalStationaryCatalog_event` in
  [`EmpiricalStationaryCatalog.lean`](./FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean)
  and `exists_invariantPMF` in
  [`FiniteInvariantExistence.lean`](./FormalSLT/StochasticDynamics/FiniteInvariantExistence.lean)
- **Checked examples:**
  [`CheckEmpiricalStationaryCatalog.lean`](./examples/CheckEmpiricalStationaryCatalog.lean)
  checks the two-candidate structural theorem; its explicit selector-branch
  paths are arithmetic receipts and are not claimed good.
  [`CheckEmpiricalStationaryCatalogInformative.lean`](./examples/CheckEmpiricalStationaryCatalogInformative.lean)
  proves theorem-produced good paths in both selected-candidate branches for
  the risk-catalog component, with positive KL and Bessel variance and an
  informative boundary. It supplies the row-TV errors exactly, fixes depth
  zero, and does not exercise the combined transition-confidence event.
  [`CheckFiniteInvariantExistence.lean`](./examples/CheckFiniteInvariantExistence.lean)
  verifies existence, the chosen asymmetric Boolean invariant law, and both
  strict uniqueness routes.

The candidate kernels and their potential data must be in the finite declared
catalog before the scored path is observed; this does not validate an
arbitrary path-fitted candidate or score. Normalized row-TV transfer still
requires every row to be visited. The result remains finite-state with a
deterministic start, and its common event is controlled by outer mass without
a separate measurability theorem. The selected boundary is not asserted to be
an e-process. Finite invariant existence supplies neither a computable closed
form nor irreducibility, a convergence rate, or a mixing time; uniqueness
requires one of the displayed strict contraction hypotheses.

### Controlled trajectory semantics

For finite state and action spaces, `ControlledTrajectory` constructs the path
law generated by a full-history behavior policy and a homogeneous controlled
environment. For a predeclared finite target-policy catalog, bounded transition
scores, overlap, and a common importance-ratio cap, it proves that the
normalized one-step importance score has the exact predictable conditional
mean required by the forward empirical-Bernstein PAC-Bayes engine.

- **Lean interface:**
  `controlledImportanceCatalog_predictableMean_interfaces` in
  [`ControlledTrajectory.lean`](./FormalSLT/StochasticDynamics/ControlledTrajectory.lean)
- **Checked example:**
  [`CheckControlledTrajectory.lean`](./examples/CheckControlledTrajectory.lean)
  uses two reachable Boolean histories with the same initial and current state
  but different interior actions, checks distinct behavior weights, and proves
  positive support for every displayed continuation atom.

This is a behavior-law semantic and conditional-expectation interface. It does
not identify stationary target-policy value, correct target-versus-behavior
state occupancy, or prove a target-trajectory off-policy evaluation theorem.

### Stationary target-policy off-policy evaluation

`StationaryTargetPolicyOPE` combines the controlled behavior-law interface
with a supplied invariant PMF and exact bounded Poisson potential for each
state-Markov target policy. With known environment and behavior propensities,
explicit overlap and a common action-ratio cap, one outer-mass event controls
the posterior stationary target-policy risk at every `n >= 2` and every atom
of a finite declared tilt catalog. The posterior and tilt may be chosen
pointwise after the behavior path because the event is simultaneous.

- **Lean theorem:** `exists_stationaryTargetPolicyOPE_event` in
  [`StationaryTargetPolicyOPE.lean`](./FormalSLT/StochasticDynamics/StationaryTargetPolicyOPE.lean)
- **Checked example:**
  [`CheckStationaryTargetPolicyOPE.lean`](./examples/CheckStationaryTargetPolicyOPE.lean)
  verifies two Boolean target policies, ratios `1/2` and `3/2`, exact
  invariant laws and nonconstant Poisson potentials, constant predictable mean
  `4/15`, and positive observed Bessel variation.

The theorem uses one-step action importance ratios. It does not estimate the
environment, behavior propensities, invariant laws, or potentials; it is not a
full-trajectory importance-sampling or target-occupancy correction theorem.

### Dynamic target-policy comparators

`DynamicTargetPolicyComparator` controls finite catalogs of history-dependent
target policies along the prefixes encountered under a history-dependent
behavior policy. `PrefixDynamicTargetPolicyComparator` additionally permits a
known environment kernel that depends on time and the complete available
prefix. Under bounded transition scores, overlap, and a common action-ratio
cap, one outer event is simultaneous over every `n >= 2`, posterior PMF, and
atom of a finite declared tilt catalog.

- **Lean theorems:** `exists_dynamicTargetPolicyComparator_event` and
  `exists_prefixDynamicTargetPolicyComparator_event` in
  [`DynamicTargetPolicyComparator.lean`](./FormalSLT/StochasticDynamics/DynamicTargetPolicyComparator.lean)
  and
  [`PrefixDynamicTargetPolicyComparator.lean`](./FormalSLT/StochasticDynamics/PrefixDynamicTargetPolicyComparator.lean)
- **Checked example:**
  [`CheckDynamicTargetPolicyComparator.lean`](./examples/CheckDynamicTargetPolicyComparator.lean)
  verifies two reachable Boolean histories with the same initial and current
  state but different interior actions, history-dependent target risks
  `5/8` and `3/8`, a prefix-dependent environment witness, positive support,
  and positive observed Bessel variation for both target atoms.

The controlled quantity is the posterior average of target one-step
conditional risks at behavior-realized prefixes. It is not target-policy
occupancy or value, full-trajectory importance sampling, doubly robust OPE, or
unknown-environment inference.

### Finite-horizon target-path change of measure

`TargetPathChangeOfMeasure` constructs the finite-prefix law of a supplied
history-dependent target policy under the same known prefix-dependent
environment and identifies it with the corresponding marginal of the actual
infinite target trajectory law. Under overlap, the target expectation of every
finite-prefix payoff equals its behavior-law expectation weighted by the
product of target-to-behavior action likelihood ratios. Event, terminal-state
occupancy, and finite-horizon risk forms are exposed separately.

- **Lean theorem:**
  `prefixControlledTargetTrajectory_integral_changeOfMeasure` in
  [`TargetPathChangeOfMeasure.lean`](./FormalSLT/StochasticDynamics/TargetPathChangeOfMeasure.lean)
- **Checked example:**
  [`CheckTargetPathChangeOfMeasure.lean`](./examples/CheckTargetPathChangeOfMeasure.lean)
  verifies likelihood ratios `3/2` and `1/2`, unit behavior expectation, and
  recovery of target state occupancy `3/4` from behavior occupancy `1/2`.

This is an exact finite-horizon identity, not an anytime concentration result.
A one-step ratio cap `C` gives only the explicit worst-case range `C ^ n`; no
vanishing full-trajectory importance-sampling boundary, unknown-environment
inference, or learned-nuisance guarantee is claimed.

The source theorem, exact agreement, material differences, and external-review
questions for selected flagship results are tracked in
[`docs/LITERATURE.md`](./docs/LITERATURE.md).

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
  posteriors, finite-grid data-dependent tilt selection, and a finite normalized
  hypothesis--tilt master e-process whose one Ville event permits path- and
  posterior-dependent selection of a declared tilt atom. A finite-IID adapter
  discharges the measurable bounded-loss process assumptions and packages the
  result as one measurable exceptional event. The library also has a
  process-level theorem over arbitrary measurable hypothesis spaces and an
  end-to-end i.i.d. bounded-loss theorem over finite-dimensional
  spherical-Gaussian hypotheses with a checked closed-form KL penalty and a
  stochastic fair-Bernoulli product-stream certificate.
- **Finite Markov prequential risk:** an actual Ionescu--Tulcea path law for a
  finite transition PMF, a derived next-step conditional-risk identity, the
  sharp universal `1/4` conditional-variance proxy for `[0,1]` losses, an
  anytime two-sided fixed-predictor certificate, and a PAC-Bayes certificate
  simultaneous over all positive times and posteriors on a finite predictor
  catalog. A normalized finite tilt prior whose atoms satisfy `0 < λ_j < 3`
  gives one measurable exceptional event; on its complement, the posterior
  and one predeclared tilt atom may be selected after the trajectory, with the
  atom's exact weight penalty. The same common failure set is controlled under
  an arbitrary supplied finite-state initial PMF by mixing the
  deterministic-start path laws before taking one measurable hull.
- **Test-time PAC-Bayes certificate:** a finite-horizon, five-component
  population-risk bound assembled from a conditional sub-Gamma increment
  model, with a worked instance proving all five contributions strictly
  positive.
- **Probability and statistics foundations:** scoped interfaces for measure
  convergence, laws of large numbers, moments, finite estimation, Fisher
  information, Cramer-Rao, finite exponential families, and asymptotic
  statistics.
- **Empirical-Bernstein PAC-Bayes:** Bessel-corrected loss variance, its
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
  contributes the explicit penalty `xi / t`. A support-aware countable master
  event and downstream finite-posterior selector over a predeclared
  `Nat`-indexed tilt-pair catalog are checked separately. The selected bound
  uses that same fixed-sample event and one KL term. The closed-form flagship
  now fixes a dyadic
  scale grid of depth `clog 2 n` before observing the data and proves, on one
  event of failure mass at most `delta`,
  $R(\rho) \le \widehat R(\rho) + \frac{5}{4} \sqrt{\frac{2 \widehat V(\rho) L(\rho)}{n}} + \frac{5}{2} \frac{L(\rho)}{n}$, where
  $L(\rho) = \mathrm{KL}(\rho \| \mathrm{prior}) + \log((\mathrm{clog}_2 n + 1) / \delta)$.
  A reverse-exchangeability layer now proves the Bessel conditional-expectation
  identity, reverse Bessel martingale, reverse joint mean/variance exponential
  submartingale, one-event posterior catalog on each dyadic epoch, and the
  reverse closed-form bound. Countable stitching on the infinite IID product
  space then gives one measurable event of mass at most `delta` on whose
  complement every `n >= 2` and every finite posterior obey
  $R(\rho) < \widehat R_n(\rho) + \frac{5}{2} \sqrt{\frac{\widehat V_n(\rho) L_n(\rho)}{n}} + \frac{5 L_n(\rho)}{n}$, where
  $L_n(\rho) = \mathrm{KL}(\rho \| \mathrm{prior}) + \log(r(r+1)^2 / \delta)$ and
  `r = Nat.log 2 n`. The same reverse construction is also checked over an
  arbitrary measurable hypothesis space: it integrates the per-hypothesis
  Bessel variance under every admissible posterior measure and uses one
  measure-theoretic KL term. The observations remain finite-valued. This is an
  offline reverse-epoch theorem, not a forward e-process, optional-stopping
  result, all-real optimizer, or continuous-observation theorem.

The Dudley core is finite by design. The finite-outcome endpoint
`continuous_dudley_entropy_integral` assumes a finite sub-Gaussian process on a
nonempty pseudometric index, a totally bounded universal index set, positive
`radiusScale` and process variance proxy, agreement of the process and ambient
distances, an antitone nonnegative interval-integrable entropy profile, and
supplied separable-terminal boundary certificates. The measure-side endpoint is
instead an expectation-operator lift from a supplied `MeasureChainingBudget`;
it does not construct those metric or chaining hypotheses. Arbitrary measurable
suprema remain out of scope. The general continuous time-uniform PAC-Bayes
theorem remains process-level; its i.i.d. specialization currently covers
finite-dimensional spherical Gaussian priors and posteriors. The separate
all-sample-size empirical-Bernstein endpoint covers arbitrary measurable
hypothesis spaces but retains finite-valued observations. The statistics
interfaces preserve the hypotheses of the Mathlib results they expose. See
[Scope and open boundaries](#scope-and-open-boundaries) for the exact limits.

**Zero `sorry`. Zero `admit`. Zero custom axioms.** The public checker files
print only `[propext, Classical.choice, Quot.sound]`.

Badge counts are generated from the source tree by
[`scripts/generate_badge_counts.py`](./scripts/generate_badge_counts.py) and
checked in CI.

[![FormalSLT proof landscape: finite learning, metric entropy, PAC-Bayes including all-sample-size empirical Bernstein, anytime-valid inference, and dependent and composed results](./docs/theorem-chain.svg)](./docs/theorem-chain.svg)

*Conceptual theorem-family map, not a literal import graph. Exact assumptions
are recorded in theorem signatures and checkers. Detailed lane diagrams are in
[docs/diagrams.md](./docs/diagrams.md); select the map to open it full size.*

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
- **Finite PMF and KL interoperability with Mathlib** —
  `IsPMF.toPMF` and `IsPMF.integral_toPMF_eq_sum` expose finite real PMFs and
  their weighted sums through Mathlib's `PMF` and measure-integral APIs;
  `informationTheory_klDiv_toPMF_eq_of_support` identifies FormalSLT's finite
  real KL sum with Mathlib's extended-real KL divergence under posterior-support
  inclusion in the prior. The disjoint-support checker shows this condition
  cannot be omitted in general;
  [`CheckFinitePMFBridge.lean`](./examples/CheckFinitePMFBridge.lean)
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
- **Finite weighted-tilt Markov PAC-Bayes certificate** —
  `markovPACBayes_tiltMixture_prequentialRisk_certificate` gives one measurable
  exceptional event of probability at most `delta`; on its complement the
  bound is simultaneous over all positive times, posterior PMFs, and atoms
  `0 < λ_j < 3` of a full-support finite tilt prior. A pointwise selector may
  choose one predeclared atom after the trajectory and pays
  `log (1 / (delta * weight j))`. The selector need not be measurable or
  adapted: this uses the common all-atom event and adds no optional-stopping
  claim. In the asymmetric two-state receipt, the path-selected posterior has
  exact KL `log 2`, both selected boundaries are below `1/20`, and conditional
  risk is below `11/20` at confidence `19/20`. The two explicit paths only
  exercise selector branches; they are not proved good or positive-probability;
  [`CheckMarkovPACBayes.lean`](./examples/CheckMarkovPACBayes.lean)
- **Finite controlled-trajectory importance semantics** —
  `controlledObservedImportanceScore_condExp` and
  `controlledImportanceCatalog_predictableMean_interfaces` derive the exact
  behavior-law predictable mean for normalized one-step target-policy scores
  under explicit overlap and ratio-cap assumptions;
  [`CheckControlledTrajectory.lean`](./examples/CheckControlledTrajectory.lean)
- **Stationary target-policy OPE certificate** —
  `exists_stationaryTargetPolicyOPE_event` gives one behavior-law outer event
  uniform over all `n >= 2`, posterior PMFs, and finite declared tilt atoms for
  known finite controlled dynamics with supplied invariant laws and exact
  bounded Poisson potentials;
  [`CheckStationaryTargetPolicyOPE.lean`](./examples/CheckStationaryTargetPolicyOPE.lean)
- **Dynamic target-policy comparator certificates** —
  `exists_dynamicTargetPolicyComparator_event` and
  `exists_prefixDynamicTargetPolicyComparator_event` give behavior-law events
  uniform over all `n >= 2`, posterior PMFs, and finite declared tilt atoms for
  history-dependent targets under homogeneous or known prefix-dependent
  controlled dynamics;
  [`CheckDynamicTargetPolicyComparator.lean`](./examples/CheckDynamicTargetPolicyComparator.lean)
- **Finite-horizon target-path change of measure** —
  `prefixControlledTargetTrajectory_integral_changeOfMeasure` identifies
  target-path finite-prefix expectations with likelihood-weighted behavior-path
  expectations, with event, occupancy, risk, and explicit `C ^ n` range forms;
  [`CheckTargetPathChangeOfMeasure.lean`](./examples/CheckTargetPathChangeOfMeasure.lean)
- **Finite adaptive-selection cost guardrail** —
  `selectedWeightedScore_expectation_le_one` proves that predeclared weights
  preserve the e-value expectation bound under an observation-dependent
  selector, while `diagonalSpike_scalarCorrection_safe_iff_card_le` and
  `diagonalSpike_logCorrection_ge_logCard` give a sharp finite diagonal
  witness: a common scalar correction must be at least the catalog size, hence
  pays at least `log |I|` on the log scale;
  [`CheckSelectionCost.lean`](./examples/CheckSelectionCost.lean)
- **Countable-allocation log-log guardrail** —
  `exists_small_weight_on_dyadicBlock` proves that every inclusive block
  `[N, 2N]` of a nonnegative summable allocation contains an atom of weight at
  most `1 / (N + 1)`. For positive weights,
  `frequently_geometricEpoch_loglogCost` converts this into an explicit
  `log log`-sized cost along an unbounded subsequence of geometric epochs.
  `polynomialEpochWeight_hasSum` and
  `polynomialGeometricEpoch_log_cost` give the exact telescoping allocation
  receipt. This is an allocation/union-stitching obstruction, not a universal
  confidence-sequence or LIL lower bound;
  [`CheckAllocationLogLog.lean`](./examples/CheckAllocationLogLog.lean)
- **Universal fair-sign anytime-boundary floor** —
  `fairSign_anytimeBoundary_frequently_ge_mul_sqrt` proves unconditionally
  that any deterministic one-sided boundary with crossing probability below
  one must exceed every fixed nonnegative multiple of `sqrt n` infinitely
  often. `fairSign_anytimeBoundary_eventually_ge_sqrt` gives the complementary
  CLT/Portmanteau floor at each fixed Gaussian-tail level. The sharp
  `sqrt(2 n log log n)` constant-one corollary is checked only under the
  explicit, still-unproved `FairSignUpperLIL` premise and the theorem's
  bounded-ratio side condition;
  [`CheckUniversalBoundaryLowerBound.lean`](./examples/CheckUniversalBoundaryLowerBound.lean)
- **Random-initial finite weighted-tilt Markov PAC-Bayes certificate** —
  `markovPACBayes_tiltMixture_prequentialRisk_certificate_initialLaw` mixes the
  deterministic-start path laws against an arbitrary supplied finite-state
  initial PMF without a union bound or added confidence penalty. The initial
  PMF need not have full support, and `markovPathMeasureInitial_pure` recovers
  the deterministic-start law. The non-Dirac Boolean receipt has initial
  masses `1/3` and `2/3`, exceptional mass at most `1/20`, and good-complement
  mass at least `19/20`. This remains a homogeneous finite-state one-step-risk
  theorem, not a stationary, mixing, controlled-kernel, or continuous-state
  result;
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
  $R(\rho) \le (7/4) \widehat R(\rho) + (21/(8n))(\mathrm{KL}(\rho\|\pi) + \log(1/\delta))$;
  `indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem` truncates this at
  one. The concrete balanced sample of size `40` discharges the good-event
  premise and yields the checked certificate $R(\rho) \le 301/320 < 1$;
  [`CheckIndicatorBernsteinLowRisk.lean`](./examples/CheckIndicatorBernsteinLowRisk.lean)
- **Finite weighted indicator-Bernstein tilt catalog** —
  `indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta`
  allocates confidence budget `delta * w_j` across a fixed finite tilt family,
  while
  `indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem`
  permits the selected entry to depend on both the observed sample and
  posterior. The four-entry unequal-weight receipt proves catalog mass at most
  $1/2$ and an empirical-risk-selected certificate $R(\rho) \le 13/14 < 1$.
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
- **Closed-form empirical-Bernstein PAC-Bayes bound** —
  `finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta` and
  `finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem` turn the
  one-event joint score into the literature-shaped square-root-plus-linear
  endpoint. The catalog is fixed at dyadic scales `2 / 2^j` for
  `j <= clog 2 n`; the sample and posterior may then select the useful atom on
  the already-simultaneous event. The final constants are `5/4` on
  `sqrt(2 Vhat L / n)` and `5/2` on `L/n`, with one KL term and logarithmic
  grid cost. The `n = 64`, `delta = 1/20` receipt has positive KL, positive
  empirical variance, an explicit positive-mass good sample, and a ceiling
  below `99/100`. The hypothesis catalog and full-support prior are fixed
  before the sample. This is fixed-sample and finite-hypothesis; it is neither
  all-real optimized nor time-uniform;
  [`CheckFiniteEmpiricalBernsteinSqrt.lean`](./examples/CheckFiniteEmpiricalBernsteinSqrt.lean),
  [`FiniteEmpiricalBernsteinSqrt.lean`](./FormalSLT/PACBayes/FiniteEmpiricalBernsteinSqrt.lean)
- **All-sample-size empirical-Bernstein PAC-Bayes bound** —
  `exists_continuousInfiniteEmpiricalBernstein_event` constructs one measurable
  exceptional set of infinite IID paths with mass at most `delta` for an
  arbitrary measurable hypothesis space. Outside it, every prefix size
  `n >= 2` and every posterior probability measure absolutely continuous with
  respect to the fixed prior with integrable log-likelihood ratio satisfy
  $R_{\rho} < \widehat R_{\rho,n} + (5/2) \sqrt{\widehat V_{\rho,n} L_{\rho,n} / n} + 5 L_{\rho,n} / n$,
  with $L_{\rho,n} = \mathrm{KL}(\rho \| \mathrm{prior}) + \log(r(r+1)^2 / \delta)$ and
  `r = Nat.log 2 n`. The posterior may be substituted pointwise from the path
  because the same event is uniform over all admissible posteriors. The finite-
  hypothesis specialization uses a fair-Boolean IID stream and a point
  posterior selected from the first coordinate. The continuous Gaussian
  receipt uses `Theta = (Fin 1 -> Real) x Bool`, an `N(0,1)` product fair-
  Boolean prior, and a fixed `N(1/4,1)` product fair-Boolean posterior. It
  checks posterior finite-set mass zero, `KL = 1/32`, and an unscaled zero-one
  sign-flip mismatch loss that depends on both coordinates and attains both
  endpoints. Every nonempty-sample posterior empirical risk is `1/2`; at
  `n = 2^20` and `delta = 1/2`, the correction is below `1/2` and the theorem-
  produced right-hand side is below `1`, and a checked corollary gives a path
  outside the exceptional event. The receipt does not exercise data-dependent
  continuous-posterior selection. The balanced-64 fixed-sample receipt above
  separately checks positive empirical variance and positive sample mass. The
  deterministic [benchmark report](./benchmark/output/empirical_bernstein_flagship.md)
  compares the stitched formulas with fixed empirical-Bernstein,
  McAllester/Hoeffding, and PAC-Bayes-kl on identical summary statistics; it
  evaluates constants and does not certify a particular infinite path as good.
  The proof uses reverse-epoch martingales and countable stitching, not a
  forward e-process or optional-stopping API;
  [`CheckContinuousInfiniteEmpiricalBernsteinStitch.lean`](./examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean),
  [`CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean`](./examples/CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean),
  [`ContinuousInfiniteEmpiricalBernsteinStitch.lean`](./FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean),
  [`CheckInfiniteEmpiricalBernsteinStitch.lean`](./examples/CheckInfiniteEmpiricalBernsteinStitch.lean)
- **Countable fixed-sample joint master and finite-posterior selector** —
  `countableJointMeanVariance_catalogBadSamples_mass_le_delta` extends the
  prior-moment master event to a predeclared `Nat`-indexed catalog with
  nonnegative summable weights of total mass at most one. The event includes
  product-law null samples, which cost zero probability and make the real
  `tsum` component extraction sound on every good sample. A geometric-weight
  Boolean receipt proves one event controls every natural-number entry,
  evaluates the first two confidence shares as `4` and `8`, and separately
  exercises the null-sample guard. The downstream
  `countableJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem`
  theorem permits a `Nat` entry selected from the sample and a posterior on the
  finite hypothesis space, with the exact `xi / t` residual and one KL term.
  Its receipt is structural and existential in the good sample; it does not
  evaluate a selected numerical right-hand side below one. This layer remains
  fixed-sample and does not provide all-real optimization or a time-uniform
  process;
  [`CheckCountableJointMeanVariancePACBayes.lean`](./examples/CheckCountableJointMeanVariancePACBayes.lean),
  [`CountableJointMeanVariancePACBayes.lean`](./FormalSLT/PACBayes/CountableJointMeanVariancePACBayes.lean),
  [`CountableJointMeanVariancePosterior.lean`](./FormalSLT/PACBayes/CountableJointMeanVariancePosterior.lean)
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

- **Finite weighted hypothesis--tilt master e-process** —
  `pacBayesPriorTiltMixture_eProcess` mixes finite full-support hypothesis and
  tilt priors into one normalized e-process, and
  `timeUniformPACBayes_tiltMixture_allPosteriors_bound` uses one Ville crossing
  to control every positive time, posterior PMF, and declared tilt atom. The
  selected-atom endpoint permits a path- and posterior-dependent tilt choice
  and displays one hypothesis-posterior KL term plus
  `log (1 / (delta * weight j))`; it does not use a finite union bound or a
  second tilt KL. The generic theorem states an outer-mass bound and is not by
  itself an i.i.d. bounded-loss specialization, countable mixture, or all-real
  optimizer.
  The Boolean receipt uses distinct zero and Rademacher hypothesis processes,
  tilts `1/4` and `1/2`, and proves that the master exceeds one on the positive
  outcome;
  [`CheckTimeUniformTiltMixture.lean`](./examples/CheckTimeUniformTiltMixture.lean)
- **Finite-IID weighted-tilt specialization** —
  `timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec` supplies
  one measurable event of mass at most `delta` for measurable IID `[0,1]`
  losses, finite full-support hypothesis and tilt priors, and positive tilts
  below three. Outside it, every positive time, posterior PMF, and declared
  atom is valid; the selector corollary allows both posterior and atom to depend
  on the path. The Boolean receipt evaluates both possible boundaries at most
  `3/8` and proves existential, rather than named, good-path risk `< 7/8`;
  [`CheckTimeUniformIIDTiltMixture.lean`](./examples/CheckTimeUniformIIDTiltMixture.lean)
- **Forward hybrid-Bessel finite master** —
  `forwardBesselPACBayesMasterProcess_eProcess_of_bounded` mixes the actual
  predictable-residual e-process over finite hypothesis and tilt priors.
  `exists_forwardIIDBesselPACBayes_event` supplies the IID bounded-loss
  adapter and one outer-mass event valid for every `n >= 2`, posterior PMF, and
  declared atom. A selector may depend on the path, time, and posterior. The
  boundary contains one hypothesis KL term, the selected atom's log-weight
  penalty, and the posterior average of per-hypothesis hybrid Bessel penalties.
  The hybrid expression is a lower envelope, not an e-process. The fair-Boolean
  receipt checks the common-event structure; the biased-Boolean receipt at
  `n = 32` has Bessel variance `1/32`, `KL = log 2`, a theorem-produced good
  path, risk below `343/1000`, and a same-prefix empirical-Bernstein versus
  fixed-proxy comparison of approximately `0.312` versus `0.760`;
  [`CheckForwardBesselPACBayesIID.lean`](./examples/CheckForwardBesselPACBayesIID.lean),
  [`CheckForwardBesselPACBayesIIDInformative.lean`](./examples/CheckForwardBesselPACBayesIIDInformative.lean)
- **Continuous-prior arbitrary-state trajectory endpoint** —
  `exists_continuousForwardPredictableMeanBesselPACBayes_event` replaces the
  finite hypothesis sum by integration over an arbitrary measurable parameter
  space, and
  `exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event`
  derives its process obligations from a bounded score jointly strongly
  measurable in the hypothesis, complete prefix, and next state. The common
  outer event controls every `n >= 2`, eligible posterior measure, and atom of
  a finite predeclared tilt prior. The basic `Theta = Real`, `Z = Real` checker
  uses a two-atom kernel and proves positive conditional variance without
  evaluating the boundary;
  [`CheckContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean`](./examples/CheckContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean).
  The separate Gaussian/fair-Boolean receipt has posterior finite-set mass
  zero, `KL = 1/32`, positive observed Bessel variance on a theorem-produced
  good path in each of two mass-`1/4` sign-flip branches, and boundary
  `<= 489/1024 < 1/2`. It fixes the posterior and tilt and still uses a
  two-atom real-state law;
  [`CheckContinuousMeasurableTrajectoryGaussianWitness.lean`](./examples/CheckContinuousMeasurableTrajectoryGaussianWitness.lean)
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
- Use `FormalSLT.PACBayes.TimeUniformTiltMixture` when a finite, normalized,
  positive tilt prior should be mixed into one process before applying Ville.
  Its selector chooses one predeclared atom after observing the path and
  posterior. Use `FormalSLT.PACBayes.TimeUniformIIDTiltMixture` for the checked
  measurable-event adapter to finite-IID `[0,1]` losses.
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
- Use `FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt` for the direct
  square-root-plus-linear one-event theorem. Its `clog 2 n` dyadic catalog is
  predeclared; the posterior is data-dependent, and the variance is the
  posterior average of per-hypothesis Bessel empirical variances.
- Use `FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch` for one
  infinite-IID event shared by every sample size `n >= 2` and every posterior
  on a fixed finite hypothesis type. Use
  `FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch` for the
  corresponding researcher-facing endpoint over arbitrary measurable
  hypothesis spaces and admissible posterior measures. Use the reverse modules
  directly only when working with the finite-horizon exchangeable filtration
  or epoch-level proof chain.
- Use `FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes`
  for arbitrary-measurable-hypothesis forward predictable-residual PAC-Bayes
  when the parameterized processes satisfy the explicit ambient and filtered
  product-measurability interfaces. Use
  `FormalSLT.StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes`
  for its finite-state full-prefix adapter, which derives those interfaces
  from coordinatewise parameter measurability of the score. Use
  `FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes`
  for arbitrary measurable state and hypothesis spaces with one supplied joint
  score contract in the hypothesis, complete prefix, and next state.
- Use `FormalSLT.PACBayes.CountableJointMeanVariancePACBayes` for the
  support-aware fixed-sample `Nat`-indexed master event and per-entry prior
  moment extraction. Use
  `FormalSLT.PACBayes.CountableJointMeanVariancePosterior` for the downstream
  Donsker--Varadhan score, raw gap, exact-`xi` risk, and sample/posterior-
  dependent natural-index selector endpoints. The posterior remains a PMF on
  the finite hypothesis type.
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
- **PAC-Bayes:** `PACBayesKL`, `PACBayes.FinitePMFBridge`, `PACBayesMcAllester`,
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
  `PACBayes.FiniteEmpiricalBernsteinSqrt`,
  `PACBayes.FiniteEmpiricalVarianceReverse`,
  `PACBayes.FiniteEmpiricalVarianceReverseEpoch`,
  `PACBayes.FiniteEmpiricalVarianceReverseExponential`,
  `PACBayes.FiniteEmpiricalVarianceReverseMartingale`,
  `PACBayes.FiniteEmpiricalVarianceReverseMaximal`,
  `PACBayes.FiniteEmpiricalVarianceReversePACBayes`,
  `PACBayes.FiniteJointMeanVarianceReverse`,
  `PACBayes.FiniteJointMeanVarianceReversePACBayes`,
  `PACBayes.FiniteJointMeanVarianceReverseCatalog`,
  `PACBayes.FiniteEmpiricalBernsteinReverseSqrt`,
  `PACBayes.ContinuousJointMeanVarianceReversePACBayes`,
  `PACBayes.ContinuousJointMeanVarianceReverseCatalog`,
  `PACBayes.ContinuousEmpiricalBernsteinReverseSqrt`,
  `PACBayes.FiniteProductMeasureBridge`,
  `PACBayes.InfiniteProductMeasureBridge`,
  `PACBayes.InfiniteEmpiricalBernsteinStitch`,
  `PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch`,
  `PACBayes.CountableJointMeanVariancePACBayes`,
  `PACBayes.CountableJointMeanVariancePosterior`,
  `PACBayes.GaussianMeasureKL`, `PACBayes.TimeUniformPACBayes`,
  `PACBayes.TimeUniformScorePACBayes`,
  `PACBayes.TimeUniformTiltMixture`,
  `PACBayes.TimeUniformIIDTiltMixture`,
  `PACBayes.ForwardBesselPACBayes`,
  `PACBayes.ForwardBesselPACBayesCountable`,
  `PACBayes.ForwardBesselPACBayesIID`,
  `PACBayes.ContinuousForwardPredictableMeanBesselPACBayes`,
  `PACBayes.TimeUniformContinuousPACBayes`,
  `PACBayes.TimeUniformGaussianPACBayes`, `PACBayes.TimeUniformIID`,
  `PACBayes.TimeUniformIIDGrid`, `PACBayes.IIDContinuousGaussian`,
  `PACBayes.IIDContinuousGaussianGrid`
- **Stochastic dynamics:** finite and measurable-state trajectory semantics;
  finite, countable-tilt, and continuous-prior trajectory PAC-Bayes; homogeneous Markov
  certificates with deterministic or supplied finite-state initial law;
  stationary Poisson construction, depth selection, robustness, transition
  confidence, invariant existence, and empirical candidate catalogs; and
  controlled semantics, stationary target-policy OPE, dynamic comparators,
  and finite-horizon target-path change of measure. These modules are
  re-exported by `FormalSLT.StochasticDynamics`; exact names and endpoints are
  listed in [`docs/theorem-map.md`](./docs/theorem-map.md).

## Scope and open boundaries

Many foundational learning-theory results are deliberately finite, and every
public theorem keeps its finite or measurable-space scope explicit.

### Assumptions

- **Hypothesis classes:** finite index types unless a theorem states a finite
  net, the process-level continuous PAC-Bayes interface, or the all-sample-size
  continuous empirical-Bernstein endpoint over an arbitrary measurable
  hypothesis space
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
  posterior-dependent selection. The finite joint master-mixture mass theorem uses
  nonnegative catalog weights with total at most one and `0 < delta`; its
  entrywise posterior bounds require every catalog weight to be strictly
  positive and the prior to have full support. The countable master-mixture
  foundation instead requires nonnegative summable weights with `tsum` at most
  one for its mass theorem, together with `0 < delta`; its component theorem
  requires positive weights. The downstream conditional posterior endpoints
  assume a full-support finite prior, a finite posterior PMF, and a supplied
  sample outside the shared event. The single-entry exact-`xi` theorem requires
  the selected tilt to be positive, while the arbitrary selector theorem
  requires every catalog tilt to be positive. The closed-form dyadic endpoint
  assumes `0 < delta < 1`, fixes the finite hypothesis catalog and full-support
  prior before the sample, and uses the predeclared depth `Nat.clog 2 n`. The
  finite all-sample-size endpoint additionally places the samples on the
  infinite IID product space and uses the same fixed finite hypothesis type and
  full-support prior for every `n >= 2`. Its continuous-prior extension requires
  a finite measurable-singleton observation type, an arbitrary measurable
  hypothesis space, strongly measurable bounded loss sections, a fixed
  probability prior, and posterior probability measures absolutely continuous
  with respect to that prior with integrable log-likelihood ratio.
- **Time-uniform PAC-Bayes:** finite-class and finite-dimensional
  spherical-Gaussian i.i.d. bounded-loss theorems at discrete sample times;
  process-level for a fully arbitrary measurable hypothesis space. The finite
  weighted tilt-master theorem instead assumes finite nonempty hypothesis and
  tilt types, full-support normalized priors, adapted centered bounded
  increments with a common conditional second-moment proxy, and declared
  tilts satisfying `0 < lambda_j` and `b * lambda_j < 3`. Its finite-IID
  adapter assumes measurable `[0,1]` losses, measurable IID sample coordinates,
  and specializes that tilt condition to `lambda_j < 3`.
- **Forward-Bessel PAC-Bayes:** the finite master assumes finite nonempty
  hypothesis and tilt types, full-support normalized priors, adapted `[0,1]`
  increments with fixed conditional means, and predeclared atoms
  `0 < lambda_j < 1`; its IID adapter derives these obligations from strongly
  measurable `[0,1]` losses and an IID stream. The continuous-prior master
  permits an arbitrary measurable hypothesis space, a fixed probability prior,
  and every posterior probability measure absolutely continuous with respect
  to it with integrable log-likelihood ratio. It retains a finite predeclared
  tilt type and explicit parameter/process measurability assumptions. The
  hybrid Bessel minimum is taken per hypothesis before posterior averaging.
- **Finite prefix-dependent trajectory PAC-Bayes:** finite state space,
  deterministic initial state, arbitrary prefix-dependent probability kernels,
  and a finite catalog of bounded scores declared before the trajectory. A
  score may encode a fixed-in-advance online update rule whose prediction uses
  the observed prefix but not the next state. One measurable event is
  simultaneous over all positive times, posterior PMFs, and atoms
  `0 < lambda_j < 3` of a full-support finite tilt prior. This does not validate
  creating new catalog members after observing their scored outcomes.
- **Continuous-hypothesis arbitrary-state trajectory PAC-Bayes:** arbitrary
  measurable state and hypothesis spaces, deterministic start, arbitrary
  full-prefix Markov kernels, a finite predeclared positive tilt prior, and a
  bounded score jointly strongly measurable in the hypothesis, complete
  prefix, and next state. The common event is uniform over every admissible
  posterior measure, but the theorem does not construct a measurable posterior
  selector or selected process and does not learn the score family from the
  scored path. The numerical Gaussian/fair-Boolean receipt fixes its posterior
  and tilt and uses a two-atom Rademacher transition law on `Real`; it is not an
  atomless-dynamics receipt or a matched boundary comparison.
- **Finite Markov prequential risk:** finite state space, transition PMFs,
  an arbitrary supplied finite-state initial PMF, and a fixed `[0,1]`
  observable and finite catalog of fixed `[0,1]`-valued predictors with a
  full-support prior; the PAC-Bayes endpoint is simultaneous over every
  positive time, posterior, and atom `0 < λ_j < 3` of a full-support finite
  tilt prior declared before the trajectory. The initial PMF need not have
  full support. A pointwise post-path selector may choose one atom but need not
  be measurable or adapted and adds no optional-stopping guarantee. The target
  is posterior-average one-step conditional squared risk along the realized
  path
- **Supplied-Poisson stationary risk:** finite state and hypothesis types;
  deterministic initial state; supplied invariant PMF; supplied bounded exact
  or approximate Poisson potentials, or finite-depth potentials constructed
  from a known kernel and an explicit oscillation contraction. The base lane
  uses finite declared tilts in `(0,1)`; the depth-selection lane allocates over
  all finite depths and a fixed countable geometric tilt catalog. The
  Dobrushin specialization computes
  the contraction factor from pairwise row total variation. The robust
  specialization instead fixes a candidate kernel, a supplied rowwise
  probabilists' TV radius, a supplied invariant PMF of the true kernel, and a
  fixed reference PMF and depth for candidate-potential construction. The
  event is an outer-mass package shared by every `n >= 2`, posterior PMF, and
  declared tilt atom
- **Empirical transition confidence:** finite homogeneous kernel, deterministic
  initial state, and finite state and tilt types. One outer-mass event controls
  every transition coordinate and time `n >= 2`. Normalized row certificates
  require positive visit counts; the uniform kernel certificate requires every
  row to be visited. A candidate kernel may be selected from the observed path
  because it is quantified inside the common coordinate event
- **Empirical stationary catalog:** finite homogeneous kernel, deterministic
  initial state, finite predeclared candidate and hypothesis catalogs, a finite
  transition-tilt type, and the countable geometric risk-tilt allocation. One
  outer-mass event of cost `deltaRisk + deltaTransition` uses the same path for
  risk and transition confidence. Candidate, depth, both tilts, and posterior
  may be selected from that path, but every normalized source row must have
  positive visit mass. The target is the chosen finite invariant PMF; strict
  candidate contraction is required for uniqueness
- **Controlled trajectory semantics:** finite state, action, and target-policy
  catalog types; deterministic initial decision--state pair; full-history
  behavior and target policies; homogeneous controlled environment; bounded
  one-step transition scores; overlap; and a supplied common importance-ratio
  cap. The result identifies the behavior-law predictable mean, not target-law
  occupancy or stationary target value
- **Stationary target-policy OPE:** finite state, action, target-policy, and
  tilt types; known homogeneous environment and behavior propensities;
  state-Markov target policies; supplied invariant PMFs and exact bounded
  Poisson potentials; overlap; a common action-ratio cap; and finite declared
  tilts in `(0,1)`. The event is uniform over `n >= 2`, posterior PMFs, and
  declared tilt atoms under the behavior path law
- **Dynamic target-policy comparators:** finite state, action, target-policy,
  and tilt types; known homogeneous or prefix/time-dependent environment;
  history-dependent behavior and target policies; bounded transition scores;
  overlap; a common action-ratio cap; and finite declared tilts in `(0,1)`.
  The controlled risk is evaluated at behavior-realized prefixes
- **Target-path change of measure:** finite state and action types;
  deterministic initial decision--state pair; known prefix/time-dependent
  environment; supplied history-dependent behavior and target policies; and
  overlap. The exact identity is finite-horizon; a supplied ratio cap yields
  only the worst-case cumulative range `C ^ n`
- **Chaining:** finite nets, images, supports, outcome spaces, and entropy sums
- **Public axiom profile:** `[propext, Classical.choice, Quot.sound]`

### Not yet proved

- A general probability-space Dudley theorem that constructs arbitrary
  measurable suprema and the required separability/chaining interface
- An infinite-class confidence sequence
- A countable continuous-prior or arbitrary-state forward tilt master,
  predictable tilt family, all-real tilt optimizer, or vanishing *optimized*
  all-time hybrid-Bessel boundary. The finite-hypothesis normalized countable
  master and the finite-state trajectory geometric selector with boundary
  tending to zero are checked separately. The latter uses countable confidence
  allocation rather than a selected countable master e-process. In every case,
  the hybrid Bessel expression is only a lower envelope of the actual
  predictable-residual e-process, not a separately proved e-process.
- Catalog members created after their scored outcomes, arbitrary path-fitted
  Poisson candidates outside the finite predeclared catalog, normalized
  confidence for unvisited rows, random starts for general prefix-dependent,
  measurable-state, or controlled trajectories, continuous-state stationary
  risk, quantitative mixing, learned controlled nuisances, and an anytime-valid
  cumulative-weight target-policy value theorem. Fixed-in-advance online rules,
  arbitrary measurable state and hypothesis spaces with deterministic start,
  supplied finite-state initial PMFs for the homogeneous Markov endpoint,
  finite invariant-law existence, and fixed-horizon target-path identities are
  checked separately under their stated assumptions.
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
make examples
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

- the root build, recursive example sweep, and tutorials finish successfully;
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
- [x] Lift the checked countable fixed-sample master event to finite-posterior
  and exact piecewise-`xi` natural-index selector endpoints
- [x] Mix a normalized `Nat`-indexed forward tilt catalog into a
  finite-hypothesis master e-process with exact atom costs and post-path
  selection
- [x] Add a finite-state full-prefix countable-allocation endpoint whose
  explicit geometric selected boundary tends to zero
- [x] Mix a finite, normalized hypothesis--tilt catalog into one generic
  sub-Gamma e-process with post-path atom selection
- [x] Specialize the finite hypothesis--tilt master to measurable IID `[0,1]`
  losses with one measurable exceptional event and a selected-atom endpoint
- [x] Extend the fixed-sample joint mean/Bessel-variance score through reverse
  dyadic epochs and countable stitching to one all-sample-size finite-IID event
- [x] Extend the all-sample-size empirical-Bernstein result to general
  measurable hypothesis spaces with finite-valued observations
- [x] Convert the predictable-residual empirical-Bernstein e-process to a
  checked hybrid Bessel lower envelope, mix finite hypothesis and tilt priors,
  and supply the finite-IID all-posterior selected-atom adapter
- [x] Extend the forward predictable-residual master to arbitrary measurable
  hypothesis and state spaces through a supplied jointly measurable full-prefix
  score family, with a fixed-posterior Gaussian/Rademacher numerical receipt
- [ ] Extend countable forward control to continuous priors and arbitrary
  states; add predictable or all-real tilt control, a vanishing optimized
  boundary, broader random-start support, atomless transition receipts, and
  matched comparisons
- [ ] Extend end-to-end i.i.d. bounded-loss PAC-Bayes beyond finite-dimensional
  spherical Gaussian priors and posteriors
- [x] Extend the finite PAC-Bayes certificate to a predeclared catalog of
  prefix-dependent scores, including fixed-in-advance online update rules
- [x] Add a finite stationary-risk bridge from a supplied invariant PMF and
  supplied bounded exact or approximate Poisson potentials
- [x] Construct finite-depth Poisson potentials and their span and residual
  bounds from explicit kernel-contraction data
- [x] Confidence-allocate over every finite Poisson depth and the countable
  geometric tilt catalog, with post-path selection and a vanishing
  logarithmic-depth stationary boundary
- [x] Transfer stationary certificates from a fixed candidate kernel under a
  deterministic row-TV envelope and certify uniqueness among supplied
  invariant PMFs under strict candidate contraction
- [x] Add time-uniform empirical transition-coordinate bands, visited-row TV
  certificates, and post-data candidate plug-in contraction for unknown finite
  kernels
- [x] Confidence-allocate a finite predeclared candidate--depth catalog with
  same-path risk and transition confidence, and permit post-path candidate,
  depth, tilt, and posterior substitution
- [x] Construct an invariant PMF for every nonempty finite kernel and upgrade
  it to uniqueness under strict Dobrushin or candidate row-TV contraction
- [x] Extend the finite homogeneous-Markov weighted-tilt certificate to an
  arbitrary supplied finite-state initial PMF
- [ ] Extend random starts to prefix-dependent, measurable-state, and
  controlled endpoints; add auxiliary-data catalog construction, countable
  tilts for continuous-prior and arbitrary-state layers, and predictable tilt
  families

## Dependencies

- [Lean 4](https://lean-lang.org/) v4.32.2
- [Mathlib4](https://github.com/leanprover-community/mathlib4) @ `905b9581`

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
