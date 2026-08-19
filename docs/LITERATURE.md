# Literature and theorem-fidelity ledger

This ledger separates established statistical results from FormalSLT's checked
specializations and derived finite-sample endpoints. The Lean declaration and
its hypotheses are authoritative. No row makes a broad priority claim.

- **REPRODUCTION**: the formal statement matches a named source theorem or
  load-bearing source equation after an explicit notation translation.
- **SPECIALIZATION**: FormalSLT discharges abstract source assumptions in a
  narrower concrete model.
- **DERIVED VARIANT**: the endpoint uses established ingredients but is not a
  literal restatement of the cited theorem.
- **CANDIDATE NEW**: reserved for a versioned prior-art search plus external
  review. No flagship currently uses this label.

## Flagship matrix

| Flagship result | FormalSLT endpoint | Primary source | Classification | Exact agreement | Material differences and nonclaims | Checked receipt | Next evidence |
|---|---|---|---|---|---|---|---|
| All-sample-size empirical-Bernstein PAC-Bayes over measurable hypotheses | `PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event`; finite-hypothesis specialization: `PACBayes.InfiniteEmpiricalBernsteinStitch.exists_infiniteEmpiricalBernstein_event`; finite-epoch continuous endpoint: `PACBayes.ContinuousEmpiricalBernsteinReverseSqrt.continuousEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem`; load-bearing source MGF: `PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` | Tolstikhin and Seldin, [PAC-Bayes-Empirical-Bernstein Inequality](https://proceedings.neurips.cc/paper/2013/file/a97da629b098b75c294dffdc3e463904-Paper.pdf), especially Eq. (9); compare the established anytime PAC-Bayes frameworks of Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), especially Corollary 27 and Appendix A.11, and Jang, Jun, Kuzborskij, and Orabona, [Tighter PAC-Bayes Bounds through Coin-Betting](https://proceedings.mlr.press/v195/jang23a/jang23a.pdf), Corollary 4 (Proposition 4 in the arXiv version) | **SPECIALIZATION** for the finite-IID Bessel-MGF foundation; **DERIVED VARIANT** for the continuous-prior reverse mixture, dyadic stitching, and final all-sample-size endpoint | Finite-valued IID observations; arbitrary measurable hypothesis space; strongly measurable `[0,1]` loss sections; one fixed probability prior; every posterior probability measure absolutely continuous with respect to that prior with integrable log-likelihood ratio; posterior integral of per-hypothesis Bessel variances; one measure-theoretic KL term; one posterior-independent measurable event valid for every `n >= 2` and every admissible posterior | The observation space remains finite. The displayed constants are `5/2` on `sqrt(Vhat * L / n)` and `5` on `L/n`, with `L = KL + log(r(r+1)^2/delta)` and `r = Nat.log 2 n`. The construction is an offline reverse-exchangeability/reverse-epoch theorem, not a literal reproduction of a cited paper theorem, a forward e-process, an optional-stopping theorem, an all-real optimizer, or a continuous-observation result. Pointwise posterior substitution does not add a measurable-selection or optional-stopping claim. No novelty or priority claim is made | `CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.gaussianPosterior_nonVacuous_receipt`: `Theta = (Fin 1 -> Real) x Bool`, an `N(0,1)` product fair-Boolean prior, and a fixed `N(1/4,1)` product fair-Boolean posterior with no point masses and every finite set of posterior mass zero; `KL = 1/32`; an unscaled zero-one sign-flip mismatch loss depending on both coordinates and attaining both endpoints; posterior empirical risk `1/2` for every nonempty sample; and, at `n = 2^20` and `delta = 1/2`, correction below `1/2` and theorem-produced right-hand side below `1`. `gaussianPosterior_goodPath_exists` proves that at least one path lies outside the exceptional event. This receipt fixes the posterior and does not exercise data-dependent continuous-posterior selection. The finite fair-Boolean all-`n` receipt separately checks a path-selected finite posterior | Publish the symbol-by-symbol source-to-Lean derivation and matched numerical comparison with the closest CWR and Jang routes; obtain PAC-Bayes and Lean probability reviews |
| Fixed-sample empirical-Bernstein PAC-Bayes foundation | `PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta` and `finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem`; load-bearing MGF: `PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` | Tolstikhin and Seldin, [PAC-Bayes-Empirical-Bernstein Inequality](https://proceedings.neurips.cc/paper/2013/file/a97da629b098b75c294dffdc3e463904-Paper.pdf), especially Eq. (9) and Theorems 3--4 | **SPECIALIZATION** of Eq. (9) with the same constants on finite IID outcome spaces; **DERIVED VARIANT** for the one-event logarithmic-grid endpoint | IID `[0,1]` losses; Bessel empirical variance averaged per hypothesis; posterior selected after the sample; one KL term; empirical risk and empirical variance in the final checked bound | Finite data and hypothesis types; fixed full-support prior; predeclared dyadic scale grid through `Nat.clog 2 n`; constants `5/4` and `5/2`. This is not a literal formalization of Tolstikhin--Seldin Theorem 4 or an all-real optimizer; the separate reverse-epoch lane supplies the all-sample-size endpoint | `CheckFiniteEmpiricalBernsteinSqrt.balanced64_positiveKL_positiveVariance_nonvacuous`, `balanced64_not_mem_sqrtBadSamples`, and `balanced64Ceiling_lt_ninetyNineHundredths`: `n = 64`, `delta = 1/20`, `KL = log 2`, `Vhat = 16/63`, explicit positive-mass good sample, ceiling `< 99/100` | Compare numerically against Tolstikhin--Seldin Theorem 4 and standard PAC-Bayes-kl/Hoeffding/Bernstein baselines on identical inputs; obtain an external constants and assumptions review |
| Time-uniform finite-IID PAC-Bayes | `PACBayes.TimeUniformIID.timeUniformIIDPACBayes_allPosteriors_bound`; generic engine: `PACBayes.TimeUniform.timeUniformPACBayes_allPosteriors_bound` | Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), especially the master theorem and sub-psi corollaries; compare Jang, Jun, Kuzborskij, and Orabona, [Tighter PAC-Bayes Bounds through Coin-Betting](https://proceedings.mlr.press/v195/jang23a/jang23a.pdf) | **SPECIALIZATION** of the established anytime PAC-Bayes recipe | One common event; every positive time and posterior PMF; fixed data-free prior; KL plus `log(1/delta)`; prior mixture, change of measure, and Ville route | Finite hypotheses and `[0,1]` IID losses. The main displayed endpoint uses a fixed declared tilt; finite-grid selection is separate. It is narrower than general measurable parameter spaces, predictable tilt sequences, and the source papers' broader stochastic-process settings | `CheckTimeUniformIIDPACBayes.lean` checks the IID adapter; the generic Rademacher receipt checks a nonconstant process | Add a positive-KL finite-IID numerical receipt whose final boundary is below one; benchmark fixed/grid tilts against stitched or log-log boundaries |
| Forward hybrid-Bessel PAC-Bayes | `AnytimeValid.ForwardBesselProcess.exists_forwardEmpiricalBernsteinLowerTiltCatalog_event`; finite-hypothesis master: `PACBayes.ForwardBesselPACBayes.exists_forwardBesselPACBayes_event`; continuous-prior master: `PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.exists_continuousForwardPredictableMeanBesselPACBayes_event`; arbitrary-state capstone: `StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event`; IID endpoint: `PACBayes.ForwardBesselPACBayesIID.exists_forwardIIDBesselPACBayes_event` | Howard, Ramdas, McAuliffe, and Sekhon, [Time-uniform, nonparametric, nonasymptotic confidence sequences](https://doi.org/10.1214/20-AOS1991), for predictable empirical-Bernstein processes; Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), for the PAC-Bayes mixture and Ville route | **SPECIALIZATION** of the known predictable-residual e-process; **DERIVED VARIANT** for the checked hybrid Bessel lower-envelope conversion, finite hypothesis--tilt master, continuous-prior integration, and arbitrary-state trajectory adapter | Bounded adapted increments with fixed conditional means; two checked Bessel upper envelopes for the predictable quadratic penalty and their per-hypothesis minimum; one actual e-process mixed over finite full-support hypothesis and tilt priors or integrated over an arbitrary measurable hypothesis prior; one outer-mass event valid for every `n >= 2`, eligible posterior, and declared atom; one hypothesis KL plus the selected atom's `log (1 / (delta * weight j))` penalty; IID bounded-loss adapter; deterministic-start arbitrary-state adapter under one supplied jointly measurable score | The hybrid Bessel expression is only a lower envelope of the actual predictable-residual e-process and is not itself proved to be an e-process. The tilt catalog remains finite and does not provide a vanishing optimized all-time boundary. The continuous-prior event is posterior-uniform but does not construct a measurable selector or selected process. The arbitrary-state adapter retains a deterministic start and does not supply a random initial law, atomless-dynamics receipt, or matched boundary comparison. No novelty or priority claim is made | The fair-Boolean checker is a structural common-event receipt. The separate finite-IID `CheckForwardBesselPACBayesIIDInformative.informative_nonvacuous_receipt` uses a biased Boolean stream at `n = 32`, has Bessel variance `1/32` and `KL = log 2`, proves a good prefix cylinder has mass above `delta = 1/160`, certifies risk below `343/1000`, and checks the same-prefix empirical-Bernstein versus fixed-proxy boundaries at approximately `0.312` versus `0.760`. The basic arbitrary-state `Real` checker instead uses a two-atom transition law and proves positive conditional variance without evaluating the PAC-Bayes boundary | Compare finite and continuous-prior catalogs against optimized or stitched empirical-Bernstein boundaries; add an atomless arbitrary-state receipt and matched comparison; obtain PAC-Bayes and Lean probability reviews |
| Finite Markov prequential PAC-Bayes | `StochasticDynamics.markovPACBayes_tiltMixture_prequentialRisk_certificate`; path identities include `pathSquaredLoss_condExp`, `markovRiskInnovation_condExp_eq_zero`, and `markovRiskInnovation_condSecondMoment_le_one_fourth` | Chugg, Wang, and Ramdas, master theorem and Bernstein-condition corollary; compare Karagulyan and Alquier, [Empirical PAC-Bayes Bounds for Markov Chains](https://openreview.net/forum?id=GlAeeN1Lhp) | **SPECIALIZATION** of established anytime martingale PAC-Bayes machinery; not a reproduction of the stationary-risk Markov theorem | One event of mass at most `delta`; every positive time, posterior over a fixed finite predictor catalog, and atom of a predeclared full-support finite tilt prior; exact transition path law; exact `log (1 / (delta * weight j))` atom penalty; derived conditional centering and universal `1/4` second-moment proxy | Controls the trajectory average of encountered one-step conditional risks, not stationary risk. Assumes finite state, deterministic start, fixed bounded observable and base predictors, and `0 < lambda_j < 3`. A pointwise selector may choose one atom after the path but need not be measurable or adapted and adds no optional-stopping guarantee. No joint predictor--tilt posterior, countable or all-real tilt optimization, empirical variance, mixing, stationarity, same-trajectory training, random initial law, or continuous state | `CheckMarkovPACBayes.asymmetricBool_adaptivePosteriorTiltMarkovPACBayes_certificate`: asymmetric two-state chain, path-selected posterior and tilt atom, exact `KL = log 2`, both selected boundaries `< 1/20`, and conditional risk `< 11/20` outside an event of mass at most `1/20`; explicit selector-branch paths are not proved good or positive-probability | Add a supplied random initial law and normalized countable or predictable tilt families; obtain an external assumptions/constants review and keep prequential conditional risk distinct from stationary risk |

An earlier all-times PAC-Bayes-Bernstein martingale comparator is Seldin,
Cesa-Bianchi, Auer, Laviolette, and Shawe-Taylor,
[PAC-Bayes-Bernstein Inequality for Martingales and its Application to Multiarmed Bandits](https://proceedings.mlr.press/v26/seldin12a.html).

## Reviewer dossier required for each flagship

A result is not promoted to a stronger literature or novelty classification
until every applicable item is closed.

### Version and replay

- [ ] Pin the exact FormalSLT commit, Lean version, Mathlib revision, and theorem
  fully qualified names.
- [ ] Link the theorem-facing checker and archive its `#print axioms` output.
- [ ] Re-run cache fetch, root build, every example and tutorial, proof-debt,
  custom-axiom, fidelity, orphan, witness, documentation, and whitespace gates
  on that exact commit.
- [ ] Archive the exact source PDFs used for comparison.

### Source fidelity

- [ ] Record source theorem, equation, and PDF page, with a symbol-by-symbol
  dictionary from paper notation to Lean definitions.
- [ ] Compare every quantifier: fixed versus all time, fixed versus all
  posterior, finite versus general hypothesis space, and fixed versus selected
  tilt.
- [ ] Compare strict and non-strict inequalities and ordinary probability
  events versus outer-mass control.
- [ ] Normalize constants independently before calling two statements equal.
- [ ] Keep the result labeled `REPRODUCTION`, `SPECIALIZATION`, or
  `DERIVED VARIANT` unless a versioned prior-art search and external review
  justify more.

### Hidden-assumption attack

- [ ] Trace every endpoint hypothesis down to the primitive probability
  argument; identify any supplied MGF, residual, boundary, measurability, or
  exceptional-set assumption that could contain the hard theorem.
- [ ] Verify when the prior, posterior, catalog, selector, tilt, predictor, and
  sample are chosen.
- [ ] Verify IID, independence, Markov, stationarity, mixing, support, and
  initial-law assumptions.
- [ ] Verify that empirical variance means the posterior average of each
  hypothesis's Bessel variance, not the variance of posterior-averaged loss.
- [ ] Audit confidence allocation and count the KL terms in the final common
  event.

### Numerical usefulness

- [ ] Supply a positive-KL, nonconstant-loss, positive-variance example whose
  final bound is below the trivial loss range.
- [ ] Recompute every displayed quantity independently from the witness data.
- [ ] Compare against the closest source theorem and common baselines using the
  same `n`, `delta`, prior, posterior, and data.
- [ ] Publish the nonvacuity region and sensitivity to catalog weights and
  tilts, not only one favorable point.

### External review

- [ ] Ask a PAC-Bayes expert whether the source match, classification, and
  constants are correct.
- [ ] Ask a Lean probability expert whether any hypothesis or measurability
  boundary trivializes the endpoint.
- [ ] Ask a potential user whether they would cite or use the theorem and which
  precise extension matters next.
- [ ] Record reviewer, date, commit, objection, and resolution. Unresolved
  objections remain visible.

## Result-specific attack points

- **Empirical-Bernstein:** audit `finiteJointMeanVarianceKappa`, the rational
  balance proof, the predeclared grids and weights, the reverse Bessel
  conditional-expectation identity, reverse filtration and maximal-inequality
  direction, prefix/infinite-product measure bridge, telescoping epoch budget,
  and the pairing of each mass theorem with its conditional posterior endpoint.
  Keep the all-sample-size result classified as a derived variant; do not call
  either endpoint Tolstikhin--Seldin Theorem 4, a forward e-process, or an
  optional-stopping theorem.
- **Time-uniform IID:** audit the coordinate convention, full-support finite
  prior, fixed tilt, failure-set semantics, and the missing dedicated numerical
  IID receipt.
- **Forward hybrid-Bessel:** audit the predictable-residual e-process separately
  from its deterministic hybrid Bessel lower envelope, the two envelope
  constants, the per-hypothesis minimum before posterior averaging, the single
  KL term, and the selected atom's log-weight charge. Keep the structural good-
  path receipt separate from a numerical-width claim, and do not attach novelty
  or priority language without independent prior-art review.
- **Markov prequential:** audit the Ionescu--Tulcea path law, deterministic
  initial state, fixed predictor catalog, full-support finite tilt prior,
  post-path atom-selection semantics, conditional-risk identity, conditional
  centering, and the `1/4` second-moment step. Keep the pointwise selector
  separate from optional stopping, and keep encountered conditional
  prequential risk separate from stationary risk.
