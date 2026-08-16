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
| Finite empirical-Bernstein PAC-Bayes | `PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta` and `finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem`; load-bearing MGF: `PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` | Tolstikhin and Seldin, [PAC-Bayes-Empirical-Bernstein Inequality](https://proceedings.neurips.cc/paper/2013/file/a97da629b098b75c294dffdc3e463904-Paper.pdf), especially Eq. (9) and Theorems 3--4 | **SPECIALIZATION** of Eq. (9) with the same constants on finite IID outcome spaces; **DERIVED VARIANT** for the one-event logarithmic-grid endpoint | IID `[0,1]` losses; Bessel empirical variance averaged per hypothesis; posterior selected after the sample; one KL term; empirical risk and empirical variance in the final checked bound | Finite data and hypothesis types; fixed full-support prior; predeclared dyadic scale grid through `Nat.clog 2 n`; constants `5/4` and `5/2`. This is not a literal formalization of Tolstikhin--Seldin Theorem 4, an all-real optimizer, or a time-uniform result | `CheckFiniteEmpiricalBernsteinSqrt.balanced64_positiveKL_positiveVariance_nonvacuous`, `balanced64_not_mem_sqrtBadSamples`, and `balanced64Ceiling_lt_ninetyNineHundredths`: `n = 64`, `delta = 1/20`, `KL = log 2`, `Vhat = 16/63`, explicit positive-mass good sample, ceiling `< 99/100` | Compare numerically against Tolstikhin--Seldin Theorem 4 and standard PAC-Bayes-kl/Hoeffding/Bernstein baselines on identical inputs; obtain an external constants and assumptions review |
| Time-uniform finite-IID PAC-Bayes | `PACBayes.TimeUniformIID.timeUniformIIDPACBayes_allPosteriors_bound`; generic engine: `PACBayes.TimeUniform.timeUniformPACBayes_allPosteriors_bound` | Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), especially the master theorem and sub-psi corollaries; compare Jang, Jun, Kuzborskij, and Orabona, [Tighter PAC-Bayes Bounds through Coin-Betting](https://proceedings.mlr.press/v195/jang23a/jang23a.pdf) | **SPECIALIZATION** of the established anytime PAC-Bayes recipe | One common event; every positive time and posterior PMF; fixed data-free prior; KL plus `log(1/delta)`; prior mixture, change of measure, and Ville route | Finite hypotheses and `[0,1]` IID losses. The main displayed endpoint uses a fixed declared tilt; finite-grid selection is separate. It is narrower than general measurable parameter spaces, predictable tilt sequences, and the source papers' broader stochastic-process settings | `CheckTimeUniformIIDPACBayes.lean` checks the IID adapter; the generic Rademacher receipt checks a nonconstant process | Add a positive-KL finite-IID numerical receipt whose final boundary is below one; benchmark fixed/grid tilts against stitched or log-log boundaries |
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
  balance proof, the predeclared grid and weights, and the pairing of the mass
  theorem with the conditional posterior endpoint. Do not call the result
  Tolstikhin--Seldin Theorem 4.
- **Time-uniform IID:** audit the coordinate convention, full-support finite
  prior, fixed tilt, failure-set semantics, and the missing dedicated numerical
  IID receipt.
- **Markov prequential:** audit the Ionescu--Tulcea path law, deterministic
  initial state, fixed predictor catalog, full-support finite tilt prior,
  post-path atom-selection semantics, conditional-risk identity, conditional
  centering, and the `1/4` second-moment step. Keep the pointwise selector
  separate from optional stopping, and keep encountered conditional
  prequential risk separate from stationary risk.
