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
| All-sample-size empirical-Bernstein PAC-Bayes over measurable hypotheses | `PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event` (`FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean:332`); finite-hypothesis specialization: `PACBayes.InfiniteEmpiricalBernsteinStitch.exists_infiniteEmpiricalBernstein_event`; finite-epoch continuous endpoint: `PACBayes.ContinuousEmpiricalBernsteinReverseSqrt.continuousEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem`; load-bearing source MGF: `PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` | Tolstikhin and Seldin, [PAC-Bayes-Empirical-Bernstein Inequality](https://proceedings.neurips.cc/paper/2013/file/a97da629b098b75c294dffdc3e463904-Paper.pdf), Eq. (9) and Theorems 3--4; Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), Corollary 27 and Appendix A.11; Jang, Jun, Kuzborskij, and Orabona, [Tighter PAC-Bayes Bounds through Coin-Betting](https://proceedings.mlr.press/v195/jang23a/jang23a.pdf), Theorem 1 and Corollary 4 | **SPECIALIZATION** only for the finite-outcome IID Bessel-variance MGF from Tolstikhin--Seldin Eq. (9), with the same `n^2 / (2(n-1))` coefficient; **DERIVED VARIANT** for the continuous-prior reverse mixture, reverse-epoch stitching, and final all-sample-size endpoint | Finite-valued IID observations; arbitrary measurable hypothesis space; strongly measurable `[0,1]` loss sections; one fixed probability prior; one measurable posterior-independent event; every `n >= 2`; every probability posterior absolutely continuous with respect to the prior and with integrable log-likelihood ratio; posterior average of per-hypothesis Bessel variances; one measure-theoretic KL term; final constants `5/2` and `5`, with `L = KL + log(r(r+1)^2/delta)` and `r = Nat.log 2 n` | Tolstikhin--Seldin Theorems 3--4 are fixed-`n` and combine two PAC-Bayes steps with different tuning and constants; the final FormalSLT theorem is not their Theorem 4. CWR Corollary 27 controls a posterior average of a population-minus-empirical variance term, retains population variance on the right, and uses its own epoch index and iterated-log charge. Jang Corollary 4 is all-time and allows posterior kernels and arbitrary measurable observations, but uses a biased `1/n` variance and a different nonlinear Gamma-regret boundary. FormalSLT is an offline reverse-stitch theorem, not a forward e-process, optional-stopping theorem, all-real optimizer, continuous-observation theorem, or measurable posterior-selector construction. No novelty or priority claim is made | `CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.gaussianPosterior_nonVacuous_receipt` uses `Theta = (Fin 1 -> Real) x Bool`, a standard-Gaussian/fair-Boolean prior, a fixed mean-shifted Gaussian posterior with no point masses, `KL = 1/32`, and an endpoint-attaining mismatch loss; at `n = 2^20` and `delta = 1/2`, the theorem-produced right-hand side is below one. `gaussianPosterior_goodPath_exists` supplies a path outside the exceptional event. This fixes the posterior and does not exercise data-dependent continuous-posterior selection. The finite fair-Boolean receipt separately checks a path-selected finite posterior | Publish the symbol-by-symbol Eq. (9) derivation and matched numerical comparisons with T--S Theorem 4, CWR Corollary 27, and Jang Corollary 4; obtain PAC-Bayes and Lean probability reviews |
| Fixed-sample empirical-Bernstein PAC-Bayes foundation | `PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta` and `finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem`; load-bearing MGF: `PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` | Tolstikhin and Seldin, [PAC-Bayes-Empirical-Bernstein Inequality](https://proceedings.neurips.cc/paper/2013/file/a97da629b098b75c294dffdc3e463904-Paper.pdf), especially Eq. (9) and Theorems 3--4 | **SPECIALIZATION** of Eq. (9) with the same constants on finite IID outcome spaces; **DERIVED VARIANT** for the one-event logarithmic-grid endpoint | IID `[0,1]` losses; Bessel empirical variance averaged per hypothesis; posterior selected after the sample; one KL term; empirical risk and empirical variance in the final checked bound | Finite data and hypothesis types; fixed full-support prior; predeclared dyadic scale grid through `Nat.clog 2 n`; constants `5/4` and `5/2`. This is not a literal formalization of Tolstikhin--Seldin Theorem 4 or an all-real optimizer; the separate reverse-epoch lane supplies the all-sample-size endpoint | `CheckFiniteEmpiricalBernsteinSqrt.balanced64_positiveKL_positiveVariance_nonvacuous`, `balanced64_not_mem_sqrtBadSamples`, and `balanced64Ceiling_lt_ninetyNineHundredths`: `n = 64`, `delta = 1/20`, `KL = log 2`, `Vhat = 16/63`, explicit positive-mass good sample, ceiling `< 99/100` | Compare numerically against Tolstikhin--Seldin Theorem 4 and standard PAC-Bayes-kl/Hoeffding/Bernstein baselines on identical inputs; obtain an external constants and assumptions review |
| Time-uniform finite-IID PAC-Bayes | `PACBayes.TimeUniformIID.timeUniformIIDPACBayes_allPosteriors_bound`; generic engine: `PACBayes.TimeUniform.timeUniformPACBayes_allPosteriors_bound` | Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), especially the master theorem and sub-psi corollaries; compare Jang, Jun, Kuzborskij, and Orabona, [Tighter PAC-Bayes Bounds through Coin-Betting](https://proceedings.mlr.press/v195/jang23a/jang23a.pdf) | **SPECIALIZATION** of the established anytime PAC-Bayes recipe | One common event; every positive time and posterior PMF; fixed data-free prior; KL plus `log(1/delta)`; prior mixture, change of measure, and Ville route | Finite hypotheses and `[0,1]` IID losses. The main displayed endpoint uses a fixed declared tilt; finite-grid selection is separate. It is narrower than general measurable parameter spaces, predictable tilt sequences, and the source papers' broader stochastic-process settings | `CheckTimeUniformIIDPACBayes.lean` checks the IID adapter; the generic Rademacher receipt checks a nonconstant process | Add a positive-KL finite-IID numerical receipt whose final boundary is below one; benchmark fixed/grid tilts against stitched or log-log boundaries |
| Forward predictable-residual process and PAC-Bayes core | `AnytimeValid.ForwardBesselProcess.exists_forwardEmpiricalBernsteinLowerTiltCatalog_event`; finite-hypothesis master: `PACBayes.ForwardBesselPACBayes.exists_forwardBesselPACBayes_event`; countable finite-hypothesis master: `PACBayes.ForwardBesselPACBayesCountable.countableForwardBesselPACBayesMasterProcess_eProcess_of_bounded`; vanishing selector: `PACBayes.ForwardBesselPACBayesCountable.exists_geometricForwardBesselPACBayes_allTime_vanishing_event`; continuous-prior master: `PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.exists_continuousForwardPredictableMeanBesselPACBayes_event`; IID adapter: `PACBayes.ForwardBesselPACBayesIID.exists_forwardIIDBesselPACBayes_event` | Howard, Ramdas, McAuliffe, and Sekhon, [Time-uniform, nonparametric, nonasymptotic confidence sequences](https://arxiv.org/pdf/1810.08240), especially Theorem 4 and Appendix A.8; Chugg, Wang, and Ramdas, [A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds](https://www.jmlr.org/papers/volume24/23-0401/23-0401.pdf), for change of measure, prior mixing, and Ville | **SPECIALIZATION** of Howard et al.'s predictable-residual exponential-supermartingale core; **DERIVED VARIANT** for the deterministic hybrid-Bessel lower envelope and the finite, countable, continuous-prior, and PAC-Bayes conversions | Bounded adapted increments with fixed conditional means; `psi_E(lambda) = -log(1-lambda)-lambda`; predictable squared residuals; fixed tilts in `(0,1)`; one common outer-mass event; posterior-uniform PAC-Bayes lift with one KL term and the selected tilt atom's log-weight charge; a normalized positive `Nat`-indexed catalog and explicit vanishing selector for finite hypotheses | The hybrid-Bessel expression is a deterministic lower envelope of the actual predictable-residual e-process, not itself a proved e-process. The continuous-prior lane retains finite tilts and does not construct a measurable posterior selector or selected process. No all-real optimizer, predictable time-varying tilt, or optional-stopping conclusion is added by pointwise selection | `CheckForwardBesselPACBayesIIDInformative.informative_nonvacuous_receipt` uses a biased Boolean stream at `n = 32`, Bessel variance `1/32`, and `KL = log 2`; it checks the same-prefix empirical-Bernstein and fixed-proxy boundaries at approximately `0.312` and `0.760`. The fair-Boolean checker separately verifies the common-event structure | Compare the hybrid conversion against Howard's exact predictable-variance boundary and optimized/stitched alternatives; extend countable tilts to the continuous-prior layer; obtain PAC-Bayes and Lean probability reviews |
| Finite-state countable adaptive trajectory empirical-Bernstein PAC-Bayes | `StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event` (`FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.lean:356`) | Howard et al., Theorem 4 and Appendix A.8, for the predictable-residual process; Chugg--Wang--Ramdas for PAC-Bayes mixing and Ville | **SPECIALIZATION** for the fixed-tilt predictable-residual process; **DERIVED VARIANT** for the hybrid-Bessel envelope, trajectory conditional-expectation adapter, finite-state confidence allocation, and explicit vanishing selector | Finite nonempty hypothesis catalog and finite measurable-singleton state space; deterministic start; arbitrary time- and full-prefix-dependent kernels; fixed-in-advance `[0,1]` prefix-readable score catalog; full-support finite prior; `0 < delta <= 1`; arbitrary path- and time-dependent posterior PMF selector; one outer-mass event; every `n >= 2`; encountered conditional-prequential versus empirical-prequential risk; geometric tilt selection with an exact boundary tending to zero | The countable trajectory theorem unions confidence over singleton tilt events; it does not build a countable trajectory master e-process. The good event is outer-mass controlled, not asserted measurable. The posterior selector need not be measurable because every posterior is covered pointwise on the common event; this does not produce a selected process or optional-stopping theorem. The target is encountered conditional risk, not stationary risk | `CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.informative_nonvacuous_receipt` uses genuinely prefix-dependent dynamics and a fixed-in-advance online score, `KL = log 2`, observed Bessel variance `1/512`, and `delta = 1/160`; it encloses the selected boundary in `(0.2738, 0.2744)` at `n = 512` and `(0.1432, 0.1434)` at `n = 2048`, proves the latter smaller, and produces a good path with complete right-hand side below `7/25` | Compare against stitched predictable-variance trajectory bounds; add a random initial law without weakening selector semantics; obtain stochastic-process and Lean probability reviews |
| Arbitrary measurable-state and measurable-hypothesis trajectory PAC-Bayes | `StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event` (`FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean:415`) | Howard et al., Theorem 4 and Appendix A.8, for the predictable-residual process; Chugg--Wang--Ramdas for continuous-prior change of measure, mixture, and Ville ingredients | **SPECIALIZATION** for the fixed-tilt predictable-residual process; **DERIVED VARIANT** for joint-measurability transport, continuous-posterior integration, and arbitrary-state trajectory adaptation | Arbitrary measurable parameter and state spaces; deterministic start; full-prefix Markov kernels; one jointly strongly measurable `[0,1]` score family in parameter, prefix, and next state; finite positive normalized tilt catalog with `0 < lambda_j < 1`; a probability prior; `delta > 0`; one outer-mass event covering every `n >= 2`, every tilt atom, and every admissible posterior measure; one measure-theoretic KL term and posterior integral of per-parameter hybrid-Bessel penalties | Finite tilts only; no vanishing selected-width theorem, random initial law, all-real or predictable tilt optimization, measurable posterior selector, selected process, optional stopping, or stationary-risk conclusion. The event is outer-mass controlled rather than asserted measurable. Normalized positive tilt weights make an empty tilt type inconsistent, even though `[Nonempty Tau]` is not an explicit theorem parameter | `CheckContinuousMeasurableTrajectoryGaussianWitness.receiptInformative_goodPath_exists` checks each oriented branch with posterior finite-set mass zero, `KL = 1/32`, conditional and empirical posterior risks `1/2`, boundary at most `489/1024 < 1/2` at `n = 64`, positive observed Bessel variance, and complete right-hand side below one; `receiptInformative_bothBranches_exist` gives both opposite-sign cylinders. The state kernel is still two-atom Rademacher, so this is not evidence for atomless dynamics | Add atomless dynamics, a matched boundary comparison, random starts, and a genuinely data-selected continuous-posterior receipt; obtain measure-theoretic probability and Lean reviews |
| Finite Markov prequential PAC-Bayes | `StochasticDynamics.markovPACBayes_tiltMixture_prequentialRisk_certificate`; random-start extension: `StochasticDynamics.markovPACBayes_tiltMixture_prequentialRisk_certificate_initialLaw`; path identities include `pathSquaredLoss_condExp`, `markovRiskInnovation_condExp_eq_zero`, and `markovRiskInnovation_condSecondMoment_le_one_fourth` | Chugg, Wang, and Ramdas, master theorem and Bernstein-condition corollary; compare Karagulyan and Alquier, [Empirical PAC-Bayes Bounds for Markov Chains](https://openreview.net/forum?id=GlAeeN1Lhp) | **SPECIALIZATION** of established anytime martingale PAC-Bayes machinery; not a reproduction of the stationary-risk Markov theorem | One event of mass at most `delta`; every positive time, posterior over a fixed finite predictor catalog, and atom of a predeclared full-support finite tilt prior; exact transition path law; supplied finite-state initial PMF; exact `log (1 / (delta * weight j))` atom penalty; derived conditional centering and universal `1/4` second-moment proxy | Controls encountered one-step conditional risk, not stationary risk. The supplied initial PMF need not have full support; the proof mixes the common raw failure set over deterministic-start laws before taking one measurable hull. No joint predictor--tilt posterior, countable or all-real tilt optimization, empirical variance, mixing, stationarity, same-trajectory training, general prefix-dependent random start, or continuous state | `CheckMarkovPACBayes.asymmetricBool_randomInitial_adaptivePosteriorTiltMarkovPACBayes_certificate`: asymmetric two-state chain, initial masses `1/3` and `2/3`, path-selected posterior and tilt atom, exact `KL = log 2`, selected boundary `< 1/20`, conditional risk `< 11/20`, exceptional mass at most `1/20`, and good-complement mass at least `19/20` | Add random starts to the general prefix-dependent and measurable-state layers plus normalized countable or predictable tilts; obtain an external assumptions/constants review and keep prequential conditional risk distinct from stationary risk |
| Known-kernel finite stationary-risk PAC-Bayes with automatic Poisson depth | `StochasticDynamics.exists_stationaryPoissonDepthSelection_allTime_vanishing_event` (`FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.lean:966`); foundations: `StochasticDynamics.IsInvariantPMF`, `finiteDobrushinCoefficient_isOscillationContraction`, `finiteDepthPoissonPotential`, and `sum_poissonPotential_increment` | Glynn and Meyn, [A Liapounov Bound for Solutions of the Poisson Equation](https://web.stanford.edu/~glynn/papers/1996/GM96.pdf), especially the discrete Poisson equation (1), additive functional (3), and martingale decomposition (4); Gaubert and Qu, [Dobrushin's Ergodicity Coefficient for Markov Operators on Cones](https://www.cmap.polytechnique.fr/~gaubert/PAPERS/GaubertQuIEOTD14QuFinal.pdf), especially (1) and (4); Howard et al. and Chugg--Wang--Ramdas for the forward empirical-Bernstein/PAC-Bayes event | **SPECIALIZATION** for the finite Dobrushin coefficient and oscillation contraction; **DERIVED VARIANT** for the truncated Poisson potential, explicit residual/span bounds, confidence allocation over depth, and vanishing selected boundary | Finite state and predictor spaces; known kernel `P`; supplied invariant PMF satisfying `stationary.bind P = stationary`; deterministic start; `[0,1]` transition scores; supplied `0 <= alpha < 1`, oscillation contraction, and centered row-risk oscillation envelope `D`; one common event; every `n >= 2`; arbitrary path- and time-dependent posterior PMFs; deterministic `floor(log_2 n)` depth and geometric tilt; exact displayed width tends to zero on every path | This does not construct the invariant law, estimate `P`, or prove an infinite-series Poisson solution. The potential is a finite truncated kernel sum and the remainder is explicit. The source papers do not state this complete PAC-Bayes endpoint. No continuous state space, random initial law, all-real tilt optimizer, or priority claim | `CheckStationaryPoissonContraction.contractionBool_allTime_vanishing_certificate` instantiates the capstone on an asymmetric Boolean chain with nonconstant centered risk and contraction factor `1/4`; `CheckStationaryPoissonDepthSelection.unitChain_allTime_vanishing_certificate` is a separate one-state structural smoke test. Both print the public axiom set | Publish an independently checked symbol dictionary for the complete stationary boundary and a nonvacuous finite-`n` receipt for the logarithmic-depth selector; review exact constants against the cited Poisson and contraction sources |
| Unknown-kernel finite stationary catalog from one non-reset trajectory | `StochasticDynamics.exists_selectedCanonicalEmpiricalStationaryCatalog_event` (`FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean:682`); transition layer: `exists_empiricalTransitionCoordinate_event`, `exists_empiricalTransitionFrequency_event`, and `exists_empiricalCandidateRowTotalVariation_event`; invariant layer: `exists_invariantPMF` and `finiteInvariantPMF_isInvariant`; perturbation layer: `finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV` | Wolfer, [Mixing Time Estimation in Ergodic Markov Chains from a Single Trajectory with Contraction Methods](https://proceedings.mlr.press/v117/wolfer20a.html), especially (1), (6)--(7), visit/edge counts (11), empirical matrix (12), and Fact 5.1; Kueffner, Meggendorfer, Weininger, and Wienhöft, [Confidence Sequences for Online Statistical Model Checking of Markov Decision Processes](https://arxiv.org/abs/2606.25797v1), especially Theorem 3; Mitrophanov, [Sensitivity and Convergence of Uniformly Ergodic Markov Chains](https://doi.org/10.1239/jap/1134587812), as perturbation background; Howard et al. and Chugg--Wang--Ramdas for the coordinate confidence process | **SPECIALIZATION** for the finite Dobrushin/TV normalization and Wolfer coefficient-perturbation corollary; **DERIVED VARIANT** for the visit-gated coordinate process, normalized row confidence, post-data selection from a predeclared candidate catalog, canonical finite invariant target, and joint stationary-risk composition | Finite state, candidate, predictor, and tilt spaces; unknown true kernel observed through one deterministic-start non-reset path; one event of complement mass at most `deltaRisk + deltaTransition`; every `n >= 2` after every row has positive visit mass; post-path selectors for candidate, depth, risk tilt, transition tilt, and posterior; coordinate confidence implies a row-TV radius; candidate coefficient plus `2 * eta` contracts the true kernel; `finiteInvariantPMF P` supplies the target; strict displayed contraction implies uniqueness | Candidates and weights are predeclared; a selector cannot invent a new model outside the uniformly covered family. The theorem requires all rows visited, uses a noncomputable chosen invariant PMF, and gives uniqueness only under the displayed strict-contraction premise. It is not the reset/simulation-access MDP setting of Kueffner et al., the stationary-ergodic mixing-time interval of Wolfer, a continuous-state result, or a priority claim | `CheckEmpiricalStationaryCatalog.boolCatalog_sameData_certificate` is a structural instantiation of the full combined event. `CheckEmpiricalStationaryCatalogInformative.receiptInformative_goodPath_exists` and `receiptInformative_bothBranches_exist` use only `receiptRiskBad`, supply the selected row-TV error deterministically through `receiptSelectedRowTV`, and never invoke the transition-confidence exceptional event. They certify informative risk/candidate branches, not an informative path outside the theorem's combined risk-plus-transition event. An end-to-end informative combined-event receipt is **UNSWEPT** | Add the missing combined-event informative receipt using the empirical transition radius produced on the same path; compare row widths and contraction certificates against Wolfer and the June-2026 MDP confidence sequences; obtain probability, Markov-chain, and Lean reviews |

### Exact candidate-v0.2 endpoint provenance

This is the declaration-level navigation layer for exactly the 19 names in
[Public API stability](./api-stability.md). It reuses the source locators,
classifications, nonclaims, and bounded formalization comparisons already
recorded in this ledger, [Mathematical sources](./references.md), and
[Related work](./related-work.md); it adds no source, novelty, or priority
claim. `UNSWEPT` means that those records do not contain an exact
audited relation or the named evidence. It does not mean that no match or
evidence exists.

The four `examples/stable_imports/Check*V02.lean` files exercise the exact
names, types, and printed axiom sets. The committed public-API signature
snapshot is normative. The dedicated checkers below add theorem-family or
concrete-receipt coverage where present. The Lean signatures, not these
summaries, remain authoritative.

| # | Candidate v0.2 declaration | Existing mathematical provenance | Classification and exact boundary | Checker surface | Prior-formalization status |
|---:|---|---|---|---|---|
| 1 | `FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event` | Tolstikhin--Seldin Eq. (9) and Theorems 3--4; Chugg--Wang--Ramdas Corollary 27 and Appendix A.11; Jang et al. Theorem 1 and Corollary 4 | **SPECIALIZATION** only for the finite-outcome IID Bessel MGF; **DERIVED VARIANT** for the continuous-prior reverse mixture and all-sample reverse stitch. Finite observations and offline simultaneous event; not a forward e-process, optional-stopping theorem, or measurable posterior selector | `examples/stable_imports/CheckPACBayesV02.lean`; `examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean` | StatLean fixed-sample/Hoeffding and Pythia Ville/e-process results are adjacent; exact capstone comparator: **UNSWEPT** |
| 2 | `FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.exists_continuousForwardPredictableMeanBesselPACBayes_event` | Howard et al. Theorem 4 and Appendix A.8; Chugg--Wang--Ramdas change-of-measure, prior-mixture, and Ville route | **SPECIALIZATION** for the fixed-tilt predictable-residual process; **DERIVED VARIANT** for the hybrid-Bessel and continuous-prior PAC-Bayes lift. Finite declared tilts; no measurable posterior selector or selected process | `examples/stable_imports/CheckPACBayesV02.lean`; `examples/CheckContinuousTrajectoryEmpiricalBernsteinPACBayes.lean` | Pythia sequential infrastructure is adjacent; exact continuous-prior capstone comparator: **UNSWEPT** |
| 3 | `FormalSLT.PACBayes.ForwardBesselPACBayesCountable.exists_countableForwardBesselPACBayes_event` | Howard et al. Theorem 4 and Appendix A.8; Chugg--Wang--Ramdas change-of-measure, prior-mixture, and Ville route | **SPECIALIZATION** for the fixed-tilt predictable-residual process; **DERIVED VARIANT** for the normalized countable tilt catalog and PAC-Bayes event. It does not supply a countable continuous-prior lift or selected process | `examples/stable_imports/CheckPACBayesV02.lean`; `examples/CheckForwardBesselPACBayesCountable.lean` | Pythia sequential infrastructure is adjacent; exact countable PAC-Bayes capstone comparator: **UNSWEPT** |
| 4 | `FormalSLT.PACBayes.ForwardBesselPACBayesCountable.exists_geometricForwardBesselPACBayes_allTime_vanishing_event` | Same Howard et al. and Chugg--Wang--Ramdas route as row 3 | **DERIVED VARIANT** for the geometric selector and pathwise vanishing displayed width. Pointwise selection does not create a selected e-process or optional-stopping theorem | `examples/stable_imports/CheckPACBayesV02.lean`; `examples/CheckForwardBesselPACBayesCountable.lean` | Pythia sequential infrastructure is adjacent; exact vanishing-selector capstone comparator: **UNSWEPT** |
| 5 | `FormalSLT.PACBayes.TimeUniform.timeUniformPACBayes_tiltMixture_allPosteriors_bound` | Chugg--Wang--Ramdas master and sub-psi route; Jang et al. as the recorded all-time comparator | **SPECIALIZATION** of the anytime PAC-Bayes recipe. Finite hypotheses and a finite predeclared tilt mixture; no all-real or predictable time-varying tilt optimizer | `examples/stable_imports/CheckPACBayesV02.lean`; `examples/CheckTimeUniformTiltMixture.lean` | Pythia proves Ville/e-process infrastructure, while its two named PAC-Bayes capstones conclude `True`; exact checked capstone comparator: **UNSWEPT** |
| 6 | `FormalSLT.AnytimeValid.eProcess_typeI_control` | Ville (1939) and the e-value/safe-testing source family in `docs/references.md`; exact source theorem locator: **UNSWEPT** | Safe-testing Type-I control over the Ville maximal inequality; the current ledger does not classify it as a literal reproduction of a named source theorem | `examples/stable_imports/CheckSequentialV02.lean`; behavioral receipt in `examples/CheckEProcess.lean` | Pythia's `ville_supermartingale`, `EProcess`, and Type-I-error layer is direct formalization prior art |
| 7 | `FormalSLT.AnytimeValid.exists_forwardEmpiricalBernsteinLowerTiltCatalog_selected_event` | Howard et al. Theorem 4 and Appendix A.8 for the fixed-tilt predictable-residual process | Pointwise selection from a predeclared finite tilt catalog; the hybrid lower envelope is not itself a proved selected e-process and adds no optional-stopping conclusion | `examples/stable_imports/CheckSequentialV02.lean`; `examples/CheckForwardBesselProcess.lean` | Pythia sequential infrastructure is adjacent; exact selected hybrid-boundary comparator: **UNSWEPT** |
| 8 | `FormalSLT.AnytimeValid.SelectionCost.selectedWeightedScore_expectation_le_one` | Named source theorem/equation/page mapping in the current ledger: **UNSWEPT** | Finite observation and index types under a PMF; each nonnegative score has expectation at most one; predeclared nonnegative weights sum to at most one; the selector may depend on the observation. No optimality or priority claim | `examples/stable_imports/CheckSequentialV02.lean`; `examples/CheckSelectionCost.lean` | Exact proof-assistant comparator: **UNSWEPT** |
| 9 | `FormalSLT.AnytimeValid.AllocationLogLog.frequently_geometricEpoch_loglogCost` | Named source theorem/equation/page mapping in the current ledger: **UNSWEPT** | Deterministic consequence of positive epoch weights with total sum at most one: an explicit iterated-log cost along an unbounded geometric-epoch subsequence. It is not itself a probability bound | `examples/stable_imports/CheckSequentialV02.lean`; `examples/CheckAllocationLogLog.lean` | Exact proof-assistant comparator: **UNSWEPT** |
| 10 | `FormalSLT.AnytimeValid.UniversalBoundaryLowerBound.fairSign_anytimeBoundary_frequently_ge_mul_sqrt` | Named source theorem/equation/page mapping in the current ledger: **UNSWEPT** | One-sided fair-sign lower bound for a deterministic boundary whose crossing probability is at most `delta < 1`, for every multiplier `C >= 0`. It is not a general-process LIL theorem; the separate constant-one limsup endpoint remains conditional on its stated upper-LIL premise | `examples/stable_imports/CheckSequentialV02.lean`; `examples/CheckUniversalBoundaryLowerBound.lean` | Exact proof-assistant comparator: **UNSWEPT** |
| 11 | `FormalSLT.StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event` | Howard et al. Theorem 4 and Appendix A.8; Chugg--Wang--Ramdas PAC-Bayes mixing and Ville route | **SPECIALIZATION** for the fixed-tilt process; **DERIVED VARIANT** for the trajectory adapter, allocation, and vanishing selector. It controls encountered conditional-prequential risk on an outer-mass event, not stationary risk or a selected e-process | `examples/stable_imports/CheckStochasticDynamicsV02.lean`; `examples/CheckTrajectoryEmpiricalBernsteinPACBayesCountable.lean` | Pythia sequential and AFP Markov infrastructure are adjacent; exact trajectory capstone comparator: **UNSWEPT** |
| 12 | `FormalSLT.StochasticDynamics.exists_stationaryPoissonDepthSelection_allTime_vanishing_event` | Glynn--Meyn equations (1), (3), and (4); Gaubert--Qu equations (1) and (4); Howard et al. and Chugg--Wang--Ramdas concentration route | **SPECIALIZATION** for finite Dobrushin/oscillation contraction; **DERIVED VARIANT** for finite Poisson truncation, depth allocation, and the selected PAC-Bayes boundary. Known kernel and supplied invariant law; no infinite-series Poisson solution | `examples/stable_imports/CheckStochasticDynamicsV02.lean`; `examples/CheckStationaryPoissonDepthSelection.lean` | StatLean, Econlib, and AFP give invariant-law comparators; CertRL gives adjacent Bellman contraction. Exact stationary PAC-Bayes capstone comparator: **UNSWEPT** |
| 13 | `FormalSLT.StochasticDynamics.exists_selectedCanonicalEmpiricalStationaryCatalog_event` | Wolfer equations (1), (6)--(7), and (11)--(12), plus Fact 5.1; Kueffner et al. Theorem 3 comparator; Mitrophanov perturbation background; Howard et al. and Chugg--Wang--Ramdas concentration route | **SPECIALIZATION** for finite TV/Dobrushin normalization; **DERIVED VARIANT** for visit-gated transition confidence, predeclared candidate selection, and stationary-risk composition. Requires every row visited and uses a noncomputable chosen invariant PMF | `examples/stable_imports/CheckStochasticDynamicsV02.lean`; `examples/CheckEmpiricalStationaryCatalog.lean` | StatLean, Econlib, and AFP invariant-law work is adjacent; exact combined stationary-catalog capstone comparator and an informative combined-event receipt: **UNSWEPT** |
| 14 | `FormalSLT.StochasticDynamics.exists_stationaryTargetPolicyOPE_event` | One-step target-to-behavior likelihood-ratio cancellation; Howard et al. Theorem 4 and Appendix A.8; Chugg--Wang--Ramdas PAC-Bayes route; Glynn--Meyn Poisson organization | **SPECIALIZATION** of the predictable-residual/PAC-Bayes ingredients; **DERIVED VARIANT** for controlled importance weighting and exact-Poisson stationary risk. Supplied environment, invariant laws, potentials, and overlap; not trajectory importance sampling, doubly robust estimation, or policy optimization | `examples/stable_imports/CheckStochasticDynamicsV02.lean`; `examples/CheckStationaryTargetPolicyOPE.lean` | StatLean, Econlib, AFP, and CertRL supply adjacent invariant-law or finite-MDP infrastructure; exact formal OPE comparator: **UNSWEPT** |
| 15 | `FormalSLT.StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event` | Howard et al. Theorem 4 and Appendix A.8; Chugg--Wang--Ramdas continuous-prior change-of-measure, mixture, and Ville ingredients | **SPECIALIZATION** for the fixed-tilt process; **DERIVED VARIANT** for joint-measurability transport, continuous-posterior integration, and arbitrary-state trajectory adaptation. Finite tilts and deterministic start; no selected process or stationary-risk conclusion | `examples/stable_imports/CheckStochasticDynamicsV02.lean`; `examples/CheckContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean` | StatLean and Pythia are adjacent; AFP's reviewed Markov development is countable-state. Exact measurable-state capstone comparator: **UNSWEPT** |
| 16 | `FormalSLT.StochasticDynamics.markovPACBayes_tiltMixture_prequentialRisk_certificate_initialLaw` | Chugg--Wang--Ramdas master/Bernstein route; Karagulyan--Alquier as the recorded Markov comparator | **SPECIALIZATION** of anytime martingale PAC-Bayes machinery. Finite Markov prequential risk with a supplied initial law; not stationary risk, empirical variance, or same-trajectory training | `examples/stable_imports/CheckStochasticDynamicsV02.lean`; `examples/CheckMarkovPACBayes.lean` | Pythia sequential and AFP Markov infrastructure are adjacent; CertRL's Bellman contraction is not prequential risk. Exact capstone comparator: **UNSWEPT** |
| 17 | `FormalSLT.VC.VCDimension.sauerShelahFiniteSetFamily` | Sauer--Shelah/VC source route recorded through Mohri--Rostamizadeh--Talwalkar and Shalev-Shwartz--Ben-David; exact theorem/page/constant mapping: **UNSWEPT** | Finite set-family Sauer--Shelah theorem; literal-reproduction versus specialization classification is **UNSWEPT** and no priority claim follows | `examples/stable_imports/CheckVCV02.lean`; `examples/CheckWrapperPort.lean` | `formal-learning-theory-kernel` and the adjacent Lean statistical-learning projects cover PAC/VC infrastructure; exact theorem comparator: **UNSWEPT** |
| 18 | `FormalSLT.VC.VCRademacher.empiricalRademacherComplexity_le_massart_effective` | Rademacher/VC and finite-class Massart source route recorded through Mohri--Rostamizadeh--Talwalkar, Shalev-Shwartz--Ben-David, and the concentration references; exact theorem/page/constant mapping: **UNSWEPT** | Finite effective-class Massart adapter; literal-reproduction versus derived-variant classification is **UNSWEPT** | `examples/stable_imports/CheckVCV02.lean`; `examples/CheckWrapperPort.lean` | `lean-rademacher`, StatsMLlib, StatLean, and the other recorded Lean SLT projects are adjacent; exact endpoint comparator: **UNSWEPT** |
| 19 | `FormalSLT.VC.VCSampleComplexity.vc_erm_excessRisk_tail` | VC/Rademacher route recorded through Mohri--Rostamizadeh--Talwalkar and Shalev-Shwartz--Ben-David; bounded-differences route recorded through Boucheron--Lugosi--Massart and McDiarmid; exact theorem/page/constant mapping: **UNSWEPT** | VC-style finite-class ERM excess-risk tail, assuming supplied binomial-sum growth bounds for the effective classes of both the loss and its negation. The theorem does not take a VC dimension premise directly; exact source-theorem and constant-level classification is **UNSWEPT** | `examples/stable_imports/CheckVCV02.lean` and `examples/CheckWrapperPort.lean` check the exact public alias; `examples/CheckVCSampleComplexity.lean` checks the canonical implementation theorem | `lean-rademacher`, StatsMLlib, `formal-learning-theory-kernel`, and the other recorded Lean SLT projects are adjacent; exact capstone comparator: **UNSWEPT** |

### Proof-assistant and reusable-interface crosswalk

**Bounded-search legend.** The records in [Related work](./related-work.md) pin
Lean comparators StatLean `e1ef06b`, Pythia `6540433`,
formal-learning-theory-kernel `7511199`, and Econlib `003655c`; AFP artifact
`afp-2026-08-12`; and Rocq sources MathComp Analysis `fcd4ec5`, Infotheo
`98573b`, coq-proba `c5a74b`, and FormalML `8495ce1`. `—` means that these
records contain no exact endpoint, not that none exists elsewhere; no novelty or
priority follows. Mathlib names are selected declarations on the current proof
path, not a minimal trace. Surface labels are descriptive only:
**GENERIC LIBRARY LEMMA**, **APPLICATION ADAPTER**, or **REPO-SPECIFIC**.

| Flagship endpoint | Selected Mathlib declarations | Pinned Lean comparators | Isabelle/HOL / AFP | Rocq / Coq | Reusable FormalSLT surface |
|---|---|---|---|---|---|
| All-sample measurable empirical-Bernstein PAC-Bayes | `InformationTheory.klDiv`, `InformationTheory.toReal_klDiv`, `Nat.log` | StatLean: `StatisticalLearning.pac_bayes` is fixed-sample/Hoeffding; Pythia: `ville_supermartingale`, `EProcess` | AFP Concentration Inequalities: foundational | — | `continuous_donsker_varadhan` — **GENERIC LIBRARY LEMMA** |
| Fixed-sample empirical-Bernstein PAC-Bayes | `convexOn_exp`, `Fintype.card_pos_iff`, `Nat.clog` | formal-learning-theory-kernel: `pac_bayes_finite` uses cross entropy; StatLean: `pac_bayes` is the closest KL comparator, but Hoeffding-style | AFP Concentration Inequalities: foundational | — | `finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` — **REPO-SPECIFIC** |
| Time-uniform finite-IID PAC-Bayes | `condExp_indep_eq`, `condExp_mono`, `ProbabilityTheory.Supermartingale` | Pythia proves Ville/e-process infrastructure; `pacbayes_cs_ville` and `pacbayes_mixture_eprocess` have proposition `True`, so are not capstone comparators | — | — | `mixture_is_supermartingale`, `countableWeightedSupermartingale_tsum` — **GENERIC LIBRARY LEMMA** |
| Forward predictable-residual and PAC-Bayes family | `condExp_sub`, `condExp_smul`, `ProbabilityTheory.Supermartingale` | Pythia: Ville, exponential e-process, and averaging infrastructure | AFP Concentration Inequalities: adjacent infrastructure | — | `forwardEmpiricalBernsteinFactor_condExp_le_one` — **REPO-SPECIFIC**; `mixture_is_supermartingale` — **GENERIC LIBRARY LEMMA** |
| Finite-state countable adaptive trajectory PAC-Bayes | `Kernel.traj`, `Kernel.condExp_traj`, `condVar_ae_eq_condExp_sq_sub_sq_condExp` | Pythia: sequential infrastructure | AFP Markov Models: countable-state paths, stopping times, recurrence | CertRL: discounted value iteration, not trajectory PAC-Bayes | `observedTrajectoryScore_condExp` — **APPLICATION ADAPTER** |
| Arbitrary measurable-state trajectory PAC-Bayes | `Kernel.traj`, `Kernel.condExp_traj`, `InformationTheory.klDiv` | StatLean: arbitrary observations, countable discrete hypotheses, fixed sample; Pythia: sequential infrastructure | AFP Markov Models: countable-state only | — | `integral_observedTrajectoryScore_traj_of_joint`, `observedTrajectoryScore_condExp_of_joint` — **APPLICATION ADAPTER** |
| Finite Markov prequential PAC-Bayes | `Kernel.traj`, `Kernel.condExp_traj`, `condVar_ae_eq_condExp_sq_sub_sq_condExp` | Pythia: sequential infrastructure | AFP Markov Models: Markov paths | CertRL: `is_contraction_bellman_op` is discounted Bellman contraction, not prequential risk | `pathSquaredLoss_condExp_via_trajectory`, `observedTrajectoryScore_condExp_of_joint` — **APPLICATION ADAPTER** |
| Known-kernel stationary Poisson-depth PAC-Bayes | `Kernel.traj`, `Nat.log`, `Nat.log_pow_left` | StatLean: invariant-law existence/uniqueness and Harris ergodicity; Econlib: finite stationary laws, invariance bridge, Doeblin contraction | AFP Stochastic Matrices: `stationary_distribution_exists`, `stationary_distribution_unique`; AFP Markov Models: PMF-bind stationarity | CertRL: Bellman contraction only | `finitePMFTotalVariation`, `finiteDobrushinCoefficient_isOscillationContraction` — **GENERIC LIBRARY LEMMA**; bridge `70e2847` — **APPLICATION ADAPTER**, outside this tree |
| Unknown-kernel empirical stationary catalog | `stdSimplex`, `CompactSpace.tendsto_subseq`, `Kernel.traj` | StatLean and Econlib: invariant-law and contraction comparators | AFP Stochastic Matrices and Markov Models: invariant-law comparators | CertRL: adjacent finite-MDP work | `exists_invariantPMF` — **REPO-SPECIFIC**; `finitePMFTotalVariation`, `finiteDobrushinCoefficient_isOscillationContraction` — **GENERIC LIBRARY LEMMA** |

An earlier all-times PAC-Bayes-Bernstein martingale comparator is Seldin,
Cesa-Bianchi, Auer, Laviolette, and Shawe-Taylor,
[PAC-Bayes-Bernstein Inequality for Martingales and its Application to Multiarmed Bandits](https://proceedings.mlr.press/v26/seldin12a.html).

### Mathlib import boundary at the v0.2 code freeze

At FormalSLT commit `b91d6a37938cf1665430ea2a8cc45d8f67995f12`
(tree `4b476c0c88165f871daa3f5a4094591ef0e52f1e`), the project uses Lean
`v4.32.2` and Mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c`. For each flagship endpoint,
the table recursively follows `import FormalSLT...` declarations and records
selected Mathlib modules named directly at the boundary of that FormalSLT
source closure. The count is the complete number of unique Mathlib boundary
modules; routine algebra and tactic imports are omitted from the displayed
spine.

| Flagship endpoint | Mathlib boundary count | Selected exact import spine |
|---|---:|---|
| All-sample measurable empirical-Bernstein PAC-Bayes | 49 | Continuous change of measure: `Mathlib.InformationTheory.KullbackLeibler.Basic`, `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`; infinite-product and reverse-time infrastructure: `Mathlib.Probability.ProductMeasure`, `Mathlib.MeasureTheory.MeasurableSpace.Invariants`, `Mathlib.Probability.Process.Filtration`, `Mathlib.Probability.Martingale.OptionalStopping`; integration and epoch selection: `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Integral.Prod`, `Mathlib.Data.Nat.Log` |
| Fixed-sample empirical-Bernstein PAC-Bayes | 26 | Finite matching and variance: `Mathlib.Data.Fintype.Perm`, `Mathlib.Data.Fintype.BigOperators`, `Mathlib.Probability.Moments.Variance`; exponential-moment argument: `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Analysis.Convex.Jensen`, `Mathlib.Analysis.Convex.SpecificFunctions.Basic`; finite grid: `Mathlib.Data.Nat.Log` |
| Time-uniform finite-IID PAC-Bayes | 35 | IID adapter: `Mathlib.Probability.ConditionalExpectation`, `Mathlib.Probability.HasLaw`; finite-posterior change of measure: `Mathlib.InformationTheory.KullbackLeibler.Basic`, `Mathlib.Probability.ProbabilityMassFunction.Integrals`; mixture and maximal control: `Mathlib.MeasureTheory.Integral.Prod`, `Mathlib.Probability.Martingale.OptionalStopping` |
| Forward predictable-residual and PAC-Bayes family | 60 | Forward-Bessel algebra: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`, `Mathlib.NumberTheory.Harmonic.Defs`; anytime and countable machinery: `Mathlib.Probability.Martingale.OptionalStopping`, `Mathlib.MeasureTheory.Integral.DominatedConvergence`, `Mathlib.Analysis.PSeries`; finite and continuous PAC-Bayes layers: `Mathlib.InformationTheory.KullbackLeibler.Basic`, `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`, `Mathlib.Probability.ProbabilityMassFunction.Integrals` |
| Finite-state countable adaptive trajectory PAC-Bayes | 61 | Trajectory law and conditional moments: `Mathlib.Probability.Kernel.IonescuTulcea.Traj`, `Mathlib.Probability.CondVar`, `Mathlib.Probability.ConditionalExpectation`, `Mathlib.Probability.ProbabilityMassFunction.Integrals`; anytime selector: `Mathlib.Probability.Process.Filtration`, `Mathlib.Probability.Martingale.OptionalStopping`, `Mathlib.Analysis.SpecialFunctions.Log.Deriv`, `Mathlib.NumberTheory.Harmonic.Defs`, `Mathlib.Analysis.PSeries`; finite-posterior KL: `Mathlib.InformationTheory.KullbackLeibler.Basic` |
| Arbitrary measurable-state trajectory PAC-Bayes | 49 | Trajectory law and conditional moments: `Mathlib.Probability.Kernel.IonescuTulcea.Traj`, `Mathlib.Probability.CondVar`, `Mathlib.Probability.ConditionalExpectation`; continuous change of measure: `Mathlib.InformationTheory.KullbackLeibler.Basic`, `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`; integration and anytime control: `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Integral.Prod`, `Mathlib.Probability.Martingale.OptionalStopping` |
| Finite Markov prequential PAC-Bayes | 38 | `Mathlib.Probability.Kernel.IonescuTulcea.Traj`, `Mathlib.Probability.CondVar`, `Mathlib.Probability.ConditionalExpectation`, `Mathlib.Probability.ProbabilityMassFunction.Integrals`, `Mathlib.InformationTheory.KullbackLeibler.Basic`, `Mathlib.Probability.Martingale.OptionalStopping` |
| Known-kernel stationary Poisson-depth PAC-Bayes | 61 | Path and posterior infrastructure: `Mathlib.Probability.Kernel.IonescuTulcea.Traj`, `Mathlib.Probability.CondVar`, `Mathlib.Probability.ProbabilityMassFunction.Integrals`, `Mathlib.InformationTheory.KullbackLeibler.Basic`; all-time depth and tilt selection: `Mathlib.Probability.Process.Filtration`, `Mathlib.Probability.Martingale.OptionalStopping`, `Mathlib.Analysis.PSeries`, `Mathlib.NumberTheory.Harmonic.Defs`, `Mathlib.Data.Nat.Log` |
| Unknown-kernel empirical stationary catalog | 63 | The known-kernel stationary closure above, plus exactly `Mathlib.Analysis.Convex.StdSimplex` and `Mathlib.Topology.Sequences` for finite invariant-law existence |

This is import-provenance evidence, not a minimal theorem-dependency trace. A
module can occur through shared infrastructure without every declaration being
used by the final theorem. The map does not claim that Mathlib supplies the
FormalSLT endpoint, that every displayed module is necessary, or that an
upstream Mathlib contribution exists.

## Stationary and unknown-kernel source dictionary

FormalSLT uses probabilists' finite total variation throughout this lane:

```text
finitePMFTotalVariation(p, q) = (1/2) * sum_z |p(z) - q(z)|.
```

Thus `finiteDobrushinCoefficient P` is the maximum row-pair total variation.
Its oscillation inequality has no additional factor two. If every row of `P`
is within TV radius `eta` of the corresponding row of `Q`, Wolfer's maximum
row-`L1` perturbation norm is at most `2 * eta`; this is the source of the
`+ 2 * eta` term below.

| Source result | FormalSLT mapping | Exact correspondence | Classification and audit boundary |
|---|---|---|---|
| Gaubert--Qu (1), finite Dobrushin formula, and (4), diameter/Hopf-oscillation contraction | `finitePMFTotalVariation` (`FormalSLT/StochasticDynamics/StationaryPoissonDobrushin.lean:46`); `finiteDobrushinCoefficient` (`FormalSLT/StochasticDynamics/StationaryPoissonDobrushin.lean:209`); `finiteDobrushinCoefficient_isOscillationContraction` (`FormalSLT/StochasticDynamics/StationaryPoissonDobrushin.lean:262`) | Row `L1 / 2` is FormalSLT TV; maximizing it over row pairs is the checked coefficient; the checked one-step oscillation inequality uses the same coefficient without an extra factor | **SPECIALIZATION**, verified for finite PMF kernels. The paper's general cone theorem is not formalized here |
| Glynn--Meyn (1), (3), and (4), Poisson equation and martingale decomposition | `approximatePoissonResidual` (`FormalSLT/StochasticDynamics/StationaryPoissonPACBayes.lean:62`); `poissonCorrectedTransitionScore` (`FormalSLT/StochasticDynamics/StationaryPoissonPACBayes.lean:78`); `sum_poissonPotential_increment` (`FormalSLT/StochasticDynamics/StationaryPoissonPACBayes.lean:228`); `finiteDepthPoissonPotential` (`FormalSLT/StochasticDynamics/StationaryPoissonContraction.lean:182`); `finiteDepthPoissonResidualBound` (`FormalSLT/StochasticDynamics/StationaryPoissonContraction.lean:434`) | The correction telescopes as a Poisson coboundary. FormalSLT chooses a finite truncated potential and retains its residual explicitly rather than assuming an exact infinite-horizon solution | **DERIVED VARIANT — theorem-level audit complete.** FormalSLT uses the discrete Poisson identity (1) and the finite telescoping/martingale organization behind (3)--(4). It does not reproduce Proposition 1.1, Theorems 2.1--2.3, Lemma 3.1, Theorem 3.2, Theorems 4.1--4.4, or Section 4.2's perturbation identities. Its finite Neumann truncation and `alpha^m * D` residual instead follow from finite oscillation contraction |
| Wolfer (1), (6)--(7), (11)--(12), and Fact 5.1 | `finitePMFTotalVariation` (`FormalSLT/StochasticDynamics/StationaryPoissonDobrushin.lean:46`); `finiteDobrushinCoefficient` (`FormalSLT/StochasticDynamics/StationaryPoissonDobrushin.lean:209`); `transitionVisitMass` (`FormalSLT/StochasticDynamics/EmpiricalTransitionConfidence.lean:115`); `transitionEdgeMass` (`FormalSLT/StochasticDynamics/EmpiricalTransitionConfidence.lean:120`); `empiricalTransitionFrequency` (`FormalSLT/StochasticDynamics/EmpiricalTransitionConfidence.lean:125`); `finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV` (`FormalSLT/StochasticDynamics/StationaryPoissonRobustInvariant.lean:73`) | Counts and empirical rows use the same one-trajectory visit/edge organization. Fact 5.1 gives `abs(kappa(P) - kappa(Q)) <= max_z L1(P(z), Q(z))`; row TV at most `eta` therefore gives the checked one-sided `kappa(P) <= kappa(Q) + 2*eta` | **SPECIALIZATION** for the deterministic coefficient corollary; **DERIVED VARIANT** for the time-uniform visit-gated confidence event. Wolfer's fixed high-confidence mixing-time estimator is not reproduced |
| Kueffner--Meggendorfer--Weininger--Wienhöft, Theorem 3 | `exists_empiricalTransitionCoordinate_event` (`FormalSLT/StochasticDynamics/EmpiricalTransitionConfidence.lean:369`), `exists_countableEmpiricalTransitionCoordinate_event` (`FormalSLT/StochasticDynamics/EmpiricalTransitionConfidenceCountable.lean`), and downstream frequency/row-TV events | Both provide time-uniform transition-coordinate confidence. Their theorem treats an IID successor stream localized to each state-action pair, distributes confidence across pairs, and permits simulation access with resets and adaptive action choice. FormalSLT instead derives visit-gated coordinates from one non-reset Markov trajectory; its countable extension allocates confidence over a predeclared geometric tilt catalog and exposes positive-visit-frequency and candidate-discrepancy premises for vanishing normalized budgets | **DERIVED VARIANT / COMPARATOR — formula audit complete.** Theorem 3's four displayed confidence sequences were compared formula by formula. None is FormalSLT's coordinate boundary. Betting Bernstein is the closest process comparator through the shared `-log(1-lambda)-lambda` predictable-residual term, but its adaptive `lambda_i`, weighted mean, and row-local IID clock differ from FormalSLT's fixed predeclared tilt atoms, global visit gating, prior charge, hybrid-Bessel envelope, and later positive-visit normalization |
| Mitrophanov, finite-time and invariant-law perturbation bounds under uniform ergodicity | `finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV` (`FormalSLT/StochasticDynamics/StationaryPoissonRobustInvariant.lean:73`); `invariantPMF_unique_of_candidate_rowTV` (`FormalSLT/StochasticDynamics/StationaryPoissonRobustInvariant.lean:258`); empirical stationary-catalog composition | Mitrophanov's finite-state coefficient of ergodicity is exactly FormalSLT's maximum row-pair total variation. After converting the paper's signed-measure norm to probabilists' TV and taking its unperturbed kernel as FormalSLT's candidate `Q`, the paper's `m = 1` invariant-law sensitivity result gives `TV(pi_P, pi_Q) <= eta / (1 - kappa(Q))` under its invariant-law and uniform-ergodicity assumptions. FormalSLT instead proves `kappa(P) <= kappa(Q) + 2 * eta` and uniqueness for supplied invariant laws of `P` when `kappa(Q) + 2 * eta < 1`; it does not prove stationary-law sensitivity | **COMPARATOR — normalization and constants audit complete.** The `+ 2 * eta` coefficient inequality remains the elementary row-triangle/Wolfer corollary, not Mitrophanov's theorem |
| Finite invariant-law existence | `exists_finiteKernelPushSimplex_fixedPoint` (`FormalSLT/StochasticDynamics/FiniteInvariantExistence.lean:252`); `exists_invariantPMF` (`FormalSLT/StochasticDynamics/FiniteInvariantExistence.lean:317`); `finiteInvariantPMF`; `finiteInvariantPMF_isInvariant` (`FormalSLT/StochasticDynamics/FiniteInvariantExistence.lean:349`) | FormalSLT takes Cesaro averages of iterated finite laws, extracts a convergent subsequence by compactness of the real simplex, and passes the telescoping push-forward defect to zero | **DERIVED VARIANT** of the classical finite Krylov--Bogolyubov route. Direct proof-assistant comparators are recorded in [Related work](./related-work.md); no priority conclusion follows |

The source audit used the following exact PDF bytes: Glynn--Meyn
(`SHA-256 15194bd87978de63163040e9f64a8379aea1f19960740a62d95b564265027d5d`),
Kueffner et al. arXiv v1
(`SHA-256 04d41e3925a41f45d22daeb5f073317a39291de2d81d8313633cee60d7ea2f22`),
and Mitrophanov
(`SHA-256 3a7a9c35f0a130181c03ff7c24311e849435cc27dbdf77885b26e6ec98c9fddb`).
These hashes identify the files inspected; they do not turn the bounded source
comparison into an exhaustive prior-art or priority search.

## Controlled-queue literature and provenance spine

This is a bounded evidence map for the historical pre-correction checkpoint
`5eae99f5f217edc7b44bd81dda6fde2a946effda` (tree
`255c20fe5297c1adcc0a4ee3b9e3a308b311f48a`). It records the chain from the
mathematical source families above to the controlled-queue application. It is
registration-ineligible because it predates the fail-closed OSF final-GUID
cross-binding correction. It is not a novelty or priority search.

Two classifications are deliberately independent:

- **Literature fidelity** uses `SPECIALIZATION` and `DERIVED VARIANT` as
  defined at the top of this ledger. **APPLICATION INSTANTIATION** means that
  exact queue tables and constants discharge a checked generic theorem; it
  does not assert a new source theorem.
- **Evidence status** uses **CHECKED THEOREM** for a Lean declaration exposed
  to a named `examples/Check*.lean` audit, **CHECKED DETERMINISTIC RECEIPT**
  when frozen nonprospective bytes are also independently reconstructed, and
  **FROZEN PROTOCOL ONLY** when the contract contains no prospective data or
  result. These labels say nothing about mathematical priority.

### Source family to generic target-policy chain

| Mathematical source family | FormalSLT declaration and role | Exact assumptions carried into the queue lane | Literature fidelity | Theorem-facing audit |
|---|---|---|---|---|
| One-step target-to-behavior likelihood-ratio cancellation; Howard et al., Theorem 4 and Appendix A.8, for the predictable-residual process; Chugg--Wang--Ramdas for prior mixing, change of measure, and Ville | `controlledObservedImportanceScore_condExp` (`FormalSLT/StochasticDynamics/ControlledTrajectory.lean:316`) proves the one-step conditional-mean identity; `exists_stationaryTargetPolicyOPE_event` (`FormalSLT/StochasticDynamics/StationaryTargetPolicyOPE.lean:431`) adds the exact-Poisson stationary-risk interpretation | Finite state and action spaces; deterministic initial controlled observation; possibly history-dependent behavior policy; predeclared Markov target policies; pointwise overlap; a positive common action-ratio cap `C`; `[0,1]` transition scores; supplied invariant PMFs and bounded exact Poisson potentials; full-support finite hypothesis and tilt priors; `0 < lambda < 1`; `delta > 0` | **SPECIALIZATION** of the predictable-residual/PAC-Bayes ingredients; **DERIVED VARIANT** for the controlled importance-weighting and stationary-Poisson composition. The one-step cancellation is proved algebraically and is not presented as a reproduction of a separately named OPE theorem | `examples/CheckStationaryTargetPolicyOPE.lean`; the controlled semantic prerequisites are also exercised by the application checkers below |
| Glynn--Meyn's Poisson coboundary and martingale organization, with the same Howard/Chugg--Wang--Ramdas concentration layer | `exists_stationaryApproximateTargetPolicyOPE_signedResidual_event` (`FormalSLT/StochasticDynamics/StationaryTargetPolicyApproximateOPE.lean:181`) retains the signed Poisson residual; `exists_stationaryApproximateTargetPolicyOPE_event` (`FormalSLT/StochasticDynamics/StationaryTargetPolicyApproximateOPE.lean:290`) replaces it by a supplied pointwise envelope | The exact-Poisson assumptions above except that the potential may be approximate; invariance is still supplied; the final endpoint adds the posterior average of the explicit residual envelope | **DERIVED VARIANT**. Glynn--Meyn do not state this importance-weighted, PAC-Bayes, finite-catalog endpoint | `examples/CheckStationaryTargetPolicyApproximateOPE.lean` |
| Gaubert--Qu finite Dobrushin/oscillation contraction; Wolfer row-TV normalization and coefficient perturbation; Glynn--Meyn finite Poisson organization | `exists_stationaryRobustCandidateFiniteDepthTargetPolicyOPE_event` in `FormalSLT/StochasticDynamics/StationaryTargetPolicyRobustFiniteDepthOPE.lean` uses a candidate kernel, finite-depth potential, contraction residual, and a supplied physical row-TV radius | A fixed candidate `Q`, target-policy reference PMFs, `0 <= alpha < 1`, centered candidate row-risk oscillation at most `D`, fixed depth `m`, and true-to-candidate row TV at most `eta`; its residual is `alpha^m * D + 2 * (1 + B_m) * eta` | **SPECIALIZATION** for the finite Dobrushin contraction normalization; **DERIVED VARIANT** for the target-policy finite-depth robust endpoint | `examples/CheckStationaryTargetPolicyRobustFiniteDepthOPE.lean` |
| Wolfer one-trajectory visit/edge organization; Kueffner et al. Theorem 3 as a confidence-sequence comparator; Howard/Chugg--Wang--Ramdas for the actual fixed-tilt process | `exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event` (`FormalSLT/StochasticDynamics/StationaryTargetPolicyEmpiricalFiniteDepthOPE.lean:52`) intersects risk and empirical augmented-transition events on the same path | Fixed candidate and depth before the event; behavior action mass exactly `1/2`; every augmented source row visited at the reported time; predeclared risk and transition tilt catalogs; separate `deltaRisk` and `deltaTransition`; no independence assumption. An augmented row-TV radius `etaAug` becomes physical row TV `2 * etaAug`, hence residual `alpha^m * D + 4 * (1 + B_m) * etaAug` | **DERIVED VARIANT / COMPARATOR**. It is neither Wolfer's mixing-time estimator nor Kueffner et al.'s reset/simulation-access row-local IID construction | `examples/CheckStationaryTargetPolicyEmpiricalFiniteDepthOPE.lean` |

The first row uses only one-step action ratios. None of these declarations is a
full-trajectory importance-sampling estimator, a doubly robust estimator, a
policy-optimization theorem, or an identification result without the stated
overlap, invariant-law, and Poisson assumptions.

### Exact queue instantiation and current evidence

| Layer | Exact frozen assumptions and constants | Lean endpoint, checker, and receipt | Evidence status | Literature fidelity and explicit boundary |
|---|---|---|---|---|
| Generated controlled model, scores, overlap, and contraction | `24` physical states, `2` actions, uniform behavior, target-policy catalog of size `4`, fixed Brier-predictor catalog of size `3`, and candidate refresh parameters `5/8`, `3/4`, and `7/8`. The fixed Brier scores lie in `[0,1]`; their centered row-risk oscillation is bounded by `D = 1`; target-to-behavior action ratios are bounded by `C = 3/2`; candidate target-policy Dobrushin coefficients are bounded above by the corresponding refresh parameter | `ControlledQueueTypedModel`, `ControlledQueueTargetPolicyScores`, and `ControlledQueueContraction`; audited by `examples/CheckControlledQueueTypedModel.lean`, `examples/CheckControlledQueueTargetPolicyScores.lean`, and `examples/CheckControlledQueueContraction.lean` | **CHECKED THEOREM** | **APPLICATION INSTANTIATION** of the finite controlled, score, and Dobrushin interfaces. The coefficient values are upper bounds, not asserted exact coefficients. Squared Brier loss is used as a bounded score; no propriety or calibration theorem is invoked. The two causal Beta predictors are not fixed stationary target-policy hypotheses |
| Twelve-atom nominal empirical-kernel OPE | Nominal candidate `gamma = 3/4`; `4 x 3 = 12` policy--predictor atoms; depth fixed before the base event; singleton risk and transition tilts `1/4`; risk and transition budgets `1/40` each; uniform priors over `12` hypotheses and `4,608` augmented transition coordinates; all `48` augmented source rows must be visited at the displayed time | `exists_nominalControlledQueueEmpiricalFiniteDepthOPE_event` (`FormalSLT/Applications/ControlledQueueOPECatalog.lean:313`); `examples/CheckControlledQueueOPECatalog.lean` | **CHECKED THEOREM** | **APPLICATION INSTANTIATION / DERIVED VARIANT** of the generic empirical finite-depth theorem. It does not prove named-trace good-event membership, remove the all-row visitation premise, or make the transition-coordinate event informative on the retrospective receipt |
| Structured refresh-family adaptive event | The true environment is assumed to be the one-parameter refresh family with one fixed `gamma in [0,1)` and fixed initial observation. The predeclared support has `3 x 7 = 21` candidate--depth atoms, depths `[0,1,2,3,5,8,12]`, four risk tilts and four persistence tilts `[1/16,1/8,1/4,1/2]`, arbitrary posterior PMFs over the `12` hypotheses, and budgets `1/40 + 1/40 = 1/20`. Candidate, depth, both tilt atoms, posterior, and time may be selected inside the common event | `exists_controlledQueueStructuredAdaptiveOPE_event` (`FormalSLT/Applications/ControlledQueueStructuredOPE.lean:476`) and `exists_selectedControlledQueueStructuredAdaptiveOPE_event` (`FormalSLT/Applications/ControlledQueueStructuredOPE.lean:515`); `examples/CheckControlledQueueStructuredOPE.lean` | **CHECKED THEOREM** | **APPLICATION INSTANTIATION / DERIVED VARIANT** of approximate-Poisson OPE plus scalar persistence confidence. This is not uniform over `gamma`, does not test refresh-family membership, and does not construct a measurable selected process or selected e-process. Unlike the generic `4,608`-coordinate lane, it has no every-row visitation premise |
| Frozen sharp prospective primary event | True `gamma = 149/200`; initial observation `(eco, state 0)`; horizon `200000`; nominal candidate `gamma = 3/4`; shifted depth-`12` potential; Dirac posterior on queue-threshold policy and nominal-model overload predictor; risk tilt `1/16`; persistence tilt `1/64`; budgets `1/40 + 1/40 = 1/20`; ratio cap `3/2`; candidate-drift oscillation `58989951/9007199254740992`; refresh-sensitivity oscillation `831542406207231/3236962232172544`; cumulant bounds `psi(1/16) <= 1/480` and `psi(1/64) <= 1/8064` | `exists_controlledQueueSharpStructuredReceipt_event` (`FormalSLT/Applications/ControlledQueueSharpStructuredOPE.lean:465`), supported by the exact affine refresh identity in `ControlledQueueRefreshSensitivity`; `examples/CheckControlledQueueSharpStructuredOPE.lean` | **CHECKED THEOREM**, but only for the event and frozen pathwise formula | **APPLICATION INSTANTIATION / DERIVED VARIANT**. No prospective trace exists at this snapshot, no named path is proved to be in the good event, and no endpoint below the frozen `1/10` threshold is claimed |
| Generic prospective histogram reduction | Any `24 x 2 x 24` physical transition histogram matching a path at horizon `200000`; only the preregistered affine Bessel branch, log-cost bounds `9` and `7`, and cumulant bounds `1/480` and `1/8064` are used | `sharpStructuredReceiptBoundary_evaluation_of_histogram` (`FormalSLT/Applications/ControlledQueueSharpStructuredReceiptCore.lean:602`) proves `sharpStructuredOPEBoundary <= sharpStructuredHistogramUpper`; `examples/CheckControlledQueueSharpStructuredReceiptCore.lean` | **CHECKED THEOREM**, generic in the counts; no prospective counts are present | **APPLICATION INSTANTIATION** of already checked arithmetic and event components, not another statistical source theorem. It does not prove histogram provenance, path membership, or the `1/10` threshold. A generated threshold corollary is permitted only if the future exact arithmetic supports it |
| Retrospective nominal known-kernel receipt | Nominal kernel; explicit invariant law; queue-threshold/nominal-model atom; exact stationary Brier risk `4338268437/67816493056 < 13/200`; fixed initial observation `(action 1, state 1)`; aligned suffix horizon `199999`; depth `12`; risk tilt `1/16`; event budget `1/40` | `queueThreshold_nominalModelOverload_stationaryRisk` (`FormalSLT/Applications/ControlledQueueInvariantRisk.lean:1461`) and `knownKernelReceipt_selectedRisk_lt_seven_hundredths` (`FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean:799`); `examples/CheckControlledQueueInvariantRisk.lean`; `examples/CheckControlledQueueKnownKernelReceipt.lean`; `known-kernel-receipt-v1.json` plus its generated manifest and independent verifier | **CHECKED DETERMINISTIC RECEIPT** for the known-kernel arithmetic; the trace and receipt bytes are replayable | **APPLICATION INSTANTIATION**. The `< 7/100` conclusion is conditional on both the aligned histogram and the theorem-produced event inequality. The receipt does not prove that the named retrospective trace is in the event, does not give histogram-conditioned `39/40` coverage, and is not an unknown-kernel result or prospective confirmation |

### Prospective provenance boundary

The canonical protocol is
`applications/controlled_queue/structured-ope-protocol-v1.json`, SHA-256
`070519615ba7cdaf0198a72a03ab6f691a7ff9b37c2eaa97a363d7fd4c3bf153`.
At that historical pre-correction snapshot:

- the trace generator, independent trace verifier, receipt generator, and
  independent receipt verifier have SHA-256 values
  `5b2a2334c0181ef8ec1bb8cbf7626ceecac4fa1de28922abfd0a3ce4798452fa`,
  `0b8177622c6c713ac14d8aa53d5a2cafa63a29e945cd5f8ef75d3ef9fcc18c34`,
  `928d9a3e909f118274dd097c8735b7b94fe709298288f0b2395666f1eba6f01a`,
  and `6918f8bb06c207eee9017871967fd4fc958561990bda51bbe544f1df05d3637f`,
  respectively;
- the six reserved prospective outputs are absent; and
- no immutable OSF registration receipt, formula-selected beacon round, fresh
  trace, fresh receipt, or result is bound or present in this snapshot. The
  evidence status is therefore
  **FROZEN PROTOCOL ONLY**.

#### Current locally checked code freeze

The current locally checked code-freeze snapshot is commit
`6c3f7de49d545be3e6bcfbb32f70b4aa86ef55de` (tree
`12248252ab3dc2bcd549b61f2678d40618fb1c7e`). It retains the canonical
protocol bytes identified above. At this snapshot:

- `scripts/generate_controlled_queue_prospective_trace.py` and
  `scripts/verify_controlled_queue_prospective_trace.py` have SHA-256 values
  `409d3fa5302f6617d2ce1b9922f3721f8c1aec5ca30961a45486e597853b64e0`
  and
  `a18a82f6b1836b55d569eb26a6775b23e8c7a1c239d85342e4a01aabfe470578`,
  respectively;
- `scripts/generate_controlled_queue_prospective_receipt.py` and
  `scripts/verify_controlled_queue_prospective_receipt.py` have SHA-256 values
  `bf19db7a1dd2f10259ecf3ee63132719eae3b5a3abba92cf9a9cc94d45e81a5b`
  and
  `da8983a73d15f5a5c55f72115419962890c88a45dcc38b3ee0ce7aa3919cee69`,
  respectively; and
- the offline-built version-one pre-registration binding
  `applications/controlled_queue/prospective/evidence/code-freeze-binding-v1.json`
  is exactly `1,501` bytes with SHA-256
  `9dea4b601331717358bf0b9e8610384a4f7fbe71c332c563700ec91dd3a2064e`,
  binds the commit and tree above, and contains no `registration_id`; and
- all six reserved prospective outputs remain absent.

For this ledger, the `oracle_true_kernel_selected_h12_eb` and
`selected_h12_nonvariance_fixed_range` comparison rows are both
**PLANNED_NOT_CHECKED** arithmetic-only noncertificates. They are not checked
confidence certificates or theorem results.

This block records only a local pre-registration code, tool-identity, and
binding-byte check. No OSF registration or registration ID exists, no beacon
has been read, and no prospective trace, receipt, result, or public release is
claimed. Commit `6c3f7de49d545be3e6bcfbb32f70b4aa86ef55de` must remain durably
reachable in Git until the registration handoff is complete; squashing it away
or deleting its only preserving ref would prevent exact-object reconstruction
by the offline builder and verifiers.

The future post-beacon gate is ordered: independently verify trace bytes and
beacon provenance, independently verify receipt bytes and arithmetic, then
elaborate the generated Lean certificate. Lean proves the
histogram-to-endpoint mathematics; it does not verify SHA-256, the public
timestamp, the drand signature, or raw binary provenance. The protocol also
keeps the adaptive `21`-atom result separate from the fixed primary, requires
all declared baselines and failures to be published unchanged, and forbids a
secondary row from rescuing a failed primary.

The retrospective trace and known-kernel receipt informed the frozen design.
They are pilot evidence, not confirmatory evidence. The protocol makes no
claim of cumulative value, control regret, policy optimization, validity
outside the refresh family, or stationary certification for the two causal
Beta predictors.

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
- **Markov prequential:** audit the deterministic-start Ionescu--Tulcea path
  laws, their mixture under the supplied finite-state initial PMF, point-mass
  recovery, fixed predictor catalog, full-support finite tilt prior, post-path
  atom-selection semantics, conditional-risk identity, conditional centering,
  and the `1/4` second-moment step. Keep the pointwise selector separate from
  optional stopping, and keep encountered conditional prequential risk
  separate from stationary risk.
- **Known-kernel stationary Poisson:** audit the PMF invariance identity, TV
  normalization, oscillation-contraction convention, finite-depth potential,
  telescoping correction, residual and span constants, confidence allocation,
  logarithmic depth, and exact vanishing-width proof. Keep the truncated
  potential distinct from an exact infinite-series Poisson solution and from an
  invariant-law existence theorem.
- **Unknown-kernel stationary catalog:** audit visit/edge indexing, coordinate
  complement orientation, normalization by positive visit mass, every-row-visited
  premise, row-TV summation, candidate selection timing, the `+ 2 * eta`
  conversion, the two confidence budgets, the canonical noncomputable invariant
  target, and the conditional uniqueness branch. The current informative checker
  does not exercise the transition-confidence event; that combined-event receipt
  remains **UNSWEPT**.
