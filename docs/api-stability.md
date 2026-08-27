# Public API stability

Status: compatibility policy for FormalSLT v0.2.0.

## Supported imports

FormalSLT supports four topic imports:

- `FormalSLT.PACBayes`
- `FormalSLT.Sequential`
- `FormalSLT.StochasticDynamics`
- `FormalSLT.VC`

The 19 declarations below are the v0.2 allowlist. The four isolated
files under `examples/stable_imports/` import one topic each and check the
corresponding declaration types and axiom sets. The committed signature
snapshot is normative; prose summaries are not substitutes for Lean theorem
statements.

### PAC-Bayes

- `FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event`
- `FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.exists_continuousForwardPredictableMeanBesselPACBayes_event`
- `FormalSLT.PACBayes.ForwardBesselPACBayesCountable.exists_countableForwardBesselPACBayes_event`
- `FormalSLT.PACBayes.ForwardBesselPACBayesCountable.exists_geometricForwardBesselPACBayes_allTime_vanishing_event`
- `FormalSLT.PACBayes.TimeUniform.timeUniformPACBayes_tiltMixture_allPosteriors_bound`

### Sequential inference

- `FormalSLT.AnytimeValid.eProcess_typeI_control`
- `FormalSLT.AnytimeValid.exists_forwardEmpiricalBernsteinLowerTiltCatalog_selected_event`
- `FormalSLT.AnytimeValid.SelectionCost.selectedWeightedScore_expectation_le_one`
- `FormalSLT.AnytimeValid.AllocationLogLog.frequently_geometricEpoch_loglogCost`
- `FormalSLT.AnytimeValid.UniversalBoundaryLowerBound.fairSign_anytimeBoundary_frequently_ge_mul_sqrt`

### Stochastic dynamics

- `FormalSLT.StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event`
- `FormalSLT.StochasticDynamics.exists_stationaryPoissonDepthSelection_allTime_vanishing_event`
- `FormalSLT.StochasticDynamics.exists_selectedCanonicalEmpiricalStationaryCatalog_event`
- `FormalSLT.StochasticDynamics.exists_stationaryTargetPolicyOPE_event`
- `FormalSLT.StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event`
- `FormalSLT.StochasticDynamics.markovPACBayes_tiltMixture_prequentialRisk_certificate_initialLaw`

### VC theory

- `FormalSLT.VC.VCDimension.sauerShelahFiniteSetFamily`
- `FormalSLT.VC.VCRademacher.empiricalRademacherComplexity_le_massart_effective`
- `FormalSLT.VC.VCSampleComplexity.vc_erm_excessRisk_tail`

For patch releases in the v0.2.x line, supported import paths and allowlisted
declaration names and types will remain source compatible. Their public axiom
set will not expand beyond `propext`, `Classical.choice`, and `Quot.sound`.
Proof bodies and internal import structure may change.

The root `FormalSLT` import remains a convenience umbrella, but its complete
transitive namespace is not frozen. Individual implementation modules and
declarations outside the allowlist remain usable but are not covered by this
compatibility promise.

## Current `main` additions

The following endpoints are imported by the supported topic umbrellas on
`main`, but were merged after the `v0.2.0` tag. They are therefore not part of
the 19-declaration v0.2 compatibility allowlist above. This separation keeps
the tagged release record exact while making the current research surface
discoverable.

### Sequential inference

- `FormalSLT.AnytimeValid.wealthWeightedBet_eProcess_of_positive_factors`
- `FormalSLT.AnytimeValid.countableSleepingMasterBet_eProcess`
- `FormalSLT.AnytimeValid.countableSleepingMaster_logWealth_regret_le`

### PAC-Bayes

- `FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes.exists_forwardPredictableStrategyPACBayes_shared_constantMean_factorized_ordinaryRisk_event`
- `FormalSLT.PACBayes.ForwardPredictableStrategyPACBayesCountable.exists_countableForwardPredictableStrategyPACBayes_event`
- `FormalSLT.PACBayes.ForwardPredictableStrategyPACBayesCountable.exists_countableForwardPredictableStrategyPACBayesFinitePrefixOracle_event`
- `FormalSLT.PACBayes.ForwardBesselPACBayesOracle.exists_growingPrefixForwardBesselPACBayesOracle_event`
- `FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesCountable.exists_countableContinuousForwardPredictableMeanBesselPACBayes_event`
- `FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle.exists_continuousGrowingPrefixForwardBesselPACBayesOracle_event`

### Stochastic dynamics

- `FormalSLT.StochasticDynamics.exists_trajectoryGrowingPrefixForwardBesselPACBayesOracle_event`
- `FormalSLT.StochasticDynamics.exists_continuousMeasurableTrajectoryGrowingPrefixForwardBesselPACBayesOracle_event`

The finite product-catalog endpoint permits post-data model and strategy
posteriors and charges separate finite KL terms while returning an ordinary
posterior conditional-risk bound when strategies are shared across models. The
countable strategy master instead selects one atom from a fixed catalog and
charges its declared log-weight cost. The growing-prefix oracle specializes a
geometric tilt catalog to an observable boundary with an explicit LIL-order
envelope. The measurable lift supports arbitrary measurable hypothesis and
trajectory-state spaces and eligible continuous posterior measures. Its width
tends to zero only under the stated pathwise posterior-KL rate. The selected
atom is not an all-real optimizer or a selected e-process, and its exact
real-valued argmin is noncomputable. Separately, the exact wealth-weighted
masters compute over a supplied finite catalog or a dyadically weighted
countable sleeping-expert catalog and compete with every active declared
expert. They do not optimize over a continuum or provide parameter-free
coin-betting.

## Deprecation

A renamed or improved endpoint receives a new canonical declaration. The old
name remains as an alias or theorem-faithful wrapper for the rest of the
current minor release, is marked with Lean's `@[deprecated]` attribute, and is
listed in release notes. A patch release does not remove a supported
declaration.

If a theorem is strengthened, the old theorem type is retained as a corollary;
the old name is not silently redirected to a different statement. Removal may
occur only in a later minor release and must be announced. A correctness
defect may require an immediate documented exception.

## v0.1 compatibility

`examples/CheckV01Usability.lean` preserves the documented June v0.1
quickstart surface. CI also replays the exact Lean examples shipped in the
annotated `v0.1.0` tag against the current library. This is a
source-compatibility guarantee for those published examples, not for every
unlisted internal declaration.

The two historical Bousquet-Elisseeff declarations with `azuma` in their names
are retained as deprecated wrappers with their exact v0.1 theorem types. Their
canonical replacements prove sharper thresholds.

## Verification

From the repository root:

```bash
lake exe cache get
lake build FormalSLT
make api
make downstream
```

`make api` compares the current 19 signatures and axiom reports with the
committed v0.2 snapshot, compares the two deprecated compatibility theorem
types with their own v0.1 snapshot, checks the current showcase and v0.1
quickstart, replays all exact v0.1.0 examples, and requires exact-name parity
across this allowlist, the literature ledger, the theorem map, and the four
isolated import checkers. `make downstream` builds a separate Lake package
that consumes only the four topic imports.
