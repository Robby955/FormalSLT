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
