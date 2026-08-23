import FormalSLT.Applications.ControlledQueueFixedRangeComparator
import Mathlib.Tactic.MinImports

open Lean Elab Command
open FormalSLT.Applications.ControlledQueue
open FormalSLT.StochasticDynamics

/-! Reusable fixed-range target-policy OPE interface. -/

#check stationaryTargetPolicyFixedRangeOPEBoundary
#check trajectoryPosteriorAverageConditionalRisk_controlledPoissonScore_eq
#check trajectoryPosteriorEmpiricalPrequentialRisk_controlledPoissonScore_eq
#check exists_stationaryApproximateTargetPolicyFixedRangeOPE_signedResidual_event
#check exists_stationaryApproximateTargetPolicyFixedRangeOPE_event

#print axioms trajectoryPosteriorAverageConditionalRisk_controlledPoissonScore_eq
#print axioms trajectoryPosteriorEmpiricalPrequentialRisk_controlledPoissonScore_eq
#print axioms exists_stationaryApproximateTargetPolicyFixedRangeOPE_signedResidual_event
#print axioms exists_stationaryApproximateTargetPolicyFixedRangeOPE_event

/-! Fixed-range persistence and controlled-queue instantiation. -/

#check fixedRangePersistenceHitBoundary
#check fixedRangePersistenceHitRadius
#check exists_fixedRangePersistenceHitConfidence_event
#check fixedRangeSelectedRiskBoundary
#check fixedRangeStructuredPersistenceBudget
#check fixedRangeStructuredResidual
#check fixedRangeStructuredOPEBoundary
#check exists_controlledQueueFixedRangeComparator_event

#print axioms exists_fixedRangePersistenceHitConfidence_event
#print axioms exists_controlledQueueFixedRangeComparator_event

/-! The final comparator must use the fixed-range trajectory theorem and must
not recover either empirical-Bernstein event through a transitive dependency. -/

run_cmd do
  let decl : Name :=
    ``FormalSLT.Applications.ControlledQueue.exists_controlledQueueFixedRangeComparator_event
  let dependencies ← liftCoreM decl.transitivelyUsedConstants
  let required : Name :=
    ``FormalSLT.StochasticDynamics.trajectoryPACBayes_tiltMixture_prequentialRisk_certificate
  unless dependencies.contains required do
    throwError m!"fixed-range comparator is missing its trajectory PAC-Bayes dependency: {required}"
  let forbidden : Array Name := #[
    ``FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes.exists_forwardPredictableMeanBesselPACBayes_event,
    ``FormalSLT.StochasticDynamics.exists_trajectoryEmpiricalBernsteinPACBayes_event,
    ``FormalSLT.Applications.ControlledQueue.exists_persistenceHitConfidence_event]
  for name in forbidden do
    if dependencies.contains name then
      throwError m!"fixed-range comparator has forbidden empirical-Bernstein dependency: {name}"

example :
    queueRiskFailureBudget + sharpStructuredPersistenceFailureBudget =
      (1 / 20 : ℝ) := by
  norm_num [queueRiskFailureBudget, sharpStructuredPersistenceFailureBudget]

example : knownKernelRiskTilt () = (1 / 16 : ℝ) := by
  rfl

example : sharpStructuredPersistenceTilt () = (1 / 64 : ℝ) := by
  rfl
