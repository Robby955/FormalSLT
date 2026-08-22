import FormalSLT.Applications.ControlledQueueSharpStructuredOPE
import Mathlib.Tactic.MinImports

open Lean Elab Command
open FormalSLT.AnytimeValid
open FormalSLT.StochasticDynamics
open FormalSLT.Applications.ControlledQueue
open FormalSLT.Applications.ControlledQueueData

/-! Core reusable declarations introduced by the sharp structured slice. -/

#check forwardEmpiricalBernsteinPsi_le_quadratic
#check finiteOscillation_add_const_mul_le
#check abs_approximateTargetPolicyPoissonResidual_le_affineDrift

#print axioms forwardEmpiricalBernsteinPsi_le_quadratic
#print axioms finiteOscillation_add_const_mul_le
#print axioms abs_approximateTargetPolicyPoissonResidual_le_affineDrift

/-! Exact refresh-family sensitivity bridge. -/

#check refreshTargetPolicyPoissonDriftSensitivity
#check targetPolicyPoissonDrift_refresh_sub_candidate_eq
#check abs_approximateTargetPolicyPoissonResidual_le_refreshSensitivity

#print axioms targetPolicyPoissonDrift_refresh_sub_candidate_eq
#print axioms abs_approximateTargetPolicyPoissonResidual_le_refreshSensitivity

/-! Frozen sharp structured receipt declarations. -/

#check sharpStructuredPersistenceTilt
#check sharpStructuredPersistenceTiltWeight
#check sharpStructuredPersistenceFailureBudget
#check sharpSelectedCandidateDriftOscillation
#check sharpSelectedRefreshSensitivityOscillation
#check sharpStructuredPersistenceBudget
#check sharpStructuredResidual
#check sharpStructuredOPEBoundary
#check sharpStructuredTruePersistence
#check sharpStructuredInitial
#check sharpStructuredHorizon
#check sharpStructuredTruePersistence_apply
#check sharpStructuredInitial_eq
#check sharpStructuredPersistenceTiltWeight_isFullSupport
#check sharpStructuredPersistenceTilt_pos
#check sharpStructuredPersistenceTilt_lt_one
#check sharpStructuredPersistenceFailureBudget_pos
#check knownKernelRiskTilt_psi_le_one_fourEighty
#check sharpStructuredPersistenceTilt_psi_le_one_eightThousandSixtyFour
#check knownKernelSelectedCandidateDrift_finiteOscillation_le
#check knownKernelSelectedRefreshSensitivity_finiteOscillation_le
#check exists_controlledQueueSharpStructuredOPE_event
#check exists_controlledQueueSharpStructuredReceipt_event

#print axioms sharpStructuredTruePersistence_apply
#print axioms sharpStructuredInitial_eq
#print axioms sharpStructuredPersistenceTiltWeight_isFullSupport
#print axioms sharpStructuredPersistenceTilt_pos
#print axioms sharpStructuredPersistenceTilt_lt_one
#print axioms sharpStructuredPersistenceFailureBudget_pos
#print axioms knownKernelRiskTilt_psi_le_one_fourEighty
#print axioms sharpStructuredPersistenceTilt_psi_le_one_eightThousandSixtyFour
#print axioms knownKernelSelectedCandidateDrift_finiteOscillation_le
#print axioms knownKernelSelectedRefreshSensitivity_finiteOscillation_le
#print axioms exists_controlledQueueSharpStructuredOPE_event
#print axioms exists_controlledQueueSharpStructuredReceipt_event

/-! The sharp candidate-drift certificate must not recover its oscillation
through the exact invariant law or exact stationary-risk receipt. -/

run_cmd do
  let decl : Name :=
    ``FormalSLT.Applications.ControlledQueue.knownKernelSelectedCandidateDrift_finiteOscillation_le
  let dependencies ← liftCoreM decl.transitivelyUsedConstants
  let forbidden : Array Name := #[
    ``FormalSLT.Applications.ControlledQueue.knownKernelSelectedResidual,
    ``FormalSLT.Applications.ControlledQueue.knownKernelSelectedPotential_residual_eq,
    ``FormalSLT.Applications.ControlledQueue.queueThreshold_nominalModelOverload_stationaryRisk,
    ``FormalSLT.Applications.ControlledQueue.queueThreshold_nominalModelOverload_catalogStationaryRisk,
    ``FormalSLT.Applications.ControlledQueue.knownKernelSelectedPosteriorRisk_eq,
    ``FormalSLT.Applications.ControlledQueue.queueThresholdStationaryLaw,
    ``FormalSLT.Applications.ControlledQueue.queueThresholdStationaryLaw_isInvariant,
    ``FormalSLT.Applications.ControlledQueue.queueThresholdStationaryLaw_eq_catalogStationary,
    ``FormalSLT.Applications.ControlledQueueKnownKernelReceiptData.selectedStationaryLawTable,
    ``FormalSLT.Applications.ControlledQueueKnownKernelReceiptData.selectedStationaryRisk,
    ``FormalSLT.Applications.ControlledQueueKnownKernelReceiptData.selectedResidualTable,
    ``FormalSLT.StochasticDynamics.approximateTargetPolicyPoissonResidual,
    ``FormalSLT.StochasticDynamics.stationaryTargetPolicyRisk]
  for name in forbidden do
    if dependencies.contains name then
      throwError m!"candidate-drift certificate has forbidden transitive dependency: {name}"

/-! Concrete prospective constants, checked independently of any trace. -/

example :
    (sharpStructuredTruePersistence : ℝ) = 149 / 200 := by
  exact sharpStructuredTruePersistence_apply

example :
    sharpStructuredInitial = ((0 : Action), (0 : PhysicalState)) := by
  exact sharpStructuredInitial_eq

example : sharpStructuredHorizon = 200000 := by
  rfl

example :
    persistenceHitProbability sharpStructuredTruePersistence =
      1209 / 1600 := by
  norm_num [persistenceHitProbability, sharpStructuredTruePersistence]

example :
    candidatePersistenceHitProbability nominalCandidateIndex =
      73 / 96 := by
  norm_num [candidatePersistenceHitProbability,
    candidatePersistenceParameter, nominalCandidateIndex,
    persistenceHitProbability, candidateGamma, candidateGammaRat,
    candidateGammaTable]

example :
    |persistenceHitProbability sharpStructuredTruePersistence -
        candidatePersistenceHitProbability nominalCandidateIndex| =
      23 / 4800 := by
  norm_num [persistenceHitProbability, sharpStructuredTruePersistence,
    candidatePersistenceHitProbability, candidatePersistenceParameter,
    nominalCandidateIndex, candidateGamma, candidateGammaRat,
    candidateGammaTable]
