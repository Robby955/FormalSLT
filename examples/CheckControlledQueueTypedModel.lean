import FormalSLT.Applications.ControlledQueueTypedModel

/-!
# Controlled-queue typed-model receipt

The concrete transition below starts from current observation `(boost, 0)` and
moves to `(eco, 1)`.  The previous action does not select the generated kernel
row: the row is `(state 0, action eco)`, and the nominal candidate assigns it
mass `73/96`.  Uniform behavior contributes the separate factor `1/2`, giving
augmented mass `73/192`.
-/

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueue
open FormalSLT.StochasticDynamics

#check CandidateIndex
#check PolicyIndex
#check TargetPolicyIndex
#check behaviorPolicyIndex
#check targetPolicyTableIndex
#check candidateGammaRat
#check candidateKernelStep
#check candidateKernelStepStateAction
#check candidateKernelTableMass
#check policyTableMass
#check candidateEnvironment
#check queuePolicy
#check behaviorPolicy
#check targetPolicy

#check candidateKernelTableMass_pos
#check candidateKernelStep_stateActionRowEquiv
#check candidateKernelTableMass_eq_refreshMixture
#check candidateKernelTable_eq_massTable
#check candidateKernelTableMass_sum_one
#check policyTableMass_pos
#check policyTableMass_sum_one
#check candidateEnvironment_apply_toReal
#check queuePolicy_apply_toReal
#check behaviorPolicy_apply_toReal
#check targetPolicy_apply_toReal
#check targetPolicy_probability_le_three_halves_behavior
#check candidateEnvironment_transition_apply_toReal
#check augmentedCandidateBehaviorKernel_apply_toReal
#check augmentedBehavior_candidateEnvironment_rowTV_eq_sum
#check environmentRowTV_candidate_le_two_mul_augmentedRowTV

#print axioms candidateKernelTableMass_pos
#print axioms candidateKernelStep_stateActionRowEquiv
#print axioms candidateKernelTableMass_eq_refreshMixture
#print axioms candidateKernelTable_eq_massTable
#print axioms candidateKernelTableMass_sum_one
#print axioms policyTableMass_pos
#print axioms policyTableMass_sum_one
#print axioms candidateEnvironment_apply_toReal
#print axioms queuePolicy_apply_toReal
#print axioms behaviorPolicy_apply_toReal
#print axioms targetPolicy_apply_toReal
#print axioms targetPolicy_probability_le_three_halves_behavior
#print axioms candidateEnvironment_transition_apply_toReal
#print axioms augmentedCandidateBehaviorKernel_apply_toReal
#print axioms augmentedBehavior_candidateEnvironment_rowTV_eq_sum
#print axioms environmentRowTV_candidate_le_two_mul_augmentedRowTV

/-- The nominal candidate's first physical state/action row assigns mass
`73/96` to next state one. -/
theorem nominal_firstRow_nextOne_mass :
    (candidateEnvironment (1 : CandidateIndex)
      (0 : PhysicalState) (0 : Action) (1 : PhysicalState)).toReal =
        (73 / 96 : ℝ) := by
  rw [candidateEnvironment_apply_toReal]
  norm_num [candidateKernelTableMass_eq_refreshMixture, candidateGammaRat,
    candidateKernelStep, candidateGammaTable, candidateKernelStepByRow]

/-- The first generated target is conservative: its boost probability at
state zero is exactly `1/4`. -/
theorem conservative_stateZero_boost_mass :
    (targetPolicy (0 : TargetPolicyIndex)
      (0 : PhysicalState) (1 : Action)).toReal = (1 / 4 : ℝ) := by
  rw [targetPolicy_apply_toReal]
  norm_num [targetPolicyTableIndex, policyTableMass, policyTable]

/-- The action-major augmented transition mass is the behavior half times the
candidate environment mass. -/
theorem nominal_augmented_transition_mass :
    (augmentedBehaviorKernel
      (candidateEnvironment (1 : CandidateIndex)) behaviorPolicy
      ((1 : Action), (0 : PhysicalState))
      ((0 : Action), (1 : PhysicalState))).toReal = (73 / 192 : ℝ) := by
  rw [augmentedBehaviorKernel_apply, ENNReal.toReal_mul,
    behaviorPolicy_apply_toReal, nominal_firstRow_nextOne_mass]
  norm_num

#check nominal_firstRow_nextOne_mass
#check conservative_stateZero_boost_mass
#check nominal_augmented_transition_mass

#print axioms nominal_firstRow_nextOne_mass
#print axioms conservative_stateZero_boost_mass
#print axioms nominal_augmented_transition_mass
