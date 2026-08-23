import FormalSLT.Applications.ControlledQueueOPECatalog

open FormalSLT.Applications.ControlledQueue

#check QueueHypothesis
#check nominalCandidateIndex
#check nominalCandidateEnvironment
#check queueHypothesisTargetPolicy
#check queueHypothesisScore
#check queueHypothesisStationary
#check queueHypothesisReference
#check queueHypothesisPrior
#check queueTransitionPrior
#check queueRiskTiltWeight
#check queueTransitionTiltWeight
#check queueRiskTilt
#check queueTransitionTilt
#check queueRiskFailureBudget
#check queueTransitionFailureBudget
#check queueHypothesisFiniteDepthPotential
#check queueEmpiricalKernelTVBudget
#check queueEmpiricalFiniteDepthOPEBoundary
#check queueEmpiricalFiniteDepthResidual
#check nominalCandidateGamma_eq_three_fourths
#check queueHypothesis_card
#check queueHypothesisPrior_apply
#check queueTransitionCoordinate_card
#check queueTransitionPrior_apply
#check queueHypothesisPrior_isFullSupport
#check queueTransitionPrior_isFullSupport
#check queueRiskTiltWeight_isFullSupport
#check queueTransitionTiltWeight_isFullSupport
#check queueRiskTilt_pos
#check queueRiskTilt_lt_one
#check queueTransitionTilt_pos
#check queueTransitionTilt_lt_one
#check queueRiskFailureBudget_pos
#check queueTransitionFailureBudget_pos
#check queueHypothesisStationary_isInvariant
#check queueHypothesisStationary_unique_of_refresh
#check queueHypothesisScore_mem_Icc
#check queueHypothesis_nominal_isOscillationContraction
#check queueHypothesis_nominal_centeredRowRiskOscillation_le_one
#check queueHypothesis_overlap
#check queueHypothesis_ratioBound_three_halves
#check exists_nominalControlledQueueEmpiricalFiniteDepthOPE_event

#print axioms nominalCandidateGamma_eq_three_fourths
#print axioms queueHypothesis_card
#print axioms queueHypothesisPrior_apply
#print axioms queueTransitionCoordinate_card
#print axioms queueTransitionPrior_apply
#print axioms queueHypothesisPrior_isFullSupport
#print axioms queueTransitionPrior_isFullSupport
#print axioms queueRiskTiltWeight_isFullSupport
#print axioms queueTransitionTiltWeight_isFullSupport
#print axioms queueRiskTilt_pos
#print axioms queueRiskTilt_lt_one
#print axioms queueTransitionTilt_pos
#print axioms queueTransitionTilt_lt_one
#print axioms queueRiskFailureBudget_pos
#print axioms queueTransitionFailureBudget_pos
#print axioms queueHypothesisStationary_isInvariant
#print axioms queueHypothesisStationary_unique_of_refresh
#print axioms queueHypothesisScore_mem_Icc
#print axioms queueHypothesis_nominal_isOscillationContraction
#print axioms queueHypothesis_nominal_centeredRowRiskOscillation_le_one
#print axioms queueHypothesis_overlap
#print axioms queueHypothesis_ratioBound_three_halves
#print axioms exists_nominalControlledQueueEmpiricalFiniteDepthOPE_event

example : Fintype.card QueueHypothesis = 12 := by
  exact queueHypothesis_card

example :
    queueHypothesisPrior
        ((0 : TargetPolicyIndex), (0 : FixedPredictorIndex)) =
      (1 / 12 : ℝ) := by
  simp

example :
    queueRiskFailureBudget + queueTransitionFailureBudget =
      (1 / 20 : ℝ) := by
  norm_num [queueRiskFailureBudget, queueTransitionFailureBudget]

example (coordinate :
    FormalSLT.StochasticDynamics.TransitionCoordinate Observation) :
    queueTransitionPrior coordinate = (1 / 4608 : ℝ) := by
  simp
