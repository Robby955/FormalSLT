import FormalSLT.Applications.RandomRefreshLoadCertificate

/-!
# Twenty-state random-refresh certificate checker

This checker audits the application configuration and its shared event with
complement real outer mass at most `1/20`. It does not claim measurability of
the event or membership of a named path.
-/

open FormalSLT.StochasticDynamics.RandomRefreshLoadModel

#check candidateReference
#check candidateWeight
#check predictorPrior
#check transitionPrior
#check transitionWeight
#check transitionTilt
#check riskFailureBudget
#check transitionFailureBudget
#check selectCandidate
#check selectDepth
#check selectRiskTilt
#check selectTransitionTilt
#check oraclePosterior
#check selectPosterior
#check selectedEmpiricalKernelTVBudget
#check selectedKnownKernelBoundary
#check selectedUnknownKernelBoundary
#check candidateWeight_isFullSupport
#check predictorPrior_isFullSupport
#check transitionPrior_isFullSupport
#check transitionWeight_isFullSupport
#check transitionTilt_pos
#check transitionTilt_lt_one
#check riskFailureBudget_pos
#check transitionFailureBudget_pos
#check candidateOscillation_nonneg
#check selectPosterior_isPMF
#check exists_randomRefreshLoad_selected_event
#check exists_randomRefreshLoad_matched_event

#print axioms candidateWeight_isFullSupport
#print axioms predictorPrior_isFullSupport
#print axioms transitionPrior_isFullSupport
#print axioms transitionWeight_isFullSupport
#print axioms transitionTilt_pos
#print axioms transitionTilt_lt_one
#print axioms riskFailureBudget_pos
#print axioms transitionFailureBudget_pos
#print axioms candidateOscillation_nonneg
#print axioms selectPosterior_isPMF
#print axioms exists_randomRefreshLoad_selected_event
#print axioms exists_randomRefreshLoad_matched_event
