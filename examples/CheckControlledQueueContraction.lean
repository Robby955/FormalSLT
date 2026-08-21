import FormalSLT.Applications.ControlledQueueContraction

open ProbabilityTheory

open FormalSLT.Applications.ControlledQueue
open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

#check finitePMFTotalVariation_le_of_common_minorization
#check finiteDobrushinCoefficient_le_of_common_minorization
#check isOscillationContraction_of_finiteDobrushinCoefficient_le
#check candidateGamma
#check candidateRefreshBase
#check candidateRefreshBase_le_candidateKernelTableMass
#check twentyFour_mul_candidateRefreshBase_add_gamma
#check uniformStateReference
#check uniformStateReference_apply_toReal
#check candidateTargetPolicyKernel_common_minorization
#check candidateTargetPolicyKernel_rowTV_le_gamma
#check candidateTargetPolicyKernel_dobrushin_le_gamma
#check candidateTargetPolicyKernel_isOscillationContraction
#check candidateGamma_mem_Ico

#print axioms finitePMFTotalVariation_le_of_common_minorization
#print axioms finiteDobrushinCoefficient_le_of_common_minorization
#print axioms isOscillationContraction_of_finiteDobrushinCoefficient_le
#print axioms candidateRefreshBase_le_candidateKernelTableMass
#print axioms twentyFour_mul_candidateRefreshBase_add_gamma
#print axioms uniformStateReference_apply_toReal
#print axioms candidateTargetPolicyKernel_common_minorization
#print axioms candidateTargetPolicyKernel_rowTV_le_gamma
#print axioms candidateTargetPolicyKernel_dobrushin_le_gamma
#print axioms candidateTargetPolicyKernel_isOscillationContraction
#print axioms candidateGamma_mem_Ico

example : candidateGamma (0 : CandidateIndex) = 5 / 8 := by
  norm_num [candidateGamma, candidateGammaTable]

example : candidateRefreshBase (1 : CandidateIndex) = 1 / 96 := by
  norm_num [candidateRefreshBase, candidateGamma, candidateGammaTable]

example :
    finiteDobrushinCoefficient
        (targetPolicyKernel
          (candidateEnvironment (1 : CandidateIndex))
          (targetPolicy (0 : TargetPolicyIndex))) ≤
      (3 / 4 : ℝ) := by
  simpa [candidateGamma, candidateGammaTable] using
    candidateTargetPolicyKernel_dobrushin_le_gamma
      (1 : CandidateIndex) (targetPolicy (0 : TargetPolicyIndex))
