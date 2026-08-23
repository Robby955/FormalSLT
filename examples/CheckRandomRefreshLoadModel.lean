import FormalSLT.Applications.RandomRefreshLoadModel

/-!
# Twenty-state random-refresh load-model checker

This checker exposes the complete model-layer API and audits every public
theorem declaration.  It intentionally contains no long-path or final
statistical application claim.
-/

open FormalSLT.StochasticDynamics
open FormalSLT.StochasticDynamics.RandomRefreshLoadModel

#check State
#check state_card
#check loadLevel
#check regime
#check four_mul_loadLevel_add_regime
#check successorEquiv
#check successor
#check successorEquiv_apply
#check successor_val
#check Candidate
#check candidateGammaNN
#check candidateBaseNN
#check candidateGamma
#check candidateBase
#check twenty_mul_candidateBase_add_gamma
#check refreshKernel
#check refreshKernel_apply_toReal
#check uniformLaw
#check uniformLaw_apply_toReal
#check uniformLaw_invariant
#check refreshKernel_rowTotalVariation
#check refreshKernel_dobrushinCoefficient
#check refreshKernel_dobrushinCoefficient_lt_one
#check nominalCandidateRowTV
#check refreshKernel_nominalCandidateRowTV
#check Predictor
#check overloadIndicator
#check overloadIndicator_eq_one_iff
#check predictorProbability
#check brierScore
#check brierScore_mem_Icc
#check candidateOverloadProbability
#check oracle_is_nominalOverloadProbability
#check brierRowRisk
#check markovRowRisk_brierScore
#check candidateStationaryRiskValue
#check low_stationaryRisk
#check high_stationaryRisk
#check candidate_stationaryRisk
#check nominal_stationaryRisk
#check candidateOscillation
#check brierScore_centeredOscillation_le
#check early_centeredOscillation_eq

#print axioms state_card
#print axioms four_mul_loadLevel_add_regime
#print axioms successorEquiv_apply
#print axioms successor_val
#print axioms twenty_mul_candidateBase_add_gamma
#print axioms refreshKernel_apply_toReal
#print axioms uniformLaw_apply_toReal
#print axioms uniformLaw_invariant
#print axioms refreshKernel_rowTotalVariation
#print axioms refreshKernel_dobrushinCoefficient
#print axioms refreshKernel_dobrushinCoefficient_lt_one
#print axioms refreshKernel_nominalCandidateRowTV
#print axioms brierScore_mem_Icc
#print axioms overloadIndicator_eq_one_iff
#print axioms oracle_is_nominalOverloadProbability
#print axioms markovRowRisk_brierScore
#print axioms low_stationaryRisk
#print axioms high_stationaryRisk
#print axioms candidate_stationaryRisk
#print axioms nominal_stationaryRisk
#print axioms brierScore_centeredOscillation_le
#print axioms early_centeredOscillation_eq
