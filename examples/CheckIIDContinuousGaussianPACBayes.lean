import FormalSLT.PACBayes

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes
open FormalSLT.PACBayes.IIDContinuousGaussian

#check timeUniformIIDGaussianPACBayes_bound
#check exp_iidContinuousScore_eq
#check timeUniformIIDGaussianPACBayesUpperFailure_subset_processFailure
#check FormalSLT.PACBayes.TimeUniformIID.integrable_subGammaExponentialProcess_of_bounded
#check FormalSLT.PACBayes.TimeUniformIID.iIndepFun_indep_comap_natural_of_lt
#check shiftedGaussian_kl_closedForm
#check shiftedGaussian_penalty_evaluated
#check unitSample_iIndep
#check unitHalfLoss_endToEnd_certificate
#check fairBoolLaw_isProbabilityMeasure
#check fairBoolStreamLaw_isProbabilityMeasure
#check gaussianThresholdBoolLoss_of_nonneg
#check gaussianThresholdBoolLoss_of_neg
#check gaussianThresholdBoolLoss_stronglyMeasurable
#check gaussianThresholdBoolLoss_range
#check fairBoolPopulationRisk_eq_half
#check fairBoolCoordinateSample_iIndep
#check fairBoolCoordinateSample_hasLaw
#check gaussianThresholdBoolEmpiricalRisk_allTrue
#check fairBoolGaussianPosteriorPopulationRisk_eq_half
#check fairBoolGaussianPosteriorEmpiricalRisk_allTrue_le_quarter
#check shiftedGaussian_nonvacuityPenalty_evaluated
#check allTrueBoolStream_mem_gaussianPACBayesFailure
#check fairBoolThreshold_endToEnd_certificate

example :
    sphericalGaussianKLClosedForm shiftedGaussianPosterior standardGaussianPrior =
      (1 : ℝ) / 2 :=
  shiftedGaussian_kl_closedForm

example :
    subGammaCgf 1 1 1 / 1 +
        (sphericalGaussianKLClosedForm shiftedGaussianPosterior standardGaussianPrior +
          Real.log (1 / Real.exp (-1))) / ((10 : ℝ) * 1) =
      (9 : ℝ) / 10 :=
  shiftedGaussian_penalty_evaluated

#print axioms timeUniformIIDGaussianPACBayes_bound
#print axioms exp_iidContinuousScore_eq
#print axioms timeUniformIIDGaussianPACBayesUpperFailure_subset_processFailure
#print axioms FormalSLT.PACBayes.TimeUniformIID.integrable_subGammaExponentialProcess_of_bounded
#print axioms FormalSLT.PACBayes.TimeUniformIID.iIndepFun_indep_comap_natural_of_lt
#print axioms shiftedGaussian_penalty_evaluated
#print axioms unitSample_iIndep
#print axioms unitHalfLoss_endToEnd_certificate
#print axioms fairBoolLaw_isProbabilityMeasure
#print axioms fairBoolStreamLaw_isProbabilityMeasure
#print axioms gaussianThresholdBoolLoss_of_nonneg
#print axioms gaussianThresholdBoolLoss_of_neg
#print axioms gaussianThresholdBoolLoss_stronglyMeasurable
#print axioms gaussianThresholdBoolLoss_range
#print axioms fairBoolPopulationRisk_eq_half
#print axioms fairBoolCoordinateSample_iIndep
#print axioms fairBoolCoordinateSample_hasLaw
#print axioms gaussianThresholdBoolEmpiricalRisk_allTrue
#print axioms fairBoolGaussianPosteriorPopulationRisk_eq_half
#print axioms fairBoolGaussianPosteriorEmpiricalRisk_allTrue_le_quarter
#print axioms shiftedGaussian_nonvacuityPenalty_evaluated
#print axioms allTrueBoolStream_mem_gaussianPACBayesFailure
#print axioms fairBoolThreshold_endToEnd_certificate
