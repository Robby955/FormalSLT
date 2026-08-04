import FormalSLT.PACBayes

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes
open FormalSLT.PACBayes.IIDContinuousGaussian

#check timeUniformIIDGaussianPACBayes_bound
#check shiftedGaussian_kl_closedForm
#check shiftedGaussian_penalty_evaluated
#check unitHalfLoss_endToEnd_certificate

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
#print axioms shiftedGaussian_penalty_evaluated
#print axioms unitHalfLoss_endToEnd_certificate
