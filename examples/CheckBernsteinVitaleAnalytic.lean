import FormalSLT.PACBayes.BernsteinBound

/-!
# Axiom audit for analytic Bernstein/Vitale PAC-Bayes widening
-/

open FormalSLT.PACBayes
open FormalSLT.PACBayes.BernsteinAnalytic

#print axioms gaussianGaussianKL_equalVariance_closedForm
#print axioms vitaleContinuousKL_analytic_gaussian_equalVariance
#print axioms vitaleContinuousKL_sphericalGaussian
#print axioms bernstein_iid_bounded_upper_tail
#print axioms bernsteinBound_analytic
#print axioms bernsteinBound_sphericalGaussian

#check @gaussianGaussianKL_equalVariance_closedForm
#check @vitaleContinuousKL_analytic_gaussian_equalVariance
#check @vitaleContinuousKL_sphericalGaussian
#check @bernstein_iid_bounded_upper_tail
#check @bernsteinBound_analytic
#check @bernsteinBound_sphericalGaussian

example : True := trivial
