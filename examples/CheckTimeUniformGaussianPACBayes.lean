import FormalSLT.PACBayes.TimeUniformGaussianPACBayes

/-!
# Time-uniform spherical-Gaussian PAC-Bayes audit

Checks that the explicit closed-form Gaussian failure event agrees with the
abstract continuous PAC-Bayes event and that the end-to-end probability bound
has the repository's standard public axiom set.
-/

open FormalSLT.PACBayes.TimeUniformGaussian

#check @timeUniformSphericalGaussianPACBayesUpperFailure
#check @timeUniformSphericalGaussianPACBayesUpperFailure_eq_continuous
#check @timeUniformSphericalGaussianPACBayes_bound

#print axioms timeUniformSphericalGaussianPACBayesUpperFailure_eq_continuous
#print axioms timeUniformSphericalGaussianPACBayes_bound
