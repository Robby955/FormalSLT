import FormalSLT.PACBayes.BernsteinBound
import FormalSLT.PACBayes.GaussianKL

/-!
# Gaussian posterior numerical certificate

This file is a reproducible worked certificate for a one-dimensional Gaussian
prior/posterior pair. The Gaussian KL value is derived from the finite-
dimensional Gaussian measure backend rather than supplied as an integer-only
KL certificate.
-/

namespace FormalSLT.Examples.GaussianPosteriorCertificate

open FormalSLT.PACBayes

noncomputable section

def sampleSize : Int := 1000

def gaussianPrior : SphericalGaussianParams 1 where
  mean := fun _ => 0
  variance := 1
  variance_pos := by norm_num

def gaussianPosterior : SphericalGaussianParams 1 where
  mean := fun _ => 1
  variance := 1
  variance_pos := by norm_num

def gaussianPosteriorKL : ℝ :=
  sphericalGaussianKL gaussianPosterior gaussianPrior

def varianceNumerator : Int := 25

def complexityNumerator : Int := 40

def empiricalRiskNumerator : Int := 120

def bernsteinBoundNumerator : Int := 200

/-- Closed-form KL value for the worked equal-variance Gaussian posterior. -/
theorem gaussianPosterior_kl_eq :
    gaussianPosteriorKL = (1 : ℝ) / 2 := by
  rw [gaussianPosteriorKL, sphericalGaussianKL_eq_closedForm]
  norm_num [gaussianPrior, gaussianPosterior, squaredMeanDistance,
    sphericalGaussianKLClosedForm]

/-- The Gaussian KL value fits inside the displayed complexity budget. -/
theorem gaussianPosterior_kl_within_complexity :
    gaussianPosteriorKL ≤ (complexityNumerator : ℝ) := by
  rw [gaussianPosterior_kl_eq]
  norm_num [complexityNumerator]

/-- Arithmetic certificate for the displayed Bernstein PAC-Bayes upper side. -/
theorem gaussianPosterior_bernstein_certificate :
    empiricalRiskNumerator + varianceNumerator + complexityNumerator ≤
      bernsteinBoundNumerator := by
  norm_num [empiricalRiskNumerator, varianceNumerator, complexityNumerator,
    bernsteinBoundNumerator]

#eval empiricalRiskNumerator + varianceNumerator + complexityNumerator
#eval bernsteinBoundNumerator

#check @FormalSLT.PACBayes.sphericalGaussianKL_eq_closedForm
#check @FormalSLT.PACBayes.bernsteinPACBayes_continuousPriorPosterior_certificate

end

end FormalSLT.Examples.GaussianPosteriorCertificate
