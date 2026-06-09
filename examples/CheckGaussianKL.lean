import FormalSLT.PACBayes.GaussianKL

/-!
# Axiom audit for finite-dimensional Gaussian KL
-/

open FormalSLT.PACBayes

noncomputable section

def oneDimGaussianPrior : SphericalGaussianParams 1 where
  mean := fun _ => 0
  variance := 1
  variance_pos := by norm_num

def oneDimGaussianPosterior : SphericalGaussianParams 1 where
  mean := fun _ => 1
  variance := 1
  variance_pos := by norm_num

example :
    sphericalGaussianKL oneDimGaussianPosterior oneDimGaussianPrior =
      (1 : ℝ) / 2 := by
  rw [sphericalGaussianKL_eq_closedForm]
  norm_num [oneDimGaussianPrior, oneDimGaussianPosterior,
    squaredMeanDistance, sphericalGaussianKLClosedForm]

#check @diagonalGaussianMeasure
#check @sphericalGaussianMeasure
#check @diagonalGaussianDensity_nonneg
#check @diagonalGaussianMeasure_absolutelyContinuous_volume
#check @sphericalGaussianMeasure_absolutelyContinuous_volume
#check @diagonalGaussianKL_eq_sum_closedForm
#check @sphericalGaussianKL_eq_closedForm

#print axioms diagonalGaussianDensity_nonneg
#print axioms diagonalGaussianMeasure_absolutelyContinuous_volume
#print axioms diagonalGaussianKL_eq_sum_closedForm
#print axioms sphericalGaussianKL_eq_closedForm

example : True := trivial
