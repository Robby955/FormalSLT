import FormalSLT.PACBayes.GaussianKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-!
# Measure-theoretic Gaussian KL bridge

This module develops the measure-theoretic facts required to identify the
repository's analytic Gaussian KL expression with mathlib's `klDiv`.

The first completed slice proves that every positive-variance diagonal or
spherical Gaussian measure defined in `GaussianKL.lean` is equivalent to
Lebesgue measure. Consequently any two such Gaussian measures are mutually
absolutely continuous. This discharges the absolute-continuity premise in the
continuous PAC-Bayes theorem without assuming it as an external certificate.

Normalization, log-likelihood-ratio integrability, and the final `klDiv`
closed-form identity remain separate targets.
-/

namespace FormalSLT.PACBayes

open MeasureTheory
open Finset Real BigOperators
open scoped ENNReal

noncomputable section

/-- A positive-variance one-dimensional Gaussian density is strictly positive. -/
theorem gaussianCoordinateDensity_pos
    (mean variance x : ℝ) (hvariance : 0 < variance) :
    0 < gaussianCoordinateDensity mean variance x := by
  unfold gaussianCoordinateDensity
  have hnormalizer : 0 < Real.sqrt (2 * Real.pi * variance) := by
    apply Real.sqrt_pos.2
    positivity
  exact mul_pos (inv_pos.mpr hnormalizer) (Real.exp_pos _)

/-- The diagonal Gaussian density is strictly positive everywhere. -/
theorem diagonalGaussianDensity_pos {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) :
    0 < diagonalGaussianDensity params x := by
  unfold diagonalGaussianDensity
  exact Finset.prod_pos fun i _ =>
    gaussianCoordinateDensity_pos
      (params.mean i) (params.variance i) (x i) (params.variance_pos i)

/-- The real-valued diagonal Gaussian density is measurable. -/
theorem measurable_diagonalGaussianDensity {d : ℕ}
    (params : DiagonalGaussianParams d) :
    Measurable (diagonalGaussianDensity params) := by
  unfold diagonalGaussianDensity gaussianCoordinateDensity
  fun_prop

/-- The `ENNReal`-valued diagonal Gaussian density is measurable. -/
theorem measurable_diagonalGaussianENNRealDensity {d : ℕ}
    (params : DiagonalGaussianParams d) :
    Measurable (diagonalGaussianENNRealDensity params) := by
  unfold diagonalGaussianENNRealDensity
  exact ENNReal.measurable_ofReal.comp
    (measurable_diagonalGaussianDensity params)

/-- Lebesgue measure is absolutely continuous with respect to a positive-variance
repository diagonal Gaussian measure. -/
theorem volume_absolutelyContinuous_diagonalGaussianMeasure {d : ℕ}
    (params : DiagonalGaussianParams d) :
    volume ≪ diagonalGaussianMeasure params := by
  unfold diagonalGaussianMeasure
  apply withDensity_absolutelyContinuous'
  · exact (measurable_diagonalGaussianENNRealDensity params).aemeasurable
  · filter_upwards with x
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (diagonalGaussianDensity_pos params x))

/-- A repository diagonal Gaussian measure and Lebesgue measure are mutually
absolutely continuous. -/
theorem diagonalGaussianMeasure_mutuallyAbsolutelyContinuous_volume {d : ℕ}
    (params : DiagonalGaussianParams d) :
    diagonalGaussianMeasure params ≪ volume ∧
      volume ≪ diagonalGaussianMeasure params :=
  ⟨diagonalGaussianMeasure_absolutelyContinuous_volume params,
    volume_absolutelyContinuous_diagonalGaussianMeasure params⟩

/-- Lebesgue measure is absolutely continuous with respect to a positive-variance
repository spherical Gaussian measure. -/
theorem volume_absolutelyContinuous_sphericalGaussianMeasure {d : ℕ}
    (params : SphericalGaussianParams d) :
    volume ≪ sphericalGaussianMeasure params := by
  exact volume_absolutelyContinuous_diagonalGaussianMeasure params.toDiagonal

/-- A repository spherical Gaussian measure and Lebesgue measure are mutually
absolutely continuous. -/
theorem sphericalGaussianMeasure_mutuallyAbsolutelyContinuous_volume {d : ℕ}
    (params : SphericalGaussianParams d) :
    sphericalGaussianMeasure params ≪ volume ∧
      volume ≪ sphericalGaussianMeasure params :=
  ⟨sphericalGaussianMeasure_absolutelyContinuous_volume params,
    volume_absolutelyContinuous_sphericalGaussianMeasure params⟩

/-- Any two positive-variance repository diagonal Gaussian measures are mutually
absolutely continuous. -/
theorem diagonalGaussianMeasure_mutuallyAbsolutelyContinuous {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    diagonalGaussianMeasure posterior ≪ diagonalGaussianMeasure prior ∧
      diagonalGaussianMeasure prior ≪ diagonalGaussianMeasure posterior := by
  constructor
  · exact (diagonalGaussianMeasure_absolutelyContinuous_volume posterior).trans
      (volume_absolutelyContinuous_diagonalGaussianMeasure prior)
  · exact (diagonalGaussianMeasure_absolutelyContinuous_volume prior).trans
      (volume_absolutelyContinuous_diagonalGaussianMeasure posterior)

/-- Any two positive-variance repository spherical Gaussian measures are mutually
absolutely continuous. In particular, this supplies the `posterior ≪ prior`
premise needed by continuous PAC-Bayes change of measure. -/
theorem sphericalGaussianMeasure_mutuallyAbsolutelyContinuous {d : ℕ}
    (posterior prior : SphericalGaussianParams d) :
    sphericalGaussianMeasure posterior ≪ sphericalGaussianMeasure prior ∧
      sphericalGaussianMeasure prior ≪ sphericalGaussianMeasure posterior := by
  exact diagonalGaussianMeasure_mutuallyAbsolutelyContinuous
    posterior.toDiagonal prior.toDiagonal

/-- Directed absolute continuity from posterior to prior for spherical Gaussian
measures, provided as the form consumed directly by PAC-Bayes theorems. -/
theorem sphericalGaussianMeasure_absolutelyContinuous {d : ℕ}
    (posterior prior : SphericalGaussianParams d) :
    sphericalGaussianMeasure posterior ≪ sphericalGaussianMeasure prior :=
  (sphericalGaussianMeasure_mutuallyAbsolutelyContinuous posterior prior).1

end

end FormalSLT.PACBayes
