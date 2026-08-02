import FormalSLT.PACBayes.GaussianKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Measure-theoretic Gaussian KL bridge

This module develops the measure-theoretic facts required to identify the
repository's analytic Gaussian KL expression with mathlib's `klDiv`.

It proves equivalence with Lebesgue measure, normalization, and the
Radon--Nikodym derivative against Lebesgue measure for the positive-variance
diagonal and spherical Gaussian measures defined in `GaussianKL.lean`. The
remaining targets are posterior integrability of the proved explicit
log-likelihood-ratio formula and the final `klDiv` closed form.
-/

namespace FormalSLT.PACBayes

open MeasureTheory ProbabilityTheory
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

/-- The logarithm of a one-dimensional Gaussian density ratio is the usual
constant-plus-quadratic expression. -/
theorem log_gaussianCoordinateDensity_ratio
    (posteriorMean posteriorVariance priorMean priorVariance x : ℝ)
    (hposteriorVariance : 0 < posteriorVariance)
    (hpriorVariance : 0 < priorVariance) :
    Real.log
        (gaussianCoordinateDensity posteriorMean posteriorVariance x /
          gaussianCoordinateDensity priorMean priorVariance x) =
      (Real.log (priorVariance / posteriorVariance) +
          (x - priorMean) ^ (2 : Nat) / priorVariance -
          (x - posteriorMean) ^ (2 : Nat) / posteriorVariance) /
        2 := by
  have hcommon : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hposteriorNormalizer :
      0 < Real.sqrt (2 * Real.pi * posteriorVariance) :=
    Real.sqrt_pos.2 (mul_pos hcommon hposteriorVariance)
  have hpriorNormalizer :
      0 < Real.sqrt (2 * Real.pi * priorVariance) :=
    Real.sqrt_pos.2 (mul_pos hcommon hpriorVariance)
  rw [Real.log_div
      (ne_of_gt (gaussianCoordinateDensity_pos posteriorMean
        posteriorVariance x hposteriorVariance))
      (ne_of_gt (gaussianCoordinateDensity_pos priorMean
        priorVariance x hpriorVariance))]
  unfold gaussianCoordinateDensity
  rw [Real.log_mul (inv_ne_zero hposteriorNormalizer.ne')
      (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hpriorNormalizer.ne')
      (Real.exp_ne_zero _),
    Real.log_inv, Real.log_inv, Real.log_exp, Real.log_exp,
    Real.log_sqrt (mul_pos hcommon hposteriorVariance).le,
    Real.log_sqrt (mul_pos hcommon hpriorVariance).le,
    Real.log_mul hcommon.ne' hposteriorVariance.ne',
    Real.log_mul hcommon.ne' hpriorVariance.ne',
    Real.log_div hpriorVariance.ne' hposteriorVariance.ne']
  ring

/-- The logarithm of a diagonal Gaussian density ratio is a finite sum of
coordinatewise constant and quadratic terms. -/
theorem log_diagonalGaussianDensity_ratio_eq_sum {d : ℕ}
    (posterior prior : DiagonalGaussianParams d)
    (x : GaussianParameterSpace d) :
    Real.log (diagonalGaussianDensity posterior x /
        diagonalGaussianDensity prior x) =
      ∑ i, (Real.log (prior.variance i / posterior.variance i) +
          (x i - prior.mean i) ^ (2 : Nat) / prior.variance i -
          (x i - posterior.mean i) ^ (2 : Nat) /
            posterior.variance i) /
        2 := by
  unfold diagonalGaussianDensity
  rw [← Finset.prod_div_distrib]
  rw [Real.log_prod fun i _ =>
    div_ne_zero
      (ne_of_gt (gaussianCoordinateDensity_pos
        (posterior.mean i) (posterior.variance i) (x i)
        (posterior.variance_pos i)))
      (ne_of_gt (gaussianCoordinateDensity_pos
        (prior.mean i) (prior.variance i) (x i)
        (prior.variance_pos i)))]
  exact Finset.sum_congr rfl fun i _ =>
    log_gaussianCoordinateDensity_ratio
      (posterior.mean i) (posterior.variance i)
      (prior.mean i) (prior.variance i) (x i)
      (posterior.variance_pos i) (prior.variance_pos i)

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

/-- Converting the repository's `ENNReal` density back to `ℝ` recovers the
original nonnegative density. -/
@[simp]
theorem diagonalGaussianENNRealDensity_toReal {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) :
    (diagonalGaussianENNRealDensity params x).toReal =
      diagonalGaussianDensity params x := by
  simp [diagonalGaussianENNRealDensity, diagonalGaussianDensity_nonneg]

/-- The Radon--Nikodym derivative of a repository diagonal Gaussian measure
with respect to Lebesgue measure is its defining `ENNReal` density. -/
theorem rnDeriv_diagonalGaussianMeasure_volume {d : ℕ}
    (params : DiagonalGaussianParams d) :
    (diagonalGaussianMeasure params).rnDeriv volume
      =ᵐ[volume] diagonalGaussianENNRealDensity params := by
  exact Measure.rnDeriv_withDensity volume
    (measurable_diagonalGaussianENNRealDensity params)

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

/-- The repository coordinate density agrees with mathlib's normalized Gaussian
density after packaging the positive variance as an `NNReal`. -/
theorem gaussianCoordinateDensity_eq_gaussianPDFReal
    (mean variance x : ℝ) (hvariance : 0 < variance) :
    gaussianCoordinateDensity mean variance x =
      gaussianPDFReal mean ⟨variance, hvariance.le⟩ x := by
  rfl

/-- Each coordinate density is integrable with respect to Lebesgue measure. -/
theorem integrable_gaussianCoordinateDensity
    (mean variance : ℝ) (hvariance : 0 < variance) :
    Integrable (gaussianCoordinateDensity mean variance) := by
  simpa [gaussianCoordinateDensity_eq_gaussianPDFReal mean variance] using
    (integrable_gaussianPDFReal mean ⟨variance, hvariance.le⟩)

/-- Each positive-variance coordinate density integrates to one. -/
theorem integral_gaussianCoordinateDensity_eq_one
    (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫ x, gaussianCoordinateDensity mean variance x = 1 := by
  let v : NNReal := ⟨variance, hvariance.le⟩
  have hv : v ≠ 0 := by
    intro h
    have hcoe : (v : ℝ) = (0 : ℝ) :=
      congrArg (fun x : NNReal => (x : ℝ)) h
    dsimp [v] at hcoe
    exact hvariance.ne' hcoe
  simpa [gaussianCoordinateDensity_eq_gaussianPDFReal mean variance] using
    (integral_gaussianPDFReal_eq_one mean (v := v) hv)

/-- The diagonal Gaussian density integrates to one over finite-dimensional
Lebesgue space. -/
theorem integral_diagonalGaussianDensity_eq_one {d : ℕ}
    (params : DiagonalGaussianParams d) :
    ∫ x, diagonalGaussianDensity params x = 1 := by
  rw [show diagonalGaussianDensity params =
      fun x => ∏ i, gaussianCoordinateDensity
        (params.mean i) (params.variance i) (x i) by rfl]
  rw [integral_fintype_prod_volume_eq_prod]
  have hcoord : ∀ i : Fin d,
      ∫ x, gaussianCoordinateDensity
        (params.mean i) (params.variance i) x = 1 := fun i =>
    integral_gaussianCoordinateDensity_eq_one
      (params.mean i) (params.variance i) (params.variance_pos i)
  simp_rw [hcoord]
  simp

/-- The repository diagonal Gaussian measure has total mass one. -/
theorem diagonalGaussianMeasure_apply_univ {d : ℕ}
    (params : DiagonalGaussianParams d) :
    diagonalGaussianMeasure params Set.univ = 1 := by
  rw [diagonalGaussianMeasure, withDensity_apply' _ Set.univ]
  simp only [Measure.restrict_univ]
  unfold diagonalGaussianENNRealDensity
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_diagonalGaussianDensity_eq_one]
    simp
  · exact
      (Integrable.fintype_prod fun i =>
        integrable_gaussianCoordinateDensity
          (params.mean i) (params.variance i) (params.variance_pos i))
  · exact ae_of_all _ (diagonalGaussianDensity_nonneg params)

/-- Every repository diagonal Gaussian measure is a probability measure. -/
instance instIsProbabilityMeasureDiagonalGaussianMeasure {d : ℕ}
    (params : DiagonalGaussianParams d) :
    IsProbabilityMeasure (diagonalGaussianMeasure params) where
  measure_univ := diagonalGaussianMeasure_apply_univ params

/-- The repository spherical Gaussian measure has total mass one. -/
theorem sphericalGaussianMeasure_apply_univ {d : ℕ}
    (params : SphericalGaussianParams d) :
    sphericalGaussianMeasure params Set.univ = 1 :=
  diagonalGaussianMeasure_apply_univ params.toDiagonal

/-- Every repository spherical Gaussian measure is a probability measure. -/
instance instIsProbabilityMeasureSphericalGaussianMeasure {d : ℕ}
    (params : SphericalGaussianParams d) :
    IsProbabilityMeasure (sphericalGaussianMeasure params) where
  measure_univ := sphericalGaussianMeasure_apply_univ params

/-- The Radon--Nikodym derivative between two repository diagonal Gaussian
measures is the ratio of their Lebesgue densities, almost everywhere under the
prior. -/
theorem rnDeriv_diagonalGaussianMeasure_eq_density_ratio {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    (diagonalGaussianMeasure posterior).rnDeriv
        (diagonalGaussianMeasure prior)
      =ᵐ[diagonalGaussianMeasure prior]
        fun x => diagonalGaussianENNRealDensity posterior x /
          diagonalGaussianENNRealDensity prior x := by
  have hpriorVolume : diagonalGaussianMeasure prior ≪ volume :=
    diagonalGaussianMeasure_absolutelyContinuous_volume prior
  have hratio := Measure.rnDeriv_eq_div
    (diagonalGaussianMeasure_absolutelyContinuous_volume posterior)
    hpriorVolume
  filter_upwards [hratio,
      hpriorVolume (rnDeriv_diagonalGaussianMeasure_volume posterior),
      hpriorVolume (rnDeriv_diagonalGaussianMeasure_volume prior)] with x
      hxRatio hxPosterior hxPrior
  rw [hxRatio, hxPosterior, hxPrior]

/-- The log-likelihood ratio between two repository diagonal Gaussian measures
is the logarithm of their real-valued density ratio, almost everywhere under
the posterior. -/
theorem llr_diagonalGaussianMeasure_eq_log_density_ratio {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    llr (diagonalGaussianMeasure posterior) (diagonalGaussianMeasure prior)
      =ᵐ[diagonalGaussianMeasure posterior]
        fun x => Real.log (diagonalGaussianDensity posterior x /
          diagonalGaussianDensity prior x) := by
  have hposteriorPrior :
      diagonalGaussianMeasure posterior ≪ diagonalGaussianMeasure prior :=
    (diagonalGaussianMeasure_mutuallyAbsolutelyContinuous posterior prior).1
  filter_upwards [hposteriorPrior
      (rnDeriv_diagonalGaussianMeasure_eq_density_ratio posterior prior)] with
      x hx
  rw [llr, hx, ENNReal.toReal_div,
    diagonalGaussianENNRealDensity_toReal,
    diagonalGaussianENNRealDensity_toReal]

/-- The log-likelihood ratio between two repository diagonal Gaussian measures
has the standard finite coordinate-sum form, almost everywhere under the
posterior. -/
theorem llr_diagonalGaussianMeasure_eq_sum {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    llr (diagonalGaussianMeasure posterior) (diagonalGaussianMeasure prior)
      =ᵐ[diagonalGaussianMeasure posterior]
        fun x => ∑ i,
          (Real.log (prior.variance i / posterior.variance i) +
              (x i - prior.mean i) ^ (2 : Nat) / prior.variance i -
              (x i - posterior.mean i) ^ (2 : Nat) /
                posterior.variance i) /
            2 := by
  filter_upwards
      [llr_diagonalGaussianMeasure_eq_log_density_ratio posterior prior] with
      x hx
  rw [hx, log_diagonalGaussianDensity_ratio_eq_sum posterior prior x]

end

end FormalSLT.PACBayes
