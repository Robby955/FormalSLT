import FormalSLT.PACBayes.GaussianKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Measure-theoretic Gaussian KL bridge

This module develops the measure-theoretic facts required to identify the
repository's analytic Gaussian KL expression with mathlib's `klDiv`.

It proves equivalence with Lebesgue measure, normalization, the explicit
log-likelihood ratio and its integrability, and identifies mathlib's `klDiv`
with the repository's closed-form KL expression for the positive-variance
diagonal and spherical Gaussian measures defined in `GaussianKL.lean`.
-/

namespace FormalSLT.PACBayes

open MeasureTheory ProbabilityTheory
open Finset Real BigOperators
open scoped ENNReal

noncomputable section

/-- Packaging a positive real as an `NNReal` yields a nonzero value. -/
private theorem nnrealOfPos_ne_zero {variance : ℝ}
    (hvariance : 0 < variance) :
    (⟨variance, hvariance.le⟩ : NNReal) ≠ 0 := by
  intro hzero
  have hcoe := congrArg (fun v : NNReal => (v : ℝ)) hzero
  change variance = 0 at hcoe
  exact hvariance.ne' hcoe

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
  rw [gaussianPDFReal_def]
  rfl

/-- Each coordinate density is integrable with respect to Lebesgue measure. -/
theorem integrable_gaussianCoordinateDensity
    (mean variance : ℝ) (hvariance : 0 < variance) :
    Integrable (gaussianCoordinateDensity mean variance) := by
  have hfun : gaussianCoordinateDensity mean variance =
      gaussianPDFReal mean ⟨variance, hvariance.le⟩ := by
    funext x
    exact gaussianCoordinateDensity_eq_gaussianPDFReal mean variance x hvariance
  rw [hfun]
  exact integrable_gaussianPDFReal mean ⟨variance, hvariance.le⟩

/-- A coordinate Gaussian density times any shifted square is integrable with
respect to Lebesgue measure. -/
theorem integrable_gaussianCoordinateDensity_mul_sq_sub
    (mean variance center : ℝ) (hvariance : 0 < variance) :
    Integrable (fun x => gaussianCoordinateDensity mean variance x *
      (x - center) ^ (2 : Nat)) := by
  let v : NNReal := ⟨variance, hvariance.le⟩
  have hv : v ≠ 0 := nnrealOfPos_ne_zero hvariance
  have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal mean v) :=
    memLp_of_mem_interior_integrableExpSet (by simp) 2
  have hshift : MemLp (fun x : ℝ => x - center) 2
      (gaussianReal mean v) :=
    hmem.sub (memLp_const center)
  have hint : Integrable (fun x : ℝ => (x - center) ^ (2 : Nat))
      (gaussianReal mean v) := hshift.integrable_sq
  rw [gaussianReal_of_var_ne_zero mean hv,
    integrable_withDensity_iff (measurable_gaussianPDF mean v)
      (ae_of_all _ fun x => gaussianPDF_lt_top)] at hint
  have hfun : (fun x : ℝ => gaussianCoordinateDensity mean variance x *
      (x - center) ^ (2 : Nat)) =
      fun x => (x - center) ^ (2 : Nat) * gaussianPDFReal mean v x := by
    funext x
    rw [gaussianCoordinateDensity_eq_gaussianPDFReal mean variance x hvariance]
    simp only [v, mul_comm]
  rw [hfun]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using hint

/-- The weighted shifted-square moment of a one-dimensional repository
Gaussian density is its variance plus squared displacement from the mean. -/
theorem integral_gaussianCoordinateDensity_mul_sq_sub
    (mean variance center : ℝ) (hvariance : 0 < variance) :
    ∫ x, gaussianCoordinateDensity mean variance x *
        (x - center) ^ (2 : Nat) =
      variance + (mean - center) ^ (2 : Nat) := by
  let v : NNReal := ⟨variance, hvariance.le⟩
  have hv : v ≠ 0 := nnrealOfPos_ne_zero hvariance
  have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal mean v) :=
    memLp_of_mem_interior_integrableExpSet (by simp) 2
  have hid : Integrable (fun x : ℝ => x) (gaussianReal mean v) :=
    hmem.integrable one_le_two
  have hsq : Integrable (fun x : ℝ => x ^ (2 : Nat))
      (gaussianReal mean v) := hmem.integrable_sq
  have hx2 : ∫ x : ℝ, x ^ (2 : Nat) ∂gaussianReal mean v =
      (v : ℝ) + mean ^ (2 : Nat) := by
    have hvar := variance_eq_sub hmem
    rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at hvar
    have hvar' : (v : ℝ) =
        (∫ x : ℝ, x ^ (2 : Nat) ∂gaussianReal mean v) -
          mean ^ (2 : Nat) := by
      simpa [Pi.pow_apply] using hvar
    linarith
  have hshift : ∫ x : ℝ, (x - center) ^ (2 : Nat)
        ∂gaussianReal mean v =
      (v : ℝ) + (mean - center) ^ (2 : Nat) := by
    calc
      ∫ x : ℝ, (x - center) ^ (2 : Nat) ∂gaussianReal mean v =
          ∫ x : ℝ, (x ^ (2 : Nat) - (2 * center) * x) +
            center ^ (2 : Nat) ∂gaussianReal mean v := by
              apply integral_congr_ae
              filter_upwards with x
              ring
      _ = (∫ x : ℝ, x ^ (2 : Nat) - (2 * center) * x
              ∂gaussianReal mean v) +
            ∫ _x : ℝ, center ^ (2 : Nat) ∂gaussianReal mean v := by
              exact integral_add (hsq.sub (hid.const_mul (2 * center)))
                (integrable_const _)
      _ = ((∫ x : ℝ, x ^ (2 : Nat) ∂gaussianReal mean v) -
            ∫ x : ℝ, (2 * center) * x ∂gaussianReal mean v) +
            ∫ _x : ℝ, center ^ (2 : Nat) ∂gaussianReal mean v := by
              rw [integral_sub hsq (hid.const_mul (2 * center))]
      _ = (∫ x : ℝ, x ^ (2 : Nat) ∂gaussianReal mean v) -
            (2 * center) *
              (∫ x : ℝ, x ∂gaussianReal mean v) +
            center ^ (2 : Nat) := by
              rw [integral_const_mul, integral_const]
              simp
      _ = (v : ℝ) + (mean - center) ^ (2 : Nat) := by
            rw [hx2, integral_id_gaussianReal]
            ring
  rw [integral_gaussianReal_eq_integral_smul hv] at hshift
  have hfun : (fun x : ℝ => gaussianCoordinateDensity mean variance x *
      (x - center) ^ (2 : Nat)) =
      fun x => gaussianPDFReal mean v x * (x - center) ^ (2 : Nat) := by
    funext x
    rw [gaussianCoordinateDensity_eq_gaussianPDFReal mean variance x hvariance]
  rw [hfun]
  have hvcoe : (v : ℝ) = variance := rfl
  rw [hvcoe] at hshift
  simpa only [smul_eq_mul] using hshift

/-- Each positive-variance coordinate density integrates to one. -/
theorem integral_gaussianCoordinateDensity_eq_one
    (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫ x, gaussianCoordinateDensity mean variance x = 1 := by
  let v : NNReal := ⟨variance, hvariance.le⟩
  have hv : v ≠ 0 := nnrealOfPos_ne_zero hvariance
  have hfun : gaussianCoordinateDensity mean variance = gaussianPDFReal mean v := by
    funext x
    exact gaussianCoordinateDensity_eq_gaussianPDFReal mean variance x hvariance
  rw [hfun]
  exact integral_gaussianPDFReal_eq_one mean (v := v) hv

/-- Multiplying a diagonal Gaussian density by a shifted square in one
coordinate preserves its separated product form. -/
theorem diagonalGaussianDensity_mul_sq_sub_eq_prod {d : ℕ}
    (params : DiagonalGaussianParams d) (i : Fin d) (center : ℝ)
    (x : GaussianParameterSpace d) :
    diagonalGaussianDensity params x * (x i - center) ^ (2 : Nat) =
      ∏ j, if j = i then
          gaussianCoordinateDensity (params.mean j) (params.variance j) (x j) *
            (x j - center) ^ (2 : Nat)
        else
          gaussianCoordinateDensity (params.mean j) (params.variance j) (x j) := by
  unfold diagonalGaussianDensity
  let f : Fin d → ℝ := fun j =>
    gaussianCoordinateDensity (params.mean j) (params.variance j) (x j)
  let g : Fin d → ℝ := fun j => if j = i then
      gaussianCoordinateDensity (params.mean j) (params.variance j) (x j) *
        (x j - center) ^ (2 : Nat)
    else
      gaussianCoordinateDensity (params.mean j) (params.variance j) (x j)
  change (∏ j, f j) * (x i - center) ^ (2 : Nat) = ∏ j, g j
  calc
    (∏ j, f j) * (x i - center) ^ (2 : Nat) =
        (f i * ∏ j : {j // j ≠ i}, f j) *
          (x i - center) ^ (2 : Nat) := by
            rw [Fintype.prod_eq_mul_prod_subtype_ne f i]
    _ = (f i * (x i - center) ^ (2 : Nat)) *
          ∏ j : {j // j ≠ i}, f j := by ring
    _ = g i * ∏ j : {j // j ≠ i}, g j := by
          congr 1
          · simp [f, g]
          · apply Finset.prod_congr rfl
            intro j _
            simp [f, g, j.property]
    _ = ∏ j, g j :=
      (Fintype.prod_eq_mul_prod_subtype_ne g i).symm

/-- Every shifted coordinate square is integrable under a repository diagonal
Gaussian measure. -/
theorem integrable_sq_sub_coordinate_diagonalGaussianMeasure {d : ℕ}
    (params : DiagonalGaussianParams d) (i : Fin d) (center : ℝ) :
    Integrable (fun x : GaussianParameterSpace d =>
      (x i - center) ^ (2 : Nat)) (diagonalGaussianMeasure params) := by
  rw [diagonalGaussianMeasure,
    integrable_withDensity_iff
      (measurable_diagonalGaussianENNRealDensity params)
      (ae_of_all _ fun x => by
        simp [diagonalGaussianENNRealDensity])]
  have hfactor :
      (fun x : GaussianParameterSpace d =>
        (x i - center) ^ (2 : Nat) *
          (diagonalGaussianENNRealDensity params x).toReal) =
        fun x => ∏ j, if j = i then
            gaussianCoordinateDensity
                (params.mean j) (params.variance j) (x j) *
              (x j - center) ^ (2 : Nat)
          else
            gaussianCoordinateDensity
              (params.mean j) (params.variance j) (x j) := by
    funext x
    rw [diagonalGaussianENNRealDensity_toReal, mul_comm,
      diagonalGaussianDensity_mul_sq_sub_eq_prod params i center x]
  rw [hfactor]
  rw [volume_pi]
  exact
    (Integrable.fintype_prod
      (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := fun j y => if j = i then
          gaussianCoordinateDensity (params.mean j) (params.variance j) y *
            (y - center) ^ (2 : Nat)
        else
          gaussianCoordinateDensity (params.mean j) (params.variance j) y)
      (fun j => by
        by_cases hji : j = i
        · subst j
          simpa using integrable_gaussianCoordinateDensity_mul_sq_sub
            (params.mean i) (params.variance i) center (params.variance_pos i)
        · simpa [hji] using integrable_gaussianCoordinateDensity
            (params.mean j) (params.variance j) (params.variance_pos j)))

/-- The shifted second moment of one coordinate under a repository diagonal
Gaussian has the expected variance-plus-bias form. -/
theorem integral_sq_sub_coordinate_diagonalGaussianMeasure {d : ℕ}
    (params : DiagonalGaussianParams d) (i : Fin d) (center : ℝ) :
    ∫ x : GaussianParameterSpace d, (x i - center) ^ (2 : Nat)
        ∂diagonalGaussianMeasure params =
      params.variance i + (params.mean i - center) ^ (2 : Nat) := by
  rw [diagonalGaussianMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_diagonalGaussianENNRealDensity params)
      (ae_of_all _ fun x => by
        simp [diagonalGaussianENNRealDensity])]
  simp only [smul_eq_mul, diagonalGaussianENNRealDensity_toReal]
  have hfactor :
      (fun x : GaussianParameterSpace d =>
        diagonalGaussianDensity params x * (x i - center) ^ (2 : Nat)) =
        fun x => ∏ j, if j = i then
            gaussianCoordinateDensity
                (params.mean j) (params.variance j) (x j) *
              (x j - center) ^ (2 : Nat)
          else
            gaussianCoordinateDensity
              (params.mean j) (params.variance j) (x j) := by
    funext x
    exact diagonalGaussianDensity_mul_sq_sub_eq_prod params i center x
  rw [hfactor]
  let f : Fin d → ℝ → ℝ := fun j y => if j = i then
      gaussianCoordinateDensity (params.mean j) (params.variance j) y *
        (y - center) ^ (2 : Nat)
    else
      gaussianCoordinateDensity (params.mean j) (params.variance j) y
  change (∫ x : GaussianParameterSpace d, ∏ j, f j (x j)) = _
  rw [integral_fintype_prod_volume_eq_prod,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun j => ∫ y : ℝ, f j y) i]
  simp only [f, ite_true]
  rw [integral_gaussianCoordinateDensity_mul_sq_sub
    (params.mean i) (params.variance i) center (params.variance_pos i)]
  have hrest :
      ∏ j : {j // j ≠ i},
          ∫ y : ℝ, f j y = 1 := by
    apply Finset.prod_eq_one
    intro j _
    simp only [f, if_neg j.property]
    rw [
      integral_gaussianCoordinateDensity_eq_one
        (params.mean j) (params.variance j) (params.variance_pos j)]
  rw [hrest, mul_one]

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

/-- The log-likelihood ratio between two repository diagonal Gaussian measures
is integrable under the posterior. -/
theorem integrable_llr_diagonalGaussianMeasure {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    Integrable
      (llr (diagonalGaussianMeasure posterior)
        (diagonalGaussianMeasure prior))
      (diagonalGaussianMeasure posterior) := by
  rw [integrable_congr
    (llr_diagonalGaussianMeasure_eq_sum posterior prior)]
  refine integrable_finsetSum Finset.univ ?_
  intro i _
  have hpriorSquare :=
    integrable_sq_sub_coordinate_diagonalGaussianMeasure posterior i
      (prior.mean i)
  have hposteriorSquare :=
    integrable_sq_sub_coordinate_diagonalGaussianMeasure posterior i
      (posterior.mean i)
  exact (((integrable_const _).add
      (hpriorSquare.div_const (prior.variance i))).sub
        (hposteriorSquare.div_const (posterior.variance i))).div_const 2

/-- The posterior expectation of the diagonal Gaussian log-likelihood ratio is
the repository's analytic diagonal Gaussian KL expression. -/
theorem integral_llr_diagonalGaussianMeasure_eq_diagonalGaussianKL {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    ∫ x, llr (diagonalGaussianMeasure posterior)
        (diagonalGaussianMeasure prior) x
        ∂diagonalGaussianMeasure posterior =
      diagonalGaussianKL posterior prior := by
  rw [integral_congr_ae
    (llr_diagonalGaussianMeasure_eq_sum posterior prior)]
  have hterm : ∀ i : Fin d,
      Integrable
        (fun x : GaussianParameterSpace d =>
          (Real.log (prior.variance i / posterior.variance i) +
              (x i - prior.mean i) ^ (2 : Nat) / prior.variance i -
              (x i - posterior.mean i) ^ (2 : Nat) /
                posterior.variance i) /
            2)
        (diagonalGaussianMeasure posterior) := by
    intro i
    have hpriorSquare :=
      integrable_sq_sub_coordinate_diagonalGaussianMeasure posterior i
        (prior.mean i)
    have hposteriorSquare :=
      integrable_sq_sub_coordinate_diagonalGaussianMeasure posterior i
        (posterior.mean i)
    exact (((integrable_const _).add
        (hpriorSquare.div_const (prior.variance i))).sub
          (hposteriorSquare.div_const (posterior.variance i))).div_const 2
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  unfold diagonalGaussianKL
  apply Finset.sum_congr rfl
  intro i _
  have hpriorSquare :=
    integrable_sq_sub_coordinate_diagonalGaussianMeasure posterior i
      (prior.mean i)
  have hposteriorSquare :=
    integrable_sq_sub_coordinate_diagonalGaussianMeasure posterior i
      (posterior.mean i)
  have hconst : Integrable
      (fun _x : GaussianParameterSpace d =>
        Real.log (prior.variance i / posterior.variance i))
      (diagonalGaussianMeasure posterior) := integrable_const _
  have hpriorDiv := hpriorSquare.div_const (prior.variance i)
  have hposteriorDiv := hposteriorSquare.div_const (posterior.variance i)
  have hnum :
      ∫ x : GaussianParameterSpace d,
          Real.log (prior.variance i / posterior.variance i) +
              (x i - prior.mean i) ^ (2 : Nat) / prior.variance i -
            (x i - posterior.mean i) ^ (2 : Nat) /
              posterior.variance i
          ∂diagonalGaussianMeasure posterior =
        Real.log (prior.variance i / posterior.variance i) +
            (posterior.variance i +
                (posterior.mean i - prior.mean i) ^ (2 : Nat)) /
              prior.variance i -
          posterior.variance i / posterior.variance i := by
    calc
      ∫ x : GaussianParameterSpace d,
          Real.log (prior.variance i / posterior.variance i) +
              (x i - prior.mean i) ^ (2 : Nat) / prior.variance i -
            (x i - posterior.mean i) ^ (2 : Nat) /
              posterior.variance i
          ∂diagonalGaussianMeasure posterior =
        (∫ x : GaussianParameterSpace d,
            Real.log (prior.variance i / posterior.variance i) +
              (x i - prior.mean i) ^ (2 : Nat) / prior.variance i
            ∂diagonalGaussianMeasure posterior) -
          ∫ x : GaussianParameterSpace d,
            (x i - posterior.mean i) ^ (2 : Nat) /
              posterior.variance i
            ∂diagonalGaussianMeasure posterior := by
              exact integral_sub (hconst.add hpriorDiv) hposteriorDiv
      _ = ((∫ _x : GaussianParameterSpace d,
              Real.log (prior.variance i / posterior.variance i)
              ∂diagonalGaussianMeasure posterior) +
            ∫ x : GaussianParameterSpace d,
              (x i - prior.mean i) ^ (2 : Nat) / prior.variance i
              ∂diagonalGaussianMeasure posterior) -
          ∫ x : GaussianParameterSpace d,
            (x i - posterior.mean i) ^ (2 : Nat) /
              posterior.variance i
            ∂diagonalGaussianMeasure posterior := by
              rw [integral_add hconst hpriorDiv]
      _ = Real.log (prior.variance i / posterior.variance i) +
            (posterior.variance i +
                (posterior.mean i - prior.mean i) ^ (2 : Nat)) /
              prior.variance i -
          posterior.variance i / posterior.variance i := by
            rw [integral_div, integral_div,
              integral_sq_sub_coordinate_diagonalGaussianMeasure posterior i
                (prior.mean i),
              integral_sq_sub_coordinate_diagonalGaussianMeasure posterior i
                (posterior.mean i),
              integral_const]
            simp
  rw [integral_div, hnum]
  simp [posterior.variance_pos i |>.ne']
  ring

/-- Mathlib's KL divergence between two repository diagonal Gaussian measures
is finite. -/
theorem diagonalGaussianMeasure_klDiv_ne_top {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    InformationTheory.klDiv
      (diagonalGaussianMeasure posterior)
      (diagonalGaussianMeasure prior) ≠ ∞ := by
  exact InformationTheory.klDiv_ne_top
    (diagonalGaussianMeasure_mutuallyAbsolutelyContinuous posterior prior).1
    (integrable_llr_diagonalGaussianMeasure posterior prior)

/-- Mathlib's measure-theoretic KL divergence between two repository diagonal
Gaussian measures equals the repository's analytic diagonal Gaussian KL
expression. -/
theorem diagonalGaussianMeasure_klDiv_toReal_eq {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    (InformationTheory.klDiv
      (diagonalGaussianMeasure posterior)
      (diagonalGaussianMeasure prior)).toReal =
      diagonalGaussianKL posterior prior := by
  have hposteriorPrior :
      diagonalGaussianMeasure posterior ≪ diagonalGaussianMeasure prior :=
    (diagonalGaussianMeasure_mutuallyAbsolutelyContinuous posterior prior).1
  have hllr := integrable_llr_diagonalGaussianMeasure posterior prior
  rw [InformationTheory.toReal_klDiv hposteriorPrior hllr]
  simpa using
    integral_llr_diagonalGaussianMeasure_eq_diagonalGaussianKL posterior prior

/-- Mathlib's KL divergence between two repository spherical Gaussian measures
is finite. -/
theorem sphericalGaussianMeasure_klDiv_ne_top {d : ℕ}
    (posterior prior : SphericalGaussianParams d) :
    InformationTheory.klDiv
      (sphericalGaussianMeasure posterior)
      (sphericalGaussianMeasure prior) ≠ ∞ := by
  exact diagonalGaussianMeasure_klDiv_ne_top
    posterior.toDiagonal prior.toDiagonal

/-- Mathlib's measure-theoretic KL divergence between two repository spherical
Gaussian measures equals the repository's analytic spherical Gaussian KL
expression. -/
theorem sphericalGaussianMeasure_klDiv_toReal_eq {d : ℕ}
    (posterior prior : SphericalGaussianParams d) :
    (InformationTheory.klDiv
      (sphericalGaussianMeasure posterior)
      (sphericalGaussianMeasure prior)).toReal =
      sphericalGaussianKL posterior prior := by
  exact diagonalGaussianMeasure_klDiv_toReal_eq
    posterior.toDiagonal prior.toDiagonal

end

end FormalSLT.PACBayes
