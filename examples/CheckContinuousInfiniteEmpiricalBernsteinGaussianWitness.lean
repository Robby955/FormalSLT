import FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch
import FormalSLT.PACBayes.FinitePMFBridge
import FormalSLT.PACBayes.GaussianMeasureKL
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Continuous product-posterior receipt

The hypothesis space is `ℝ × Bool`.  Its continuous coordinate has a standard
Gaussian prior and a shifted Gaussian posterior; its Boolean coordinate stays
fair under both.  The Boolean prediction is flipped according to the sign of
the Gaussian coordinate, so the zero-one loss genuinely depends on both
coordinates and attains both endpoints of `[0,1]`.

The posterior has no point masses, is not finitely supported, and has exact
KL `1/32`.  At `n = 2^20` and
confidence `delta = 1/2`, its empirical risk is exactly `1/2` on every path
and the complete empirical-Bernstein correction is strictly below `1/2`.
Thus the theorem-produced upper ceiling is strictly below one.

This is a fixed continuous posterior receipt.  It does not claim
data-dependent posterior selection.
-/

namespace FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinGaussianWitness

open Finset BigOperators MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse
open FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt
open FormalSLT.PACBayes.InfiniteProductMeasureBridge
open FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch
open scoped ENNReal

noncomputable section

abbrev GaussianCoordinate := GaussianParameterSpace 1
abbrev Hypothesis := GaussianCoordinate × Bool

def priorGaussianParams : SphericalGaussianParams 1 where
  mean := fun _ ↦ 0
  variance := 1
  variance_pos := by norm_num

def posteriorGaussianParams : SphericalGaussianParams 1 where
  mean := fun _ ↦ (1 : ℝ) / 4
  variance := 1
  variance_pos := by norm_num

def priorGaussian : Measure GaussianCoordinate :=
  sphericalGaussianMeasure priorGaussianParams

def posteriorGaussian : Measure GaussianCoordinate :=
  sphericalGaussianMeasure posteriorGaussianParams

/-- Uniform probability mass on the Boolean predictor coordinate. -/
def boolPMF : Bool → ℝ := fun _ ↦ (1 : ℝ) / 2

theorem boolPMF_isPMF : IsPMF boolPMF := by
  constructor
  · intro b
    norm_num [boolPMF]
  · simp [boolPMF]

def boolMeasure : Measure Bool := boolPMF_isPMF.toPMF.toMeasure

instance priorGaussian_probability : IsProbabilityMeasure priorGaussian := by
  dsimp [priorGaussian]
  infer_instance

instance posteriorGaussian_probability : IsProbabilityMeasure posteriorGaussian := by
  dsimp [posteriorGaussian]
  infer_instance

instance boolMeasure_probability : IsProbabilityMeasure boolMeasure := by
  dsimp [boolMeasure]
  infer_instance

def boolKernel : Kernel GaussianCoordinate Bool :=
  Kernel.const GaussianCoordinate boolMeasure

instance boolKernel_markov : IsMarkovKernel boolKernel := by
  dsimp [boolKernel]
  infer_instance

def prior : Measure Hypothesis := priorGaussian ⊗ₘ boolKernel

def posterior : Measure Hypothesis := posteriorGaussian ⊗ₘ boolKernel

instance prior_probability : IsProbabilityMeasure prior := by
  dsimp [prior, priorGaussian, boolKernel, boolMeasure]
  infer_instance

instance posterior_probability : IsProbabilityMeasure posterior := by
  dsimp [posterior, posteriorGaussian, boolKernel, boolMeasure]
  infer_instance

instance priorGaussian_nullSingleton : NullSingletonClass priorGaussian := by
  dsimp [priorGaussian, sphericalGaussianMeasure, diagonalGaussianMeasure]
  infer_instance

instance posteriorGaussian_nullSingleton : NullSingletonClass posteriorGaussian := by
  dsimp [posteriorGaussian, sphericalGaussianMeasure, diagonalGaussianMeasure]
  infer_instance

instance prior_nullSingleton : NullSingletonClass prior := by
  rw [prior, boolKernel, Measure.compProd_const]
  infer_instance

instance posterior_nullSingleton : NullSingletonClass posterior := by
  rw [posterior, boolKernel, Measure.compProd_const]
  infer_instance

/-- Every finite subset has posterior mass zero, ruling out finite support. -/
theorem posterior_finite_set_mass_zero (s : Finset Hypothesis) :
    posterior s = 0 := by
  exact s.measure_zero posterior

theorem posterior_absolutelyContinuous : posterior ≪ prior := by
  exact (sphericalGaussianMeasure_absolutelyContinuous
    posteriorGaussianParams priorGaussianParams).compProd_left boolKernel

theorem posterior_llr_integrable : Integrable (llr posterior prior) posterior := by
  have hac := posterior_absolutelyContinuous
  apply (InformationTheory.integrable_llr_compProd_iff hac).2
  constructor
  · exact integrable_llr_diagonalGaussianMeasure
      posteriorGaussianParams.toDiagonal priorGaussianParams.toDiagonal
  · rw [integrable_congr (llr_self _)]
    exact integrable_zero _ _ _

/-- The unchanged Boolean kernel adds no KL to the shifted Gaussian cost. -/
theorem posterior_kl_eq :
    (InformationTheory.klDiv posterior prior).toReal = (1 : ℝ) / 32 := by
  rw [posterior, prior, InformationTheory.klDiv_compProd_left,
    posteriorGaussian, priorGaussian,
    sphericalGaussianMeasure_klDiv_toReal_eq,
    sphericalGaussianKL_eq_closedForm]
  norm_num [posteriorGaussianParams, priorGaussianParams,
    squaredMeanDistance, sphericalGaussianKLClosedForm]

/-- Flip the Boolean coordinate when the Gaussian coordinate is negative. -/
def prediction (theta : Hypothesis) : Bool :=
  if 0 ≤ theta.1 0 then theta.2 else !theta.2

/-- Genuine unscaled zero-one mismatch loss. -/
def mismatchLoss (theta : Hypothesis) (z : Bool) : ℝ :=
  if prediction theta = z then 0 else 1

theorem prediction_measurable : Measurable prediction := by
  have hsign : MeasurableSet {theta : Hypothesis | 0 ≤ theta.1 0} :=
    measurableSet_le measurable_const
      ((measurable_pi_apply 0).comp measurable_fst)
  have hnot : Measurable (fun theta : Hypothesis ↦ !theta.2) :=
    (measurable_of_finite (fun b : Bool ↦ !b)).comp measurable_snd
  exact Measurable.ite hsign measurable_snd hnot

theorem mismatchLoss_stronglyMeasurable (z : Bool) :
    StronglyMeasurable (fun theta : Hypothesis ↦ mismatchLoss theta z) := by
  have hout : Measurable (fun b : Bool ↦ if b = z then (0 : ℝ) else 1) :=
    measurable_of_finite _
  exact (hout.comp prediction_measurable).stronglyMeasurable

theorem mismatchLoss_mem_Icc (theta : Hypothesis) (z : Bool) :
    mismatchLoss theta z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold mismatchLoss
  split <;> norm_num

/-- The loss really attains both zero and one for every hypothesis. -/
theorem mismatchLoss_attains_endpoints (theta : Hypothesis) :
    mismatchLoss theta (prediction theta) = 0 ∧
      mismatchLoss theta (!prediction theta) = 1 := by
  cases h : prediction theta <;> simp [mismatchLoss, h]

/-- The two Boolean coordinates always incur complementary empirical risks. -/
theorem twoBool_empiricalRisk_add_eq_one {n : ℕ} (hn : 0 < n)
    (g : GaussianCoordinate) (S : Fin n → Bool) :
    finiteEmpiricalRisk mismatchLoss (g, false) S +
      finiteEmpiricalRisk mismatchLoss (g, true) S = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold finiteEmpiricalRisk
  rw [← mul_add, ← Finset.sum_add_distrib]
  have hsum :
      (∑ k : Fin n,
          (mismatchLoss (g, false) (S k) +
            mismatchLoss (g, true) (S k))) = n := by
    calc
      _ = ∑ _k : Fin n, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hg : 0 ≤ g 0 <;> cases S k <;>
          simp [mismatchLoss, prediction, hg]
      _ = n := by simp
  rw [hsum]
  exact inv_mul_cancel₀ hnR

/-- Conditional on every Gaussian coordinate, fair Boolean mixing makes the
posterior empirical risk exactly `1/2`. -/
theorem boolIntegral_empiricalRisk_eq_half {n : ℕ} (hn : 0 < n)
    (g : GaussianCoordinate) (S : Fin n → Bool) :
    (∫ b, finiteEmpiricalRisk mismatchLoss (g, b) S ∂boolMeasure) =
      (1 : ℝ) / 2 := by
  rw [boolMeasure, boolPMF_isPMF.integral_toPMF_eq_sum]
  simp only [Fintype.sum_bool, boolPMF]
  have hsum := twoBool_empiricalRisk_add_eq_one hn g S
  linarith

/-- The product posterior's empirical risk is exactly `1/2` on every
nonempty sample, independently of the observed path. -/
theorem posterior_empiricalRisk_eq_half {n : ℕ} (hn : 0 < n)
    (S : Fin n → Bool) :
    (∫ theta, finiteEmpiricalRisk mismatchLoss theta S ∂posterior) =
      (1 : ℝ) / 2 := by
  let f : Hypothesis → ℝ := fun theta ↦
    finiteEmpiricalRisk mismatchLoss theta S
  have hf_meas : StronglyMeasurable f :=
    stronglyMeasurable_finiteEmpiricalRisk_parameter
      mismatchLoss S mismatchLoss_stronglyMeasurable
  have hf_mem (theta : Hypothesis) : f theta ∈ Set.Icc (0 : ℝ) 1 := by
    unfold f finiteEmpiricalRisk
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hnR.le)
        (Finset.sum_nonneg fun k _ ↦ (mismatchLoss_mem_Icc theta (S k)).1)
    · calc
        (n : ℝ)⁻¹ * ∑ k : Fin n, mismatchLoss theta (S k) ≤
            (n : ℝ)⁻¹ * ∑ _k : Fin n, (1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun k _ ↦ (mismatchLoss_mem_Icc theta (S k)).2)
            (inv_nonneg.mpr hnR.le)
        _ = 1 := by simp [hnR.ne']
  have hf_int : Integrable f posterior := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_mem theta).1]
      exact (hf_mem theta).2
  rw [posterior, Measure.integral_compProd hf_int]
  simp only [boolKernel, Kernel.const_apply]
  change
    (∫ g, ∫ b, finiteEmpiricalRisk mismatchLoss (g, b) S ∂boolMeasure
      ∂posteriorGaussian) = (1 : ℝ) / 2
  simp_rw [boolIntegral_empiricalRisk_eq_half hn]
  simp

/-- A crude rational complexity ceiling sufficient for the numerical check. -/
theorem complexity_lt_17640 :
    continuousInfiniteEmpiricalBernsteinComplexity
        1048576 (1 / 2 : ℝ) prior posterior < 17640 := by
  rw [continuousInfiniteEmpiricalBernsteinComplexity, posterior_kl_eq]
  norm_num [Nat.log]
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 17640 by norm_num)
  linarith

/-- Even at the universal Bessel-variance cap `1/2`, the entire theorem
correction is strictly below `1/2`. -/
theorem numericalCorrection_lt_half
    {V : ℝ} (hV : V ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    (5 / 2 : ℝ) * Real.sqrt
        (V * continuousInfiniteEmpiricalBernsteinComplexity
          1048576 (1 / 2 : ℝ) prior posterior / 1048576) +
      5 * continuousInfiniteEmpiricalBernsteinComplexity
          1048576 (1 / 2 : ℝ) prior posterior / 1048576 < 1 / 2 := by
  let L := continuousInfiniteEmpiricalBernsteinComplexity
    1048576 (1 / 2 : ℝ) prior posterior
  have hLpos : 0 < L :=
    continuousInfiniteEmpiricalBernsteinComplexity_pos
      (by norm_num) (by norm_num) (by norm_num) prior posterior
  have hL : L < 17640 := complexity_lt_17640
  have hsarg : V * L / 1048576 < (1 : ℝ) / 100 := by
    have hmul : V * L ≤ (1 / 2 : ℝ) * L :=
      mul_le_mul_of_nonneg_right hV.2 hLpos.le
    calc
      V * L / 1048576 ≤ ((1 / 2 : ℝ) * L) / 1048576 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ < ((1 / 2 : ℝ) * 17640) / 1048576 := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left hL (by norm_num)) (by norm_num)
      _ < (1 : ℝ) / 100 := by norm_num
  have hsarg_nonneg : 0 ≤ V * L / 1048576 :=
    div_nonneg (mul_nonneg hV.1 hLpos.le) (by norm_num)
  have hsqrt : Real.sqrt (V * L / 1048576) < (1 : ℝ) / 10 := by
    rw [Real.sqrt_lt hsarg_nonneg (by norm_num)]
    norm_num
    exact hsarg
  have hlinear : 5 * L / 1048576 < (1 : ℝ) / 10 := by
    calc
      5 * L / 1048576 < 5 * 17640 / 1048576 := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left hL (by norm_num)) (by norm_num)
      _ < (1 : ℝ) / 10 := by norm_num
  change (5 / 2 : ℝ) * Real.sqrt (V * L / 1048576) +
      5 * L / 1048576 < 1 / 2
  nlinarith

/-- Concrete no-point-mass, non-vacuous theorem receipt.

One common event of mass at most `1/2` controls the fixed shifted-Gaussian
product posterior.  Off it, the theorem's displayed right-hand side is
strictly below one at `n = 2^20`. -/
theorem gaussianPosterior_nonVacuous_receipt :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      Measure.infinitePi
          (fun _ : ℕ ↦ boolPMF_isPMF.toPMF.toMeasure) E ≤
        ENNReal.ofReal (1 / 2 : ℝ) ∧
      ∀ x, x ∉ E →
        let S := natSamplePrefix 1048576 x
        let empirical :=
          ∫ theta, finiteEmpiricalRisk mismatchLoss theta S ∂posterior
        let correction :=
          (5 / 2 : ℝ) * Real.sqrt
            ((∫ theta, finiteEmpiricalVariance mismatchLoss theta S ∂posterior) *
              continuousInfiniteEmpiricalBernsteinComplexity
                1048576 (1 / 2 : ℝ) prior posterior / 1048576) +
          5 * continuousInfiniteEmpiricalBernsteinComplexity
              1048576 (1 / 2 : ℝ) prior posterior / 1048576
        (∫ theta, finitePopulationRisk boolPMF mismatchLoss theta ∂posterior) <
            empirical + correction ∧
          empirical + correction < 1 := by
  obtain ⟨E, hEmeas, hEmass, hE⟩ :=
    exists_continuousInfiniteEmpiricalBernstein_event
      boolPMF boolPMF_isPMF prior mismatchLoss
      mismatchLoss_stronglyMeasurable mismatchLoss_mem_Icc
      (delta := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  refine ⟨E, hEmeas, hEmass, ?_⟩
  intro x hx
  dsimp only
  let S := natSamplePrefix 1048576 x
  have hbound := hE x hx 1048576 (by norm_num) posterior inferInstance
    posterior_absolutelyContinuous posterior_llr_integrable
  have hV := continuousPosterior_finiteEmpiricalVariance_mem_Icc
    (posterior := posterior) (by norm_num) mismatchLoss S
    mismatchLoss_stronglyMeasurable mismatchLoss_mem_Icc
  have hcorrection := numericalCorrection_lt_half hV
  have hempirical := posterior_empiricalRisk_eq_half (by norm_num) S
  exact ⟨by simpa [add_assoc] using hbound, by linarith⟩

/-- The strict mass bound also guarantees that the receipt controls at least
one infinite sample path.  The witness is existential; no particular path is
claimed to be outside the exceptional event. -/
theorem gaussianPosterior_goodPath_exists :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      Measure.infinitePi
          (fun _ : ℕ ↦ boolPMF_isPMF.toPMF.toMeasure) E ≤
        ENNReal.ofReal (1 / 2 : ℝ) ∧
      ∃ x : ℕ → Bool, x ∉ E := by
  obtain ⟨E, hEmeas, hmass, _⟩ := gaussianPosterior_nonVacuous_receipt
  refine ⟨E, hEmeas, hmass, ?_⟩
  by_contra h
  push Not at h
  have h_univ : E = Set.univ := by
    ext x
    simp [h x]
  rw [h_univ] at hmass
  norm_num at hmass

#print axioms posterior_finite_set_mass_zero
#print axioms posterior_kl_eq
#print axioms posterior_llr_integrable
#print axioms mismatchLoss_attains_endpoints
#print axioms posterior_empiricalRisk_eq_half
#print axioms numericalCorrection_lt_half
#print axioms gaussianPosterior_nonVacuous_receipt
#print axioms gaussianPosterior_goodPath_exists

end

end FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinGaussianWitness
