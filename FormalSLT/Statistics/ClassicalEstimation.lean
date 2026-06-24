/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Statistics.Bernoulli
import FormalSLT.Statistics.SampleStatistics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Classical finite-sample estimation facts

This module starts the StatLean v0.2 classical-statistics lane.  It keeps the
first layer finite and explicit: deterministic sample-statistic algebra,
finite weighted expectation identities, count-level Bernoulli likelihood
statements, Gaussian known-variance score and least-squares identities,
Horvitz-Thompson design unbiasedness, and the finite-population bootstrap mean.

The intentionally finite scope matches the existing FormalSLT statistics seed:
the library already has finite weighted expectation primitives, but does not yet
have a reusable differentiability-under-the-integral or Fisher-information API.
-/

open scoped BigOperators
open Finset

namespace FormalSLT.Statistics
namespace ClassicalEstimation

noncomputable section

/-! ### Finite weighted expectations -/

/-- Finite weighted expectation over all points of a finite type. -/
def weightedExpectation {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, w ω * X ω

/-- The finite weighted expectation is the corresponding explicit finite sum. -/
theorem weightedExpectation_eq_sum {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) :
    weightedExpectation w X = ∑ ω, w ω * X ω := by
  rfl

/-- Weighted expectation of a constant under weights summing to one. -/
theorem weightedExpectation_const {Ω : Type*} [Fintype Ω]
    {w : Ω → ℝ} (hsum : ∑ ω, w ω = 1) (c : ℝ) :
    weightedExpectation w (fun _ => c) = c := by
  unfold weightedExpectation
  rw [← Finset.sum_mul]
  simp [hsum]

/-- Finite weighted expectation is additive. -/
theorem weightedExpectation_add {Ω : Type*} [Fintype Ω]
    (w X Y : Ω → ℝ) :
    weightedExpectation w (fun ω => X ω + Y ω)
      = weightedExpectation w X + weightedExpectation w Y := by
  unfold weightedExpectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- Finite weighted expectation respects subtraction. -/
theorem weightedExpectation_sub {Ω : Type*} [Fintype Ω]
    (w X Y : Ω → ℝ) :
    weightedExpectation w (fun ω => X ω - Y ω)
      = weightedExpectation w X - weightedExpectation w Y := by
  unfold weightedExpectation
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Finite weighted expectation is homogeneous. -/
theorem weightedExpectation_smul {Ω : Type*} [Fintype Ω]
    (w X : Ω → ℝ) (a : ℝ) :
    weightedExpectation w (fun ω => a * X ω) = a * weightedExpectation w X := by
  unfold weightedExpectation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  ring

/-- Finite weighted expectation respects negation. -/
theorem weightedExpectation_neg {Ω : Type*} [Fintype Ω]
    (w X : Ω → ℝ) :
    weightedExpectation w (fun ω => -X ω) = -weightedExpectation w X := by
  simpa using weightedExpectation_smul w X (-1)

/-- Finite weighted expectation is linear. -/
theorem weightedExpectation_linear {Ω : Type*} [Fintype Ω]
    (w X Y : Ω → ℝ) (a b : ℝ) :
    weightedExpectation w (fun ω => a * X ω + b * Y ω)
      = a * weightedExpectation w X + b * weightedExpectation w Y := by
  rw [weightedExpectation_add, weightedExpectation_smul, weightedExpectation_smul]

/-! ### Sample mean algebra -/

/-- **The sample mean of a constant sample is that constant.** -/
theorem sampleMean_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    sampleMean (fun _ : Fin n => c) = c := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sampleMean
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hnR]

/-- **Sample means add pointwise.** `(x + y) bar = x bar + y bar`. -/
theorem sampleMean_add {n : ℕ} (x y : Fin n → ℝ) :
    sampleMean (fun i => x i + y i) = sampleMean x + sampleMean y := by
  unfold sampleMean
  rw [Finset.sum_add_distrib]
  ring

/-- **Sample means subtract pointwise.** `(x - y) bar = x bar - y bar`. -/
theorem sampleMean_sub {n : ℕ} (x y : Fin n → ℝ) :
    sampleMean (fun i => x i - y i) = sampleMean x - sampleMean y := by
  unfold sampleMean
  rw [Finset.sum_sub_distrib]
  ring

/-- **Sample means commute with scalar multiplication.** -/
theorem sampleMean_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    sampleMean (fun i => a * x i) = a * sampleMean x := by
  unfold sampleMean
  rw [← Finset.mul_sum]
  ring

/-- The sample mean of the zero sample is zero. -/
theorem sampleMean_zero {n : ℕ} :
    sampleMean (fun _ : Fin n => 0) = 0 := by
  unfold sampleMean
  simp

/-- Negating a sample negates its sample mean. -/
theorem sampleMean_neg {n : ℕ} (x : Fin n → ℝ) :
    sampleMean (fun i => -x i) = -sampleMean x := by
  simpa using sampleMean_smul (-1) x

/-- Adding a constant shifts the sample mean by that constant. -/
theorem sampleMean_add_const {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    sampleMean (fun i => x i + c) = sampleMean x + c := by
  rw [sampleMean_add, sampleMean_const hn c]

/-- `sampleMean` is the uniform finite weighted mean on the sample indices. -/
theorem sampleMean_eq_finiteMean_uniform {n : ℕ} (x : Fin n → ℝ) :
    weightedExpectation (fun _ : Fin n => (1 : ℝ) / (n : ℝ)) x = sampleMean x := by
  unfold weightedExpectation sampleMean
  rw [← Finset.mul_sum]
  ring

/-- The centered residuals around the sample mean sum to zero. -/
theorem sum_sub_sampleMean_eq_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - sampleMean x) = 0 := by
  have hmean := sampleMean_mul_card hn x
  calc
    ∑ i, (x i - sampleMean x)
        = (∑ i, x i) - ∑ _i : Fin n, sampleMean x := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i, x i) - (n : ℝ) * sampleMean x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 0 := by
          rw [hmean]
          ring

/-- The sum-of-squares decomposition around the sample mean. -/
theorem sum_sq_sub_eq_sum_sq_sub_mean_add_card {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (a : ℝ) :
    ∑ i, (x i - a) ^ 2 =
      ∑ i, (x i - sampleMean x) ^ 2 + (n : ℝ) * (sampleMean x - a) ^ 2 := by
  have hcenter := sum_sub_sampleMean_eq_zero hn x
  calc
    ∑ i, (x i - a) ^ 2
        = ∑ i, ((x i - sampleMean x) + (sampleMean x - a)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = ∑ i, ((x i - sampleMean x) ^ 2
          + 2 * (sampleMean x - a) * (x i - sampleMean x)
          + (sampleMean x - a) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = ∑ i, (x i - sampleMean x) ^ 2
          + 2 * (sampleMean x - a) * ∑ i, (x i - sampleMean x)
          + ∑ _i : Fin n, (sampleMean x - a) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i, (x i - sampleMean x) ^ 2 + (n : ℝ) * (sampleMean x - a) ^ 2 := by
          rw [hcenter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-- The sample mean minimizes the empirical sum of squared deviations. -/
theorem sum_sq_sub_sampleMean_le_sum_sq_sub {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (a : ℝ) :
    ∑ i, (x i - sampleMean x) ^ 2 ≤ ∑ i, (x i - a) ^ 2 := by
  rw [sum_sq_sub_eq_sum_sq_sub_mean_add_card hn x a]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))

/-! ### Finite unbiasedness of the sample mean -/

/-- **Finite unbiasedness of the sample mean.**

For any finite probability model represented by weights, the expectation of the
sample mean equals the sample mean of the coordinate expectations. -/
theorem sampleMean_unbiased_finite {Ω : Type*} [Fintype Ω]
    {n : ℕ} (w : Ω → ℝ) (X : Fin n → Ω → ℝ) :
    weightedExpectation w (fun ω => sampleMean (fun i => X i ω))
      = sampleMean (fun i => weightedExpectation w (fun ω => X i ω)) := by
  unfold weightedExpectation sampleMean
  calc
    ∑ ω, w ω * ((∑ i, X i ω) / (n : ℝ))
        = ∑ ω, (∑ i, w ω * X i ω) / (n : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro ω _hω
          rw [← Finset.mul_sum]
          ring
    _ = (∑ ω, ∑ i, w ω * X i ω) / (n : ℝ) := by
          rw [Finset.sum_div]
    _ = (∑ i, ∑ ω, w ω * X i ω) / (n : ℝ) := by
          rw [Finset.sum_comm]

/-- If all coordinate expectations equal `μ`, the sample mean is unbiased for `μ`. -/
theorem sampleMean_unbiased_identically_distributed_finite {Ω : Type*} [Fintype Ω]
    {n : ℕ} (hn : 0 < n) (w : Ω → ℝ) (X : Fin n → Ω → ℝ) (μ : ℝ)
    (hmean : ∀ i, weightedExpectation w (fun ω => X i ω) = μ) :
    weightedExpectation w (fun ω => sampleMean (fun i => X i ω)) = μ := by
  rw [sampleMean_unbiased_finite]
  convert sampleMean_const hn μ using 2
  funext i
  exact hmean i

/-! ### Bessel-corrected sample variance seeds -/

/-- **Bessel-corrected sample variance** `(1 / (n - 1)) ∑ (xᵢ - x̄)²`.
Lean's total division gives a value at `n = 0` and `n = 1`; theorems that use it
state the needed nondegeneracy hypotheses. -/
def sampleVarianceBessel {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / ((n : ℝ) - 1)

/-- Bessel variance is nonnegative for samples of size at least two. -/
theorem sampleVarianceBessel_nonneg {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    0 ≤ sampleVarianceBessel x := by
  unfold sampleVarianceBessel
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n from le_trans (by norm_num) hn)
    linarith

/-- The Bessel variance of two observations is half the squared difference. -/
theorem sampleVarianceBessel_two (x : Fin 2 → ℝ) :
    sampleVarianceBessel x = ((x 0 - x 1) ^ 2) / 2 := by
  unfold sampleVarianceBessel sampleMean
  rw [Fin.sum_univ_two]
  norm_num
  ring

/-! ### Bernoulli count likelihood -/

/-- Bernoulli log-likelihood from `k` successes in `n` trials, omitting constants. -/
def bernoulliLogLikelihoodFromCount (n k : ℕ) (θ : ℝ) : ℝ :=
  (k : ℝ) * Real.log θ + ((n - k : ℕ) : ℝ) * Real.log (1 - θ)

/-- Bernoulli score from `k` successes in `n` trials. -/
def bernoulliScoreFromCount (n k : ℕ) (θ : ℝ) : ℝ :=
  (k : ℝ) / θ - ((n - k : ℕ) : ℝ) / (1 - θ)

/-- **Bernoulli MLE score equation.**

For an interior count `0 < k < n`, the Bernoulli score vanishes at the sample
success rate `k / n`, the textbook MLE for the Bernoulli parameter. -/
theorem bernoulliScoreAtSampleMean_eq_zero {n k : ℕ}
    (hk0 : 0 < k) (hkn : k < n) :
    bernoulliScoreFromCount n k ((k : ℝ) / (n : ℝ)) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans hk0 hkn))
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact_mod_cast Nat.cast_sub hkn.le
  have hnkR : (n : ℝ) - (k : ℝ) ≠ 0 := by
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    linarith
  unfold bernoulliScoreFromCount
  rw [hsub]
  field_simp [hn0, hkR, hnkR]
  ring

/-- Count-level Bernoulli score statement naming the interior MLE target. -/
theorem bernoulliScore_mle_from_count {n k : ℕ}
    (hk0 : 0 < k) (hkn : k < n) :
    bernoulliScoreFromCount n k ((k : ℝ) / (n : ℝ)) = 0 :=
  bernoulliScoreAtSampleMean_eq_zero hk0 hkn

/-! ### Gaussian known-variance likelihood -/

/-- Gaussian known-variance log-likelihood as a function of the mean, omitting
the additive normalizing constant. -/
def gaussianKnownVarianceLogLikelihood {n : ℕ} (x : Fin n → ℝ) (sigma2 μ : ℝ) : ℝ :=
  - (∑ i, (x i - μ) ^ 2) / (2 * sigma2)

/-- Gaussian known-variance score for the mean parameter. -/
def gaussianKnownVarianceScore {n : ℕ} (x : Fin n → ℝ) (sigma2 μ : ℝ) : ℝ :=
  (∑ i, (x i - μ)) / sigma2

/-- **Gaussian MLE score equation.**

For known nonzero variance and nonempty sample, the Gaussian mean score vanishes
at the sample mean. -/
theorem gaussianScoreAtSampleMean_eq_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {sigma2 : ℝ} (hsigma2 : sigma2 ≠ 0) :
    gaussianKnownVarianceScore x sigma2 (sampleMean x) = 0 := by
  have _hsigma2 := hsigma2
  unfold gaussianKnownVarianceScore
  rw [sum_sub_sampleMean_eq_zero hn x]
  simp

/-- **Gaussian known-variance MLE equals the sample mean.**

With positive known variance, the Gaussian log-likelihood in the mean parameter
is maximized at `sampleMean x`. -/
theorem gaussianKnownVarianceLogLikelihood_mle {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {sigma2 μ : ℝ} (hsigma2 : 0 < sigma2) :
    gaussianKnownVarianceLogLikelihood x sigma2 μ
      ≤ gaussianKnownVarianceLogLikelihood x sigma2 (sampleMean x) := by
  have hss := sum_sq_sub_sampleMean_le_sum_sq_sub hn x μ
  have hden : 0 ≤ 2 * sigma2 := by positivity
  have hdiv := div_le_div_of_nonneg_right hss hden
  have hneg :
      -((∑ i, (x i - μ) ^ 2) / (2 * sigma2))
        ≤ -((∑ i, (x i - sampleMean x) ^ 2) / (2 * sigma2)) := by
    linarith
  unfold gaussianKnownVarianceLogLikelihood
  simpa [neg_div] using hneg

/-! ### Horvitz-Thompson finite-population estimator -/

/-- Finite-population total of a value over `N` units. -/
def finitePopulationTotal {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  ∑ i, y i

/-- Finite-population totals add pointwise. -/
theorem finitePopulationTotal_add {N : ℕ} (y z : Fin N → ℝ) :
    finitePopulationTotal (fun i => y i + z i)
      = finitePopulationTotal y + finitePopulationTotal z := by
  unfold finitePopulationTotal
  rw [Finset.sum_add_distrib]

/-- Finite-population totals commute with scalar multiplication. -/
theorem finitePopulationTotal_smul {N : ℕ} (a : ℝ) (y : Fin N → ℝ) :
    finitePopulationTotal (fun i => a * y i) = a * finitePopulationTotal y := by
  unfold finitePopulationTotal
  rw [← Finset.mul_sum]

/-- Horvitz-Thompson estimator `∑ Iᵢ yᵢ / πᵢ` for known inclusion probabilities. -/
def horvitzThompsonEstimator {N : ℕ}
    (y π inclusion : Fin N → ℝ) : ℝ :=
  ∑ i, inclusion i * y i / π i

/-- The Horvitz-Thompson estimator equals the total when every sampled inclusion
weight equals its inclusion probability. -/
theorem horvitzThompsonEstimator_eq_total_of_inclusion_eq_pi {N : ℕ}
    (y π : Fin N → ℝ) (hπ_ne : ∀ i, π i ≠ 0) :
    horvitzThompsonEstimator y π π = finitePopulationTotal y := by
  unfold horvitzThompsonEstimator finitePopulationTotal
  refine Finset.sum_congr rfl ?_
  intro i _hi
  field_simp [hπ_ne i]

/-- **Horvitz-Thompson design unbiasedness.**

In a finite design space, if each unit's expected inclusion indicator is its
known inclusion probability `πᵢ`, then the Horvitz-Thompson estimator has
finite-design expectation equal to the population total. -/
theorem horvitzThompson_design_unbiased {Ω : Type*} [Fintype Ω] {N : ℕ}
    (w : Ω → ℝ) (y π : Fin N → ℝ) (inclusion : Fin N → Ω → ℝ)
    (hπ_ne : ∀ i, π i ≠ 0)
    (hinclude : ∀ i, weightedExpectation w (fun ω => inclusion i ω) = π i) :
    weightedExpectation w
        (fun ω => horvitzThompsonEstimator y π (fun i => inclusion i ω))
      = finitePopulationTotal y := by
  unfold weightedExpectation horvitzThompsonEstimator finitePopulationTotal
  calc
    ∑ ω, w ω * (∑ i, inclusion i ω * y i / π i)
        = ∑ i, ∑ ω, w ω * (inclusion i ω * y i / π i) := by
          rw [← Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro ω _hω
          rw [Finset.mul_sum]
    _ = ∑ i, y i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hinc := hinclude i
          unfold weightedExpectation at hinc
          calc
            ∑ ω, w ω * (inclusion i ω * y i / π i)
                = (y i / π i) * ∑ ω, w ω * inclusion i ω := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro ω _hω
                  ring
            _ = y i := by
                  rw [hinc]
                  field_simp [hπ_ne i]

/-! ### Finite-population bootstrap mean -/

/-- The plug-in/bootstrap mean of the empirical distribution on an observed
finite sample. -/
def bootstrapMean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, ((1 : ℝ) / (n : ℝ)) * x i

/-- **Finite-population bootstrap mean identity.**

The mean of the empirical resampling distribution equals the observed sample
mean. -/
theorem bootstrapMean_eq_sampleMean {n : ℕ} (x : Fin n → ℝ) :
    bootstrapMean x = sampleMean x := by
  unfold bootstrapMean sampleMean
  rw [← Finset.mul_sum]
  ring

/-- The bootstrap mean of a constant observed sample is that constant. -/
theorem bootstrapMean_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    bootstrapMean (fun _ : Fin n => c) = c := by
  rw [bootstrapMean_eq_sampleMean, sampleMean_const hn c]

/-- Bootstrap mean is additive. -/
theorem bootstrapMean_add {n : ℕ} (x y : Fin n → ℝ) :
    bootstrapMean (fun i => x i + y i) = bootstrapMean x + bootstrapMean y := by
  simp [bootstrapMean_eq_sampleMean, sampleMean_add]

/-- Bootstrap mean is homogeneous. -/
theorem bootstrapMean_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    bootstrapMean (fun i => a * x i) = a * bootstrapMean x := by
  simp [bootstrapMean_eq_sampleMean, sampleMean_smul]

end

end ClassicalEstimation
end FormalSLT.Statistics
