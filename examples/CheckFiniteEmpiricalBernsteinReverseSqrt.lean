import FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-horizon closed-form empirical-Bernstein receipt

At `N = m = 64` and failure level `delta = 1/20`, an explicit positive-mass
Boolean path is outside the exact all-posterior dyadic event.  A point
posterior then has positive KL, positive Bessel empirical variance, and a
theorem-produced population-risk ceiling below one.  The numerical receipt is
endpoint-only; the public theorem itself is simultaneous over all prefixes in
the declared epoch.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalBernsteinReverseSqrt

open Finset BigOperators Real MeasureTheory
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
open FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt

noncomputable section

def dataLaw : Bool → ℝ := fun _ ↦ 1 / 2

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    norm_num [dataLaw]
  · norm_num [dataLaw]

def matchLoss (h z : Bool) : ℝ := if z = h then 1 else 0

theorem matchLoss_mem_Icc (h z : Bool) :
    matchLoss h z ∈ Set.Icc (0 : ℝ) 1 := by
  cases h <;> cases z <;> norm_num [matchLoss]

def fairPrior : Bool → ℝ := fun _ ↦ 1 / 2

theorem fairPrior_isFullSupportPMF : IsFullSupportPMF fairPrior := by
  constructor
  · constructor
    · intro h
      norm_num [fairPrior]
    · norm_num [fairPrior]
  · intro h
    norm_num [fairPrior]

/-- A fixed point posterior exposes a strictly positive KL term. -/
def pointPosterior : Bool → ℝ := fun h ↦ if h then 1 else 0

theorem pointPosterior_isPMF : IsPMF pointPosterior := by
  constructor
  · intro h
    cases h <;> norm_num [pointPosterior]
  · norm_num [pointPosterior, Fintype.sum_bool]

theorem pointPosterior_kl_eq_log_two :
    klDiv pointPosterior fairPrior = Real.log 2 := by
  simp [klDiv, pointPosterior, fairPrior]

theorem pointPosterior_kl_pos :
    0 < klDiv pointPosterior fairPrior := by
  rw [pointPosterior_kl_eq_log_two]
  exact Real.log_pos (by norm_num)

theorem matchLoss_populationRisk (h : Bool) :
    finitePopulationRisk dataLaw matchLoss h = 1 / 2 := by
  cases h <;>
    norm_num [finitePopulationRisk, dataLaw, matchLoss, Fintype.sum_bool]

theorem matchLoss_populationVariance (h : Bool) :
    finitePopulationVariance dataLaw matchLoss h = 1 / 4 := by
  cases h <;>
    norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw,
      matchLoss, Fintype.sum_bool]

def balanced64Sample : Fin 64 → Bool := fun k ↦ decide (32 ≤ k.1)

theorem balanced64_sampleWeight_pos :
    0 < finiteProductSampleWeight dataLaw balanced64Sample := by
  unfold finiteProductSampleWeight
  apply Finset.prod_pos
  intro k _
  norm_num [dataLaw]

theorem card_fin64_ge_32 :
    (Finset.univ.filter (fun k : Fin 64 ↦ 32 ≤ k.1)).card = 32 := by
  decide

theorem card_fin64_lt_32 :
    (Finset.univ.filter (fun k : Fin 64 ↦ k.1 < 32)).card = 32 := by
  decide

theorem balanced64_empiricalRisk (h : Bool) :
    finiteEmpiricalRisk matchLoss h balanced64Sample = 1 / 2 := by
  cases h <;>
    norm_num [finiteEmpiricalRisk, matchLoss, balanced64Sample]
  · rw [card_fin64_lt_32]
    norm_num
  · rw [card_fin64_ge_32]
    norm_num

theorem balanced64_empiricalVariance (h : Bool) :
    finiteEmpiricalVariance matchLoss h balanced64Sample = 16 / 63 := by
  unfold finiteEmpiricalVariance
  have hmean :
      FormalSLT.Statistics.sampleMean
          (fun k ↦ matchLoss h (balanced64Sample k)) = 1 / 2 := by
    calc
      FormalSLT.Statistics.sampleMean
            (fun k ↦ matchLoss h (balanced64Sample k)) =
          finiteEmpiricalRisk matchLoss h balanced64Sample := by
            unfold FormalSLT.Statistics.sampleMean finiteEmpiricalRisk
            ring
      _ = 1 / 2 := balanced64_empiricalRisk h
  unfold FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
  rw [hmean]
  have hpoint : ∀ k : Fin 64,
      (matchLoss h (balanced64Sample k) - (1 : ℝ) / 2) ^ 2 = 1 / 4 := by
    intro k
    unfold matchLoss
    split <;> norm_num
  simp_rw [hpoint]
  norm_num

theorem samplePrefix_balanced64_eq :
    samplePrefix (Nat.le_refl 64) balanced64Sample = balanced64Sample := by
  rfl

theorem pointPosterior_balanced64_empiricalRisk :
    posteriorAverage pointPosterior
      (fun h ↦ finiteEmpiricalRisk matchLoss h
        (samplePrefix (Nat.le_refl 64) balanced64Sample)) = 1 / 2 := by
  rw [samplePrefix_balanced64_eq]
  simp [posteriorAverage, pointPosterior, balanced64_empiricalRisk]

theorem pointPosterior_balanced64_empiricalVariance :
    posteriorAverage pointPosterior
        (fun h ↦ finiteEmpiricalVariance matchLoss h
          (samplePrefix (Nat.le_refl 64) balanced64Sample)) = 16 / 63 := by
  rw [samplePrefix_balanced64_eq]
  simp [posteriorAverage, pointPosterior, balanced64_empiricalVariance]

theorem pointPosterior_balanced64_empiricalVariance_pos :
    0 < posteriorAverage pointPosterior
      (fun h ↦ finiteEmpiricalVariance matchLoss h
        (samplePrefix (Nat.le_refl 64) balanced64Sample)) := by
  rw [pointPosterior_balanced64_empiricalVariance]
  norm_num

theorem gridDepth64 : finiteEmpiricalBernsteinGridDepth 64 = 6 := by
  decide

/-- Every dyadic atom has a nonpositive fixed endpoint score. -/
theorem balanced64_score_le_zero (j : Fin 7) (h : Bool) :
    finiteJointMeanVarianceScore 64 dataLaw matchLoss
        (finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        (finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        h balanced64Sample ≤ 0 := by
  let q := finiteEmpiricalBernsteinDyadicScale j.1
  let t := finiteEmpiricalBernsteinTiltOfScale q
  let eta := finiteEmpiricalBernsteinEtaOfScale q
  have hqpos : 0 < q := finiteEmpiricalBernsteinDyadicScale_pos j.1
  have hqle : q ≤ 2 := finiteEmpiricalBernsteinDyadicScale_le_two j.1
  have ht_nonneg : 0 ≤ t := finiteEmpiricalBernsteinTiltOfScale_nonneg hqpos.le
  have heta_nonneg : 0 ≤ eta :=
    finiteEmpiricalBernsteinEtaOfScale_nonneg hqpos.le
  have hkappa_nonneg : 0 ≤ finiteJointMeanVarianceKappa 64 eta :=
    finiteJointMeanVarianceKappa_scale_nonneg (by norm_num) hqpos hqle
  have hkappa_le : finiteJointMeanVarianceKappa 64 eta ≤ 64 * eta := by
    unfold finiteJointMeanVarianceKappa
    norm_num
    nlinarith [sq_nonneg eta]
  have hexp : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hcorrection :
      Real.exp (-t) * finiteJointMeanVarianceKappa 64 eta * (1 / 4) ≤
        16 * eta := by
    have hfirst :
        Real.exp (-t) * finiteJointMeanVarianceKappa 64 eta ≤
          finiteJointMeanVarianceKappa 64 eta := by
      simpa using mul_le_mul_of_nonneg_right hexp hkappa_nonneg
    nlinarith
  have hpsi : 0 ≤ Real.exp t - 1 - t := by
    linarith [Real.add_one_le_exp t]
  have hlog :
      0 ≤ Real.log (1 + (Real.exp t - 1 - t) * (1 / 4)) := by
    exact Real.log_nonneg (by nlinarith)
  unfold finiteJointMeanVarianceScore
  rw [matchLoss_populationRisk, balanced64_empiricalRisk,
    balanced64_empiricalVariance, matchLoss_populationVariance]
  change
    t * 64 * (1 / 2 - 1 / 2) - eta * 64 * (16 / 63) -
        64 * Real.log (1 + (Real.exp t - 1 - t) * (1 / 4)) +
        Real.exp (-t) * finiteJointMeanVarianceKappa 64 eta * (1 / 4) ≤ 0
  nlinarith

theorem balanced64_reverseScore_le_zero (j : Fin 7) (h : Bool) :
    reverseJointMeanVarianceEpochScore 64 (by norm_num) 64 dataLaw matchLoss
        (finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        (finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        h 0 balanced64Sample ≤ 0 := by
  rw [show (0 : ℕ) = 64 - 64 by norm_num,
    reverseJointMeanVarianceEpochScore_endpoint
      (N := 64) (m := 64) (by norm_num) ⟨by norm_num, by norm_num⟩]
  rw [samplePrefix_balanced64_eq]
  exact balanced64_score_le_zero j h

/-- The explicit balanced path is outside the exact common dyadic event. -/
theorem balanced64_not_mem_reverseSqrtFailure :
    balanced64Sample ∉ finiteEmpiricalBernsteinReverseSqrtFailure
      64 (by norm_num) 64 dataLaw fairPrior matchLoss (1 / 20) := by
  rw [finiteEmpiricalBernsteinReverseSqrtFailure, gridDepth64]
  intro hx
  rcases hx with ⟨j, k, hk, rho, hrho, hfail⟩
  have hk0 : k = 0 := by omega
  subst k
  have hscore :
      posteriorAverage rho
          (fun h ↦ reverseJointMeanVarianceEpochScore
            64 (by norm_num) 64 dataLaw matchLoss
              (finiteEmpiricalBernsteinTiltOfScale
                (finiteEmpiricalBernsteinDyadicScale j.1))
              (finiteEmpiricalBernsteinEtaOfScale
                (finiteEmpiricalBernsteinDyadicScale j.1))
              h 0 balanced64Sample) ≤ 0 := by
    unfold posteriorAverage
    exact Finset.sum_nonpos fun h _ ↦
      mul_nonpos_of_nonneg_of_nonpos (hrho.nonneg h)
        (balanced64_reverseScore_le_zero j h)
  have hkl : 0 ≤ klDiv rho fairPrior :=
    klDiv_nonneg hrho fairPrior_isFullSupportPMF
  have hconfidence :
      0 < Real.log
        (1 / ((1 / 20 : ℝ) * finiteEmpiricalBernsteinDyadicWeight 6 j)) := by
    have hw : finiteEmpiricalBernsteinDyadicWeight 6 j = (1 : ℝ) / 7 := by
      norm_num [finiteEmpiricalBernsteinDyadicWeight]
    rw [hw]
    exact Real.log_pos (by norm_num)
  linarith

theorem reverseSqrtFailure_mass_le_one_twentieth :
    Measure.pi (fun _ : Fin 64 ↦ dataLaw_isPMF.toPMF.toMeasure)
        (finiteEmpiricalBernsteinReverseSqrtFailure
          64 (by norm_num) 64 dataLaw fairPrior matchLoss (1 / 20)) ≤
      ENNReal.ofReal ((1 : ℝ) / 20) := by
  exact finiteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
    64 64 (by norm_num) ⟨by norm_num, by norm_num⟩ dataLaw dataLaw_isPMF
    fairPrior_isFullSupportPMF matchLoss matchLoss_mem_Icc (by norm_num)

def reverseSqrtBalanced64Ceiling : ℝ :=
  1 / 2 +
    (5 / 4) * Real.sqrt ((Real.log 2 + Real.log 140) / 126) +
    (5 / 128) * (Real.log 2 + Real.log 140)

theorem pointPosterior_balanced64_risk_lt_ceiling :
    posteriorAverage pointPosterior (finitePopulationRisk dataLaw matchLoss) <
      reverseSqrtBalanced64Ceiling := by
  have hbound :=
    finiteEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
      64 64 64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF matchLoss
      matchLoss_mem_Icc (by norm_num) (by norm_num) balanced64Sample
      balanced64_not_mem_reverseSqrtFailure pointPosterior_isPMF
  rw [gridDepth64, pointPosterior_kl_eq_log_two,
    pointPosterior_balanced64_empiricalRisk,
    pointPosterior_balanced64_empiricalVariance] at hbound
  simp only [Nat.cast_ofNat] at hbound
  have hlogarg :
      Real.log (((6 : ℝ) + 1) / ((1 : ℝ) / 20)) = Real.log 140 := by
    norm_num
  rw [hlogarg] at hbound
  have hsqrtarg :
      2 * (16 / 63 : ℝ) * (Real.log 2 + Real.log 140) / 64 =
        (Real.log 2 + Real.log 140) / 126 := by ring
  rw [hsqrtarg] at hbound
  have hlinear :
      (5 / 2 : ℝ) * (Real.log 2 + Real.log 140) / 64 =
        (5 / 128) * (Real.log 2 + Real.log 140) := by ring
  rw [hlinear] at hbound
  simpa [reverseSqrtBalanced64Ceiling] using hbound

theorem reverseSqrtBalanced64Ceiling_lt_ninetyNineHundredths :
    reverseSqrtBalanced64Ceiling < (99 : ℝ) / 100 := by
  have hlog280 : Real.log 2 + Real.log 140 = Real.log 280 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (140 : ℝ) ≠ 0)]
    norm_num
  have hlog280_lt_log288 : Real.log 280 < Real.log 288 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlog288 : Real.log 288 = 5 * Real.log 2 + 2 * Real.log 3 := by
    calc
      Real.log 288 = Real.log ((2 : ℝ) ^ 5 * (3 : ℝ) ^ 2) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 5) + Real.log ((3 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = 5 * Real.log 2 + 2 * Real.log 3 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  have hL : Real.log 2 + Real.log 140 < (567 : ℝ) / 100 := by
    calc
      Real.log 2 + Real.log 140 = Real.log 280 := hlog280
      _ < Real.log 288 := hlog280_lt_log288
      _ = 5 * Real.log 2 + 2 * Real.log 3 := hlog288
      _ < (567 : ℝ) / 100 := by
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hradicand :
      (Real.log 2 + Real.log 140) / 126 < (17 / 80 : ℝ) ^ (2 : Nat) := by
    nlinarith
  have hsqrt :
      Real.sqrt ((Real.log 2 + Real.log 140) / 126) < 17 / 80 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 17 / 80)]
    exact hradicand
  unfold reverseSqrtBalanced64Ceiling
  nlinarith

theorem reverseSqrtBalanced64Ceiling_lt_one :
    reverseSqrtBalanced64Ceiling < 1 := by
  linarith [reverseSqrtBalanced64Ceiling_lt_ninetyNineHundredths]

/-- Positive path mass, exact good-event membership, positive KL, positive
Bessel variance, and a theorem-produced ceiling below the loss range. -/
theorem balanced64_reverse_sqrt_nonvacuous :
    0 < finiteProductSampleWeight dataLaw balanced64Sample ∧
      balanced64Sample ∉ finiteEmpiricalBernsteinReverseSqrtFailure
        64 (by norm_num) 64 dataLaw fairPrior matchLoss (1 / 20) ∧
      0 < klDiv pointPosterior fairPrior ∧
      0 < posteriorAverage pointPosterior
        (fun h ↦ finiteEmpiricalVariance matchLoss h
          (samplePrefix (Nat.le_refl 64) balanced64Sample)) ∧
      posteriorAverage pointPosterior
          (finitePopulationRisk dataLaw matchLoss) <
        reverseSqrtBalanced64Ceiling ∧
      reverseSqrtBalanced64Ceiling < 1 :=
  ⟨balanced64_sampleWeight_pos,
    balanced64_not_mem_reverseSqrtFailure,
    pointPosterior_kl_pos,
    pointPosterior_balanced64_empiricalVariance_pos,
    pointPosterior_balanced64_risk_lt_ceiling,
    reverseSqrtBalanced64Ceiling_lt_one⟩

#check finiteEmpiricalBernsteinReverseDyadicFailure_mass_le_delta
#check finiteEmpiricalBernsteinReverseDyadic_posteriorRisk_prefix_lt_sqrt_of_not_mem
#check finiteEmpiricalBernsteinReverseGridDepth_coverage
#check finiteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
#check finiteEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
#check exists_finiteEmpiricalBernsteinReverseSqrt_event
#check reverseSqrtFailure_mass_le_one_twentieth
#check balanced64_not_mem_reverseSqrtFailure
#check reverseSqrtBalanced64Ceiling_lt_ninetyNineHundredths
#check balanced64_reverse_sqrt_nonvacuous

#print axioms finiteEmpiricalBernsteinReverseDyadicFailure_mass_le_delta
#print axioms finiteEmpiricalBernsteinReverseDyadic_posteriorRisk_prefix_lt_sqrt_of_not_mem
#print axioms finiteEmpiricalBernsteinReverseGridDepth_coverage
#print axioms finiteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
#print axioms finiteEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
#print axioms exists_finiteEmpiricalBernsteinReverseSqrt_event
#print axioms reverseSqrtFailure_mass_le_one_twentieth
#print axioms balanced64_not_mem_reverseSqrtFailure
#print axioms reverseSqrtBalanced64Ceiling_lt_ninetyNineHundredths
#print axioms balanced64_reverse_sqrt_nonvacuous

end

end FormalSLT.Examples.CheckFiniteEmpiricalBernsteinReverseSqrt
