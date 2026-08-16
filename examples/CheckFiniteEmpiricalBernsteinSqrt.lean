import FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Closed-form empirical-Bernstein PAC-Bayes receipt

This checker instantiates the canonical logarithmic-grid theorem at `n = 64`
and failure level `delta = 1/20`, hence confidence `19/20`. A balanced Boolean sample, fair prior,
and point posterior give all three load-bearing numerical features at once:
positive KL divergence, positive Bessel empirical variance, and a final
theorem-produced ceiling strictly below the loss upper bound one.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalBernsteinSqrt

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt

noncomputable section

def dataLaw : Bool → ℝ := fun _ => 1 / 2

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    norm_num [dataLaw]
  · norm_num [dataLaw]

def matchLoss (h z : Bool) : ℝ := if z = h then 1 else 0

theorem matchLoss_mem_Icc (h z : Bool) :
    matchLoss h z ∈ Set.Icc (0 : ℝ) 1 := by
  cases h <;> cases z <;> norm_num [matchLoss]

def fairPrior : Bool → ℝ := fun _ => 1 / 2

theorem fairPrior_isFullSupportPMF : IsFullSupportPMF fairPrior := by
  constructor
  · constructor
    · intro h
      norm_num [fairPrior]
    · norm_num [fairPrior]
  · intro h
    norm_num [fairPrior]

/-- A data-selected posterior is permitted by the theorem. The receipt uses
this fixed point posterior to activate a strictly positive KL term; the receipt
does not itself exercise data-dependent posterior selection. -/
def pointPosterior : Bool → ℝ := fun h => if h then 1 else 0

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

/-- Thirty-two false observations followed by thirty-two true observations. -/
def balanced64Sample : Fin 64 → Bool := fun k => decide (32 ≤ k.1)

theorem balanced64_sampleWeight_pos :
    0 < finiteProductSampleWeight dataLaw balanced64Sample := by
  unfold finiteProductSampleWeight
  apply Finset.prod_pos
  intro k _
  norm_num [dataLaw]

theorem card_fin64_ge_32 :
    (Finset.univ.filter (fun k : Fin 64 => 32 ≤ k.1)).card = 32 := by
  decide

theorem card_fin64_lt_32 :
    (Finset.univ.filter (fun k : Fin 64 => k.1 < 32)).card = 32 := by
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
          (fun k => matchLoss h (balanced64Sample k)) = 1 / 2 := by
    calc
      FormalSLT.Statistics.sampleMean
            (fun k => matchLoss h (balanced64Sample k)) =
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

theorem pointPosterior_balanced64_empiricalRisk :
    posteriorAverage pointPosterior
      (fun h => finiteEmpiricalRisk matchLoss h balanced64Sample) = 1 / 2 := by
  simp [posteriorAverage, pointPosterior, balanced64_empiricalRisk]

theorem pointPosterior_balanced64_empiricalVariance :
    posteriorAverage pointPosterior
        (fun h => finiteEmpiricalVariance matchLoss h balanced64Sample) =
      16 / 63 := by
  simp [posteriorAverage, pointPosterior, balanced64_empiricalVariance]

theorem pointPosterior_balanced64_empiricalVariance_pos :
    0 < posteriorAverage pointPosterior
      (fun h => finiteEmpiricalVariance matchLoss h balanced64Sample) := by
  rw [pointPosterior_balanced64_empiricalVariance]
  norm_num

theorem gridDepth64 : finiteEmpiricalBernsteinGridDepth 64 = 6 := by
  decide

/-- Every atom's normalized score is nonpositive on the balanced sample. -/
theorem balanced64_score_le_zero (j : Fin 7) (h : Bool) :
    finiteJointMeanVarianceScore 64 dataLaw matchLoss
        (finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        (finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        h balanced64Sample ≤ 0 := by
  let s := finiteEmpiricalBernsteinDyadicScale j.1
  let t := finiteEmpiricalBernsteinTiltOfScale s
  let eta := finiteEmpiricalBernsteinEtaOfScale s
  have hspos : 0 < s := finiteEmpiricalBernsteinDyadicScale_pos j.1
  have hsle : s ≤ 2 := finiteEmpiricalBernsteinDyadicScale_le_two j.1
  have ht_nonneg : 0 ≤ t := finiteEmpiricalBernsteinTiltOfScale_nonneg hspos.le
  have heta_nonneg : 0 ≤ eta :=
    finiteEmpiricalBernsteinEtaOfScale_nonneg hspos.le
  have hkappa_nonneg :
      0 ≤ finiteJointMeanVarianceKappa 64 eta :=
    finiteJointMeanVarianceKappa_scale_nonneg (by norm_num) hspos hsle
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

theorem balanced64_priorMoment_le_one (j : Fin 7) :
    finiteJointMeanVariancePriorMoment 64 dataLaw fairPrior matchLoss
        (finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        (finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        balanced64Sample ≤ 1 := by
  have hfalse := Real.exp_le_one_iff.mpr (balanced64_score_le_zero j false)
  have htrue := Real.exp_le_one_iff.mpr (balanced64_score_le_zero j true)
  simp only [finiteJointMeanVariancePriorMoment, Fintype.sum_bool]
  norm_num [fairPrior]
  linarith

theorem balanced64_masterMixture_le_one :
    finiteJointMeanVarianceMasterMixture 64 dataLaw fairPrior matchLoss
        (fun j : Fin 7 => finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        (fun j : Fin 7 => finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1))
        (finiteEmpiricalBernsteinDyadicWeight 6)
        balanced64Sample ≤ 1 := by
  unfold finiteJointMeanVarianceMasterMixture
  calc
    (∑ j : Fin 7,
        finiteEmpiricalBernsteinDyadicWeight 6 j *
          finiteJointMeanVariancePriorMoment 64 dataLaw fairPrior matchLoss
            (finiteEmpiricalBernsteinTiltOfScale
              (finiteEmpiricalBernsteinDyadicScale j.1))
            (finiteEmpiricalBernsteinEtaOfScale
              (finiteEmpiricalBernsteinDyadicScale j.1))
            balanced64Sample) ≤
        ∑ j : Fin 7, finiteEmpiricalBernsteinDyadicWeight 6 j * 1 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (balanced64_priorMoment_le_one j)
        (finiteEmpiricalBernsteinDyadicWeight_pos 6 j).le
    _ = 1 := by
      simpa using finiteEmpiricalBernsteinDyadicWeight_sum_eq_one 6

/-- The canonical exceptional set has mass at most `1/20`. -/
theorem sqrtBadSamples_mass_le_one_twentieth :
    (∑ S ∈ finiteEmpiricalBernsteinSqrtBadSamples
        64 dataLaw fairPrior matchLoss (1 / 20),
      finiteProductSampleWeight dataLaw S) ≤ (1 : ℝ) / 20 := by
  exact finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta
    (n := 64) (by norm_num) dataLaw dataLaw_isPMF
    fairPrior_isFullSupportPMF.toIsPMF matchLoss matchLoss_mem_Icc (by norm_num)

/-- The explicit positive-mass balanced sample is outside the exceptional set
used for the `19/20`-confidence statement. -/
theorem balanced64_not_mem_sqrtBadSamples :
    balanced64Sample ∉ finiteEmpiricalBernsteinSqrtBadSamples
      64 dataLaw fairPrior matchLoss (1 / 20) := by
  unfold finiteEmpiricalBernsteinSqrtBadSamples
  rw [gridDepth64]
  unfold finiteEmpiricalBernsteinDyadicBadSamples
    finiteEmpiricalBernsteinScaleBadSamples
  rw [finiteJointMeanVariance_not_mem_catalogBadSamples_iff]
  have hmaster := balanced64_masterMixture_le_one
  norm_num at hmaster ⊢
  linarith

/-- The exact displayed numerical ceiling produced by the theorem. -/
def balanced64Ceiling : ℝ :=
  1 / 2 +
    (5 / 4) * Real.sqrt ((Real.log 2 + Real.log 140) / 126) +
    (5 / 128) * (Real.log 2 + Real.log 140)

theorem pointPosterior_balanced64_certificate :
    posteriorAverage pointPosterior
        (finitePopulationRisk dataLaw matchLoss) ≤
      balanced64Ceiling := by
  have hbound :=
    finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem
      (n := 64) (delta := (1 : ℝ) / 20)
      (by norm_num) dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF
      matchLoss matchLoss_mem_Icc (by norm_num) (by norm_num)
      balanced64Sample balanced64_not_mem_sqrtBadSamples pointPosterior_isPMF
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
  simpa [balanced64Ceiling] using hbound

theorem balanced64Ceiling_lt_ninetyNineHundredths :
    balanced64Ceiling < (99 : ℝ) / 100 := by
  have hlog280 : Real.log 2 + Real.log 140 = Real.log 280 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (140 : ℝ) ≠ 0)]
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
  unfold balanced64Ceiling
  nlinarith

theorem balanced64Ceiling_lt_one : balanced64Ceiling < 1 := by
  linarith [balanced64Ceiling_lt_ninetyNineHundredths]

/-- One checked receipt combines positive KL, positive empirical variance,
and a theorem-produced risk ceiling below one. -/
theorem balanced64_positiveKL_positiveVariance_nonvacuous :
    0 < finiteProductSampleWeight dataLaw balanced64Sample ∧
      0 < klDiv pointPosterior fairPrior ∧
      0 < posteriorAverage pointPosterior
        (fun h => finiteEmpiricalVariance matchLoss h balanced64Sample) ∧
      posteriorAverage pointPosterior
          (finitePopulationRisk dataLaw matchLoss) ≤ balanced64Ceiling ∧
      balanced64Ceiling < 1 :=
  ⟨balanced64_sampleWeight_pos,
    pointPosterior_kl_pos,
    pointPosterior_balanced64_empiricalVariance_pos,
    pointPosterior_balanced64_certificate,
    balanced64Ceiling_lt_one⟩

#check finiteEmpiricalBernsteinScale_badSamples_mass_le_delta
#check finiteEmpiricalBernstein_posteriorRisk_le_scale_selected_of_not_mem
#check finiteEmpiricalBernsteinDyadic_badSamples_mass_le_delta
#check finiteEmpiricalBernsteinDyadic_posteriorRisk_le_sqrt_of_not_mem
#check finiteEmpiricalBernsteinGridDepth_coverage
#check finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta
#check finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem
#check sqrtBadSamples_mass_le_one_twentieth
#check balanced64_not_mem_sqrtBadSamples
#check balanced64Ceiling_lt_ninetyNineHundredths
#check balanced64_positiveKL_positiveVariance_nonvacuous

#print axioms finiteEmpiricalBernsteinScale_badSamples_mass_le_delta
#print axioms finiteEmpiricalBernstein_posteriorRisk_le_scale_selected_of_not_mem
#print axioms finiteEmpiricalBernsteinDyadic_badSamples_mass_le_delta
#print axioms finiteEmpiricalBernsteinDyadic_posteriorRisk_le_sqrt_of_not_mem
#print axioms finiteEmpiricalBernsteinGridDepth_coverage
#print axioms finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta
#print axioms finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem
#print axioms sqrtBadSamples_mass_le_one_twentieth
#print axioms balanced64_not_mem_sqrtBadSamples
#print axioms balanced64Ceiling_lt_ninetyNineHundredths
#print axioms balanced64_positiveKL_positiveVariance_nonvacuous

end

end FormalSLT.Examples.CheckFiniteEmpiricalBernsteinSqrt
