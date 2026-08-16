import FormalSLT.PACBayes.FiniteJointMeanVarianceReversePACBayes
import FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Joint reverse-epoch empirical-Bernstein PAC-Bayes receipt

This checker instantiates the one-event reverse-epoch theorem at horizon and
endpoint `N = m = 64`, scale one, and failure level `delta = 1/20`.  A fair
Boolean law, fair prior, point posterior, and explicit balanced sample verify
positive KL, positive Bessel empirical variance, membership in the exact good
event, and a theorem-produced population-risk ceiling strictly below one.

The theorem itself permits a posterior selected after the horizon sample.  The
receipt uses a fixed point posterior to make the positive KL term explicit.
-/

namespace FormalSLT.Examples.CheckFiniteJointMeanVarianceReversePACBayes

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

/-- A fixed point posterior, used only to expose a strictly positive KL term. -/
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

/-- Thirty-two false observations followed by thirty-two true observations. -/
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
          (samplePrefix (Nat.le_refl 64) balanced64Sample)) =
      16 / 63 := by
  rw [samplePrefix_balanced64_eq]
  simp [posteriorAverage, pointPosterior, balanced64_empiricalVariance]

theorem pointPosterior_balanced64_empiricalVariance_pos :
    0 < posteriorAverage pointPosterior
      (fun h ↦ finiteEmpiricalVariance matchLoss h
        (samplePrefix (Nat.le_refl 64) balanced64Sample)) := by
  rw [pointPosterior_balanced64_empiricalVariance]
  norm_num

/-- Scale one produces mean tilt `1/3`. -/
def certT : ℝ := finiteEmpiricalBernsteinTiltOfScale 1

/-- Scale one produces variance tilt `1/6`. -/
def certEta : ℝ := finiteEmpiricalBernsteinEtaOfScale 1

theorem certT_eq : certT = 1 / 3 := by
  norm_num [certT, finiteEmpiricalBernsteinTiltOfScale]

theorem certEta_eq : certEta = 1 / 6 := by
  norm_num [certEta, finiteEmpiricalBernsteinEtaOfScale]

theorem certT_pos : 0 < certT := by
  rw [certT_eq]
  norm_num

theorem certEta_nonneg : 0 ≤ certEta := by
  rw [certEta_eq]
  norm_num

theorem certKappa_nonneg :
    0 ≤ finiteJointMeanVarianceKappa 64 certEta := by
  exact finiteJointMeanVarianceKappa_scale_nonneg
    (n := 64) (s := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem certBalance :
    (64 : ℝ) * (Real.exp certT - 1 - certT) ≤
      Real.exp (-certT) * finiteJointMeanVarianceKappa 64 certEta := by
  exact finiteJointMeanVariance_balance_of_scale
    (n := 64) (s := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

/-- Every hypothesis has a nonpositive endpoint score on the balanced path. -/
theorem balanced64_reverseScore_le_zero (h : Bool) :
    reverseJointMeanVarianceEpochScore
      64 (by norm_num) 64 dataLaw matchLoss certT certEta h 0 balanced64Sample ≤ 0 := by
  have hkappa_nonneg :
      0 ≤ finiteJointMeanVarianceKappa 64 certEta := certKappa_nonneg
  have hkappa_le : finiteJointMeanVarianceKappa 64 certEta ≤ 64 * certEta := by
    unfold finiteJointMeanVarianceKappa
    norm_num
    nlinarith [sq_nonneg certEta]
  have hexp : Real.exp (-certT) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [certT_pos])
  have hcorrection :
      Real.exp (-certT) * finiteJointMeanVarianceKappa 64 certEta * (1 / 4) ≤
        16 * certEta := by
    have hfirst :
        Real.exp (-certT) * finiteJointMeanVarianceKappa 64 certEta ≤
          finiteJointMeanVarianceKappa 64 certEta := by
      simpa using mul_le_mul_of_nonneg_right hexp hkappa_nonneg
    nlinarith
  have hpsi : 0 ≤ Real.exp certT - 1 - certT := by
    linarith [Real.add_one_le_exp certT]
  have hlog :
      0 ≤ Real.log (1 + (Real.exp certT - 1 - certT) * (1 / 4)) := by
    exact Real.log_nonneg (by nlinarith)
  rw [show (0 : ℕ) = 64 - 64 by norm_num,
    reverseJointMeanVarianceEpochScore_endpoint
      (N := 64) (m := 64) (by norm_num) ⟨by norm_num, by norm_num⟩]
  rw [samplePrefix_balanced64_eq]
  unfold finiteJointMeanVarianceScore
  rw [matchLoss_populationRisk, balanced64_empiricalRisk,
    balanced64_empiricalVariance, matchLoss_populationVariance]
  change
    certT * 64 * (1 / 2 - 1 / 2) - certEta * 64 * (16 / 63) -
        64 * Real.log (1 + (Real.exp certT - 1 - certT) * (1 / 4)) +
        Real.exp (-certT) * finiteJointMeanVarianceKappa 64 certEta * (1 / 4) ≤ 0
  nlinarith

/-- The explicit balanced path is outside the exact all-posterior failure
event, not merely outside a looser surrogate crossing set. -/
theorem balanced64_not_mem_exactFailure :
    balanced64Sample ∉ reverseJointMeanVarianceEpochAnyPosteriorFailure
      fairPrior 64 (by norm_num) 64 dataLaw matchLoss certT certEta (1 / 20) := by
  intro hx
  rcases hx with ⟨k, hk, rho, hrho, hfail⟩
  have hk0 : k = 0 := by omega
  subst k
  have hscore :
      posteriorAverage rho
          (fun h ↦ reverseJointMeanVarianceEpochScore
            64 (by norm_num) 64 dataLaw matchLoss certT certEta h 0
              balanced64Sample) ≤ 0 := by
    unfold posteriorAverage
    exact Finset.sum_nonpos fun h _ ↦
      mul_nonpos_of_nonneg_of_nonpos (hrho.nonneg h)
        (balanced64_reverseScore_le_zero h)
  have hkl : 0 ≤ klDiv rho fairPrior :=
    klDiv_nonneg hrho fairPrior_isFullSupportPMF
  have hconfidence : 0 < Real.log (1 / ((1 : ℝ) / 20)) :=
    Real.log_pos (by norm_num)
  linarith

/-- The exact exceptional event has probability at most `1/20`. -/
theorem reverseFailure_mass_le_one_twentieth :
    Measure.pi (fun _ : Fin 64 ↦ dataLaw_isPMF.toPMF.toMeasure)
        (reverseJointMeanVarianceEpochAnyPosteriorFailure
          fairPrior 64 (by norm_num) 64 dataLaw matchLoss certT certEta (1 / 20)) ≤
      ENNReal.ofReal ((1 : ℝ) / 20) := by
  exact reverseJointMeanVarianceEpochAnyPosteriorFailure_mass_le_delta
    64 64 (by norm_num) ⟨by norm_num, by norm_num⟩
    dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF matchLoss
    matchLoss_mem_Icc certT_pos.le certEta_nonneg certKappa_nonneg (by norm_num)

/-- Numerical endpoint ceiling delivered by the reverse-epoch theorem. -/
def reverseBalanced64Ceiling : ℝ :=
  1 / 2 +
    (Real.log 2 + Real.log 20) / ((1 / 3) * 64) +
    ((1 / 6) / (1 / 3)) * (16 / 63)

theorem pointPosterior_balanced64_risk_lt_ceiling :
    posteriorAverage pointPosterior
        (finitePopulationRisk dataLaw matchLoss) <
      reverseBalanced64Ceiling := by
  have hbound :=
    reverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem
      64 64 64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      dataLaw dataLaw_isPMF fairPrior matchLoss certT_pos certBalance
      balanced64Sample balanced64_not_mem_exactFailure pointPosterior_isPMF
  rw [pointPosterior_kl_eq_log_two,
    pointPosterior_balanced64_empiricalRisk,
    pointPosterior_balanced64_empiricalVariance,
    certT_eq, certEta_eq] at hbound
  simpa [reverseBalanced64Ceiling] using hbound

theorem reverseBalanced64Ceiling_lt_one :
    reverseBalanced64Ceiling < 1 := by
  have hlog40 : Real.log 2 + Real.log 20 = Real.log 40 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (20 : ℝ) ≠ 0)]
    norm_num
  have hlog40_expand : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    calc
      Real.log 40 = Real.log ((2 : ℝ) ^ 3 * 5) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log 5 := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = 3 * Real.log 2 + Real.log 5 := by
        rw [Real.log_pow]
        norm_num
  have hL : Real.log 2 + Real.log 20 < 4 := by
    rw [hlog40, hlog40_expand]
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  unfold reverseBalanced64Ceiling
  norm_num
  nlinarith

/-- One concrete receipt combines exact-event membership, positive atom
weight, positive KL, positive empirical variance, and a nonvacuous risk
ceiling at confidence `19/20`. -/
theorem balanced64_reverse_epoch_nonvacuous :
    0 < finiteProductSampleWeight dataLaw balanced64Sample ∧
      balanced64Sample ∉ reverseJointMeanVarianceEpochAnyPosteriorFailure
        fairPrior 64 (by norm_num) 64 dataLaw matchLoss certT certEta (1 / 20) ∧
      0 < klDiv pointPosterior fairPrior ∧
      0 < posteriorAverage pointPosterior
        (fun h ↦ finiteEmpiricalVariance matchLoss h
          (samplePrefix (Nat.le_refl 64) balanced64Sample)) ∧
      posteriorAverage pointPosterior
          (finitePopulationRisk dataLaw matchLoss) < reverseBalanced64Ceiling ∧
      reverseBalanced64Ceiling < 1 :=
  ⟨balanced64_sampleWeight_pos,
    balanced64_not_mem_exactFailure,
    pointPosterior_kl_pos,
    pointPosterior_balanced64_empiricalVariance_pos,
    pointPosterior_balanced64_risk_lt_ceiling,
    reverseBalanced64Ceiling_lt_one⟩

#check reverseJointMeanVarianceEpochAnyPosteriorFailure_mass_le_delta
#check reverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem
#check exists_reverseJointMeanVarianceEpoch_event
#check reverseFailure_mass_le_one_twentieth
#check balanced64_not_mem_exactFailure
#check pointPosterior_balanced64_risk_lt_ceiling
#check balanced64_reverse_epoch_nonvacuous

#print axioms reverseJointMeanVarianceEpochAnyPosteriorFailure_mass_le_delta
#print axioms reverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem
#print axioms exists_reverseJointMeanVarianceEpoch_event
#print axioms reverseFailure_mass_le_one_twentieth
#print axioms balanced64_not_mem_exactFailure
#print axioms pointPosterior_balanced64_risk_lt_ceiling
#print axioms balanced64_reverse_epoch_nonvacuous

end

end FormalSLT.Examples.CheckFiniteJointMeanVarianceReversePACBayes
