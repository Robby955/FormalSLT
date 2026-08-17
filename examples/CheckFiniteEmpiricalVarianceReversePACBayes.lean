import FormalSLT.PACBayes.FiniteEmpiricalVarianceReversePACBayes
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Positive-KL checker for the reverse-epoch PAC-Bayes variance bound

This checker instantiates the reverse-epoch theorem with a fair Boolean data
law, two Boolean hypotheses, a fair full-support prior, and the point posterior
at `true`.  At horizon `N = 64`, endpoint `m = 32`, tilt `eta = 1/2`, and
failure level `delta = 1/20`, one event of product-law mass at most `1/20`
simultaneously controls every reverse time through `32`.

The point posterior has the strictly positive complexity `KL = log 2`.  On a
path outside the exceptional event, the theorem-produced retained-variance
ceiling lies strictly between the selected population variance `1/4` and the
trivial variance ceiling one at every controlled reverse time.  The posterior
used by this numerical receipt is fixed, although the checked library theorem
simultaneously permits every posterior selected after observing the path.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceReversePACBayes

open Finset BigOperators MeasureTheory Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

noncomputable section

/-- Fair law on the Boolean observation space. -/
def dataLaw (_ : Bool) : ℝ := (1 : ℝ) / 2

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    norm_num [dataLaw]
  · norm_num [dataLaw]

/-- Indicator losses: hypothesis `h` incurs loss one exactly on observation
`h`. -/
def matchLoss (h z : Bool) : ℝ := if z = h then 1 else 0

theorem matchLoss_mem_Icc (h z : Bool) :
    matchLoss h z ∈ Set.Icc (0 : ℝ) 1 := by
  cases h <;> cases z <;> norm_num [matchLoss]

/-- Fair full-support prior on the two hypotheses. -/
def fairPrior (_ : Bool) : ℝ := (1 : ℝ) / 2

theorem fairPrior_isFullSupportPMF : IsFullSupportPMF fairPrior := by
  constructor
  · constructor
    · intro h
      norm_num [fairPrior]
    · norm_num [fairPrior]
  · intro h
    norm_num [fairPrior]

/-- Point posterior at the `true` hypothesis. -/
def pointPosterior (h : Bool) : ℝ := if h then 1 else 0

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

theorem matchLoss_populationVariance (h : Bool) :
    finitePopulationVariance dataLaw matchLoss h = (1 : ℝ) / 4 := by
  cases h <;>
    norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw,
      matchLoss, Fintype.sum_bool]

theorem pointPosterior_populationVariance_eq_quarter :
    posteriorAverage pointPosterior
        (fun h ↦ finitePopulationVariance dataLaw matchLoss h) =
      (1 : ℝ) / 4 := by
  simp [posteriorAverage, pointPosterior, matchLoss_populationVariance]

/-- The exact all-posterior violation event has mass at most `1/20`. -/
theorem failure_mass_le_one_twentieth :
    Measure.pi (fun _ : Fin 64 ↦ dataLaw_isPMF.toPMF.toMeasure)
        (reverseBesselEpochAnyPosteriorFailure
          fairPrior 64 (by norm_num) 32 dataLaw matchLoss
          ((1 : ℝ) / 2) ((1 : ℝ) / 20)) ≤
      ENNReal.ofReal ((1 : ℝ) / 20) := by
  exact reverseBesselEpochAnyPosteriorFailure_mass_le_delta
    64 32 (by norm_num) (by norm_num) dataLaw dataLaw_isPMF
      fairPrior_isFullSupportPMF matchLoss matchLoss_mem_Icc
      (by norm_num) (by norm_num)

/-- The exceptional event cannot be the whole horizon sample space. -/
theorem exists_path_outside_failure :
    ∃ x : Fin 64 → Bool,
      x ∉ reverseBesselEpochAnyPosteriorFailure
        fairPrior 64 (by norm_num) 32 dataLaw matchLoss
        ((1 : ℝ) / 2) ((1 : ℝ) / 20) := by
  by_contra hnone
  have huniv :
      reverseBesselEpochAnyPosteriorFailure
          fairPrior 64 (by norm_num) 32 dataLaw matchLoss
          ((1 : ℝ) / 2) ((1 : ℝ) / 20) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact hnone ⟨x, hx⟩
  have hmass := failure_mass_le_one_twentieth
  rw [huniv, measure_univ] at hmass
  norm_num at hmass

/-- Every reverse-prefix Bessel variance in this instance is at most `1/2`. -/
theorem selectedReverseVariance_le_half (x : Fin 64 → Bool) (k : ℕ) :
    reverseBesselProcess 64 (by norm_num) (matchLoss true) k x ≤
      (1 : ℝ) / 2 := by
  simpa only [reverseBesselProcess, prefixBesselVariance,
    finiteEmpiricalVariance] using
    (finiteEmpiricalVariance_le_half
      (reverseBesselPrefixSize_two_le 64 k)
      matchLoss true
      (samplePrefix (reverseBesselPrefixSize_le (N := 64) (by norm_num) k) x)
      (fun j ↦ matchLoss_mem_Icc true
        (samplePrefix (reverseBesselPrefixSize_le (N := 64) (by norm_num) k) x j)))

/-- One-KL confidence complexity at `delta = 1/20` is below `19/5`.
The slack is chosen so that the final retained-variance ceiling still remains
strictly below one. -/
theorem pointPosterior_confidenceComplexity_lt_nineteen_fifths :
    klDiv pointPosterior fairPrior +
        Real.log (1 / ((1 : ℝ) / 20)) <
      (19 : ℝ) / 5 := by
  rw [pointPosterior_kl_eq_log_two]
  norm_num only [one_div, inv_div, inv_one]
  have hdecomp : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    calc
      Real.log 20 = Real.log ((2 : ℝ) ^ (2 : ℕ) * 5) := by norm_num
      _ = Real.log ((2 : ℝ) ^ (2 : ℕ)) + Real.log 5 := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = 2 * Real.log 2 + Real.log 5 := by
        rw [Real.log_pow]
        norm_num
  rw [hdecomp]
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

/-- The retained-variance upper endpoint produced by the theorem for the
point posterior. -/
def pointPosteriorVarianceCeiling (x : Fin 64 → Bool) (k : ℕ) : ℝ :=
  (posteriorAverage pointPosterior
        (fun h ↦ reverseBesselProcess 64 (by norm_num) (matchLoss h) k x) +
      (klDiv pointPosterior fairPrior +
        Real.log (1 / ((1 : ℝ) / 20))) /
        (((1 : ℝ) / 2) * (32 : ℝ))) /
    (1 - (((1 : ℝ) / 2) * (32 : ℝ)) /
      (2 * ((32 : ℝ) - 1)))

/-- Even after paying the positive point-posterior KL and 95%-confidence
penalty, the theorem's solved variance ceiling is strictly below one at every
reverse time. -/
theorem pointPosteriorVarianceCeiling_lt_one
    (x : Fin 64 → Bool) (k : ℕ) :
    pointPosteriorVarianceCeiling x k < 1 := by
  have hV := selectedReverseVariance_le_half x k
  have hL := pointPosterior_confidenceComplexity_lt_nineteen_fifths
  unfold pointPosteriorVarianceCeiling
  simp [posteriorAverage, pointPosterior]
  norm_num
  nlinarith

/-- On every good path and at every controlled reverse time, the selected
population variance `1/4` is below the theorem-produced ceiling, and that
ceiling is itself strictly below one. -/
theorem pointPosterior_uniform_nonvacuous_of_not_mem
    (x : Fin 64 → Bool)
    (hx : x ∉ reverseBesselEpochAnyPosteriorFailure
      fairPrior 64 (by norm_num) 32 dataLaw matchLoss
      ((1 : ℝ) / 2) ((1 : ℝ) / 20))
    (k : ℕ) (hk : k ≤ 32) :
    (1 : ℝ) / 4 < pointPosteriorVarianceCeiling x k ∧
      pointPosteriorVarianceCeiling x k < 1 := by
  have hbound := reverseBesselEpoch_posteriorVariance_lt_of_not_mem
    64 32 (by norm_num) (by norm_num) dataLaw fairPrior matchLoss
      (eta := (1 : ℝ) / 2) (delta := (1 : ℝ) / 20)
      (by norm_num) (by norm_num) x hx k (by norm_num at hk ⊢; exact hk)
      pointPosterior_isPMF
  constructor
  · rw [pointPosterior_populationVariance_eq_quarter] at hbound
    simpa [pointPosteriorVarianceCeiling] using hbound
  · exact pointPosteriorVarianceCeiling_lt_one x k

/-- A good horizon path exists, and on it the positive-KL solved certificate
is nonvacuous simultaneously at every reverse time in the epoch. -/
theorem exists_uniform_positiveKL_nonvacuous_certificate :
    0 < klDiv pointPosterior fairPrior ∧
      ∃ x : Fin 64 → Bool,
        x ∉ reverseBesselEpochAnyPosteriorFailure
            fairPrior 64 (by norm_num) 32 dataLaw matchLoss
            ((1 : ℝ) / 2) ((1 : ℝ) / 20) ∧
          ∀ k : ℕ, k ≤ 32 →
            (1 : ℝ) / 4 < pointPosteriorVarianceCeiling x k ∧
              pointPosteriorVarianceCeiling x k < 1 := by
  refine ⟨pointPosterior_kl_pos, ?_⟩
  obtain ⟨x, hx⟩ := exists_path_outside_failure
  exact ⟨x, hx, fun k hk ↦
    pointPosterior_uniform_nonvacuous_of_not_mem x hx k hk⟩

#check reverseBesselEpochAnyPosteriorFailure_mass_le_delta
#check reverseBesselEpoch_posteriorVariance_lt_of_not_mem
#check failure_mass_le_one_twentieth
#check pointPosterior_kl_pos
#check pointPosteriorVarianceCeiling_lt_one
#check exists_uniform_positiveKL_nonvacuous_certificate

#print axioms reverseBesselEpochAnyPosteriorFailure_mass_le_delta
#print axioms reverseBesselEpoch_posteriorVariance_lt_of_not_mem
#print axioms failure_mass_le_one_twentieth
#print axioms pointPosterior_kl_pos
#print axioms pointPosteriorVarianceCeiling_lt_one
#print axioms exists_uniform_positiveKL_nonvacuous_certificate

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceReversePACBayes
