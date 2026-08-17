import FormalSLT

/-!
# Infinite-path empirical-Bernstein stitching receipt

This checker instantiates the stitched theorem on a fair Boolean iid stream.
Outside one measurable exceptional event of mass at most `1/20`, every sample
size at least two is controlled for a posterior selected from the first
observed coordinate.  Numerical
nonvacuity of the underlying closed-form boundary is checked separately by the
balanced-64 reverse empirical-Bernstein receipt.
-/

namespace FormalSLT.Examples.CheckInfiniteEmpiricalBernsteinStitch

open Finset BigOperators MeasureTheory
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.InfiniteProductMeasureBridge
open FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch

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

/-- A point posterior selected from the first observed coordinate. -/
def firstObservationPosterior (x : ℕ → Bool) : Bool → ℝ :=
  fun h ↦ if h = x 0 then 1 else 0

theorem firstObservationPosterior_isPMF (x : ℕ → Bool) :
    IsPMF (firstObservationPosterior x) := by
  constructor
  · intro h
    unfold firstObservationPosterior
    split <;> norm_num
  · cases hx : x 0 <;>
      simp [firstObservationPosterior, hx]

def fairBoolAllTimeBound (x : ℕ → Bool) (n : ℕ) : Prop :=
  posteriorAverage (firstObservationPosterior x)
      (finitePopulationRisk dataLaw matchLoss) <
    posteriorAverage (firstObservationPosterior x)
        (fun h ↦ finiteEmpiricalRisk matchLoss h (natSamplePrefix n x)) +
      (5 / 2 : ℝ) * Real.sqrt
        (posteriorAverage (firstObservationPosterior x)
            (fun h ↦ finiteEmpiricalVariance matchLoss h
              (natSamplePrefix n x)) *
          infiniteEmpiricalBernsteinComplexity n (1 / 20)
            fairPrior (firstObservationPosterior x) /
          (n : ℝ)) +
      5 *
        infiniteEmpiricalBernsteinComplexity n (1 / 20)
          fairPrior (firstObservationPosterior x) /
        (n : ℝ)

/-- Outside one `1/20`-mass exceptional event, all nontrivial prefix sizes are
controlled for the explicitly path-selected posterior. -/
theorem fairBool_allTime_selectedPosterior_receipt :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      Measure.infinitePi
          (fun _ : ℕ ↦ dataLaw_isPMF.toPMF.toMeasure) E ≤
        ENNReal.ofReal ((1 : ℝ) / 20) ∧
      ∀ x, x ∉ E → ∀ n : ℕ, 2 ≤ n → fairBoolAllTimeBound x n := by
  rcases exists_infiniteEmpiricalBernstein_event
      dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF matchLoss
      matchLoss_mem_Icc (delta := (1 : ℝ) / 20) (by norm_num) (by norm_num) with
    ⟨E, hEmeas, hEmass, hall⟩
  refine ⟨E, hEmeas, hEmass, ?_⟩
  intro x hx n hn
  exact hall x hx n hn (firstObservationPosterior x)
    (firstObservationPosterior_isPMF x)

#check measurePreserving_natSamplePrefix
#check natPrefix_iUnion_mass_le
#check reverseDyadicEpochIndex_spec
#check reverseDyadicEpochConfidence_tsum
#check infiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
#check infiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
#check infiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem
#check exists_infiniteEmpiricalBernsteinReverseSqrt_event
#check exists_infiniteEmpiricalBernstein_event
#check fairBool_allTime_selectedPosterior_receipt

#print axioms measurePreserving_natSamplePrefix
#print axioms natPrefix_iUnion_mass_le
#print axioms reverseDyadicEpochIndex_spec
#print axioms reverseDyadicEpochConfidence_tsum
#print axioms infiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
#print axioms infiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
#print axioms infiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem
#print axioms exists_infiniteEmpiricalBernsteinReverseSqrt_event
#print axioms exists_infiniteEmpiricalBernstein_event
#print axioms fairBool_allTime_selectedPosterior_receipt

end

end FormalSLT.Examples.CheckInfiniteEmpiricalBernsteinStitch
