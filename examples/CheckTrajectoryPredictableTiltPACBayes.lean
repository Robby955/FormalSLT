import FormalSLT.StochasticDynamics.TrajectoryPredictableTiltPACBayes

/-!
# Full-prefix predictable-tilt PAC-Bayes checker

The Boolean receipt uses a tilt rule that reads the current trajectory prefix.
The schedule is fixed as a rule before sampling, while the common event covers
every time and allows the posterior to depend on the realized path.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckTrajectoryPredictableTiltPACBayes

open FormalSLT.StochasticDynamics

noncomputable section

/-- A fair next-state law, expressed through the full-prefix kernel API. -/
def fairBoolPMF : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    simp only [Fintype.sum_bool]
    have hhalf : ((1 / 2 : NNReal) : ENNReal) = (1 : ENNReal) / 2 := by
      rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
      norm_num
    rw [hhalf]
    exact ENNReal.add_halves 1)

def fairPrefixBoolKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Bool) Bool :=
  Kernel.ofFunOfCountable fun _ ↦ fairBoolPMF.toMeasure

instance fairPrefixBoolKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (fairPrefixBoolKernel n) :=
  ⟨fun _ ↦ by
    change IsProbabilityMeasure fairBoolPMF.toMeasure
    infer_instance⟩

/-- Two bounded score atoms, one for each Boolean next-state label. -/
def labelScore (i : Bool) : TrajectoryScore Bool :=
  fun _n _u y ↦ if y = i then 1 else 0

theorem labelScore_mem_Icc :
    ∀ i n u y, labelScore i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  simp only [labelScore]
  split_ifs <;> norm_num

/-- A fixed-before-data rule whose value depends on the current path prefix. -/
def prefixMatchingTilt (i : Bool) : TrajectoryPredictableTilt Bool :=
  fun n u ↦ if u ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = i then 1 / 2 else 1 / 4

theorem prefixMatchingTilt_range (i : Bool) (n : ℕ)
    (u : (j : Finset.Iic n) → Bool) :
    0 ≤ prefixMatchingTilt i n u ∧
      prefixMatchingTilt i n u ≤ (1 / 2 : ℝ) := by
  simp only [prefixMatchingTilt]
  split_ifs <;> norm_num

def allFalsePath (_n : ℕ) : Bool := false

def allTruePath (_n : ℕ) : Bool := true

/-- The supplied predictable rule is genuinely path dependent. -/
theorem prefixMatchingTilt_nonconstant :
    prefixMatchingTilt true 1 (Preorder.frestrictLe 1 allTruePath) ≠
      prefixMatchingTilt true 1 (Preorder.frestrictLe 1 allFalsePath) := by
  norm_num [prefixMatchingTilt, Preorder.frestrictLe_apply,
    allTruePath, allFalsePath]

def uniformBoolPrior (_i : Bool) : ℝ := 1 / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]
  · norm_num [uniformBoolPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]

def pointPosterior (selected i : Bool) : ℝ :=
  if i = selected then 1 else 0

theorem pointPosterior_isPMF (selected : Bool) :
    IsPMF (pointPosterior selected) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases selected <;> fin_cases i <;> norm_num [pointPosterior]
  · fin_cases selected <;> norm_num [pointPosterior, Fintype.sum_bool]

def pathPosterior (x : ℕ → Bool) (_n : ℕ) : Bool → ℝ :=
  pointPosterior (x 1)

theorem pathPosterior_isPMF (x : ℕ → Bool) (n : ℕ) :
    IsPMF (pathPosterior x n) := pointPosterior_isPMF _

/-- Concrete full-prefix trajectory instance of the selected-posterior
predictable-tilt theorem. -/
theorem boolTrajectoryPredictableTiltPACBayes_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (trajectoryMeasure fairPrefixBoolKernel false).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ,
          trajectoryPredictableTiltPosteriorMeanGap
              fairPrefixBoolKernel labelScore prefixMatchingTilt
                (pathPosterior x n) n x <
            klDiv (pathPosterior x n) uniformBoolPrior +
              Real.log (1 / (1 / 20 : ℝ)) +
                trajectoryPredictableTiltPosteriorQuadraticPenalty
                  labelScore prefixMatchingTilt (pathPosterior x n) n x := by
  exact exists_trajectoryPredictableTiltPACBayes_selected_event
    (ι := Bool) fairPrefixBoolKernel false labelScore_mem_Icc
      (L := (1 / 2 : ℝ)) (by norm_num) prefixMatchingTilt_range
      uniformBoolPrior_isFullSupportPMF (delta := (1 / 20 : ℝ))
      (by norm_num) pathPosterior pathPosterior_isPMF

/-- The same Boolean model exercises the normalized tilt-weighted risk API.
The positivity premise is explicit because a zero total tilt carries no risk
information. -/
theorem boolTrajectoryPredictableTiltPACBayes_normalized_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (trajectoryMeasure fairPrefixBoolKernel false).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ,
          0 < trajectoryPredictableTiltPosteriorTotalWeight
              prefixMatchingTilt (pathPosterior x n) n x →
            trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
                fairPrefixBoolKernel labelScore prefixMatchingTilt
                  (pathPosterior x n) n x <
              trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
                  labelScore prefixMatchingTilt (pathPosterior x n) n x +
                (klDiv (pathPosterior x n) uniformBoolPrior +
                    Real.log (1 / (1 / 20 : ℝ)) +
                    trajectoryPredictableTiltPosteriorQuadraticPenalty
                      labelScore prefixMatchingTilt (pathPosterior x n) n x) /
                  trajectoryPredictableTiltPosteriorTotalWeight
                    prefixMatchingTilt (pathPosterior x n) n x := by
  exact exists_trajectoryPredictableTiltPACBayes_normalized_selected_event
    (ι := Bool) fairPrefixBoolKernel false labelScore_mem_Icc
      (L := (1 / 2 : ℝ)) (by norm_num) prefixMatchingTilt_range
      uniformBoolPrior_isFullSupportPMF (delta := (1 / 20 : ℝ))
      (by norm_num) pathPosterior pathPosterior_isPMF

#check TrajectoryPredictableTilt
#check observedTrajectoryPredictableTilt_stronglyAdapted
#check trajectoryPredictableTiltPosteriorMeanGap
#check trajectoryPredictableTiltPosteriorQuadraticPenalty
#check trajectoryPredictableTiltPosteriorTotalWeight
#check trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
#check trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
#check exists_trajectoryPredictableTiltPACBayes_event
#check exists_trajectoryPredictableTiltPACBayes_selected_event
#check exists_trajectoryPredictableTiltPACBayes_normalized_event
#check exists_trajectoryPredictableTiltPACBayes_normalized_selected_event
#check prefixMatchingTilt_nonconstant
#check boolTrajectoryPredictableTiltPACBayes_certificate
#check boolTrajectoryPredictableTiltPACBayes_normalized_certificate

#print axioms observedTrajectoryPredictableTilt_stronglyAdapted
#print axioms exists_trajectoryPredictableTiltPACBayes_event
#print axioms exists_trajectoryPredictableTiltPACBayes_selected_event
#print axioms exists_trajectoryPredictableTiltPACBayes_normalized_event
#print axioms exists_trajectoryPredictableTiltPACBayes_normalized_selected_event
#print axioms prefixMatchingTilt_nonconstant
#print axioms boolTrajectoryPredictableTiltPACBayes_certificate
#print axioms boolTrajectoryPredictableTiltPACBayes_normalized_certificate

end

end FormalSLT.Examples.CheckTrajectoryPredictableTiltPACBayes
