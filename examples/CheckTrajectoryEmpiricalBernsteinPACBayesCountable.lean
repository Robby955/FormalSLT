import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayesCountable

/-!
# Countable-tilt trajectory empirical-Bernstein PAC-Bayes checks

The receipt reuses the genuinely history-dependent Boolean architecture from
the finite-tilt trajectory checker.  Both the transition row and one score
atom inspect the interior coordinate `u 1`; the two witness histories start at
the certified initial state and agree at the current state.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckTrajectoryEmpiricalBernsteinPACBayesCountable

open FormalSLT.StochasticDynamics

noncomputable section

def countableInteriorState (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) : Bool :=
  if h : 1 ≤ n then
    u ⟨1, Finset.mem_Iic.mpr h⟩
  else
    u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

def countableHistoryDependentBoolPMF (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y = countableInteriorState n u
      then ((3 / 4 : NNReal) : ENNReal)
      else ((1 / 4 : NNReal) : ENNReal))
    (by
      have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hsum : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      cases h : countableInteriorState n u <;>
        simpa [Fintype.sum_bool, h, add_comm] using hsum)

def countableHistoryDependentBoolKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Bool) Bool :=
  Kernel.ofFunOfCountable fun u ↦
    (countableHistoryDependentBoolPMF n u).toMeasure

instance countableHistoryDependentBoolKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (countableHistoryDependentBoolKernel n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure (countableHistoryDependentBoolPMF n u).toMeasure
    infer_instance⟩

def countableHistoryDependentBoolScore (i : Bool) : TrajectoryScore Bool :=
  fun n u y ↦
    if i then
      if y = u ⟨n, Finset.mem_Iic.mpr le_rfl⟩ then 1 else 0
    else
      if y = countableInteriorState n u then 1 else 0

theorem countableHistoryDependentBoolScore_mem_Icc :
    ∀ i n u y,
      countableHistoryDependentBoolScore i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  fin_cases i <;> simp [countableHistoryDependentBoolScore] <;>
    split_ifs <;> norm_num

def countableFalseTrueFalsePath (n : ℕ) : Bool := decide (n = 1)

def countableAllFalsePath (_n : ℕ) : Bool := false

/-- The kernel really distinguishes two same-initial, same-current histories
by their interior coordinate. -/
theorem countableHistoryDependentBool_kernel_witness :
    countableFalseTrueFalsePath 0 = false ∧
      countableAllFalsePath 0 = false ∧
      countableFalseTrueFalsePath 2 = countableAllFalsePath 2 ∧
      countableHistoryDependentBoolPMF 2
          (Preorder.frestrictLe 2 countableFalseTrueFalsePath) true = 3 / 4 ∧
      countableHistoryDependentBoolPMF 2
          (Preorder.frestrictLe 2 countableAllFalsePath) true = 1 / 4 := by
  constructor
  · simp [countableFalseTrueFalsePath]
  constructor
  · simp [countableAllFalsePath]
  constructor
  · simp [countableFalseTrueFalsePath, countableAllFalsePath]
  constructor <;>
    norm_num [countableHistoryDependentBoolPMF, countableInteriorState,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply,
      countableFalseTrueFalsePath, countableAllFalsePath]

def countableUniformBoolPrior (_i : Bool) : ℝ := 1 / 2

theorem countableUniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF countableUniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [countableUniformBoolPrior]
  · norm_num [countableUniformBoolPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [countableUniformBoolPrior]

def countablePointPosterior (selected i : Bool) : ℝ :=
  if i = selected then 1 else 0

theorem countablePointPosterior_isPMF (selected : Bool) :
    IsPMF (countablePointPosterior selected) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases selected <;> fin_cases i <;>
      norm_num [countablePointPosterior]
  · fin_cases selected <;>
      norm_num [countablePointPosterior, Fintype.sum_bool]

def countablePathPosterior (x : ℕ → Bool) (_n : ℕ) : Bool → ℝ :=
  countablePointPosterior (x 1)

theorem countablePathPosterior_isPMF (x : ℕ → Bool) (n : ℕ) :
    IsPMF (countablePathPosterior x n) :=
  countablePointPosterior_isPMF _

/-- Concrete capstone: one event, arbitrary path-selected posterior, the
explicit every-time atom, and a checked exact boundary tending to zero. -/
theorem countableHistoryDependentBool_allTime_vanishing_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (trajectoryMeasure countableHistoryDependentBoolKernel false).real
          goodEventᶜ ≤ 1 / 20 ∧
        (∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          trajectoryPosteriorAverageConditionalRisk
              countableHistoryDependentBoolKernel
              countableHistoryDependentBoolScore
              (countablePathPosterior x n) n x <
            trajectoryPosteriorEmpiricalPrequentialRisk
                countableHistoryDependentBoolScore
                (countablePathPosterior x n) n x +
              trajectoryCountableEmpiricalBernsteinPACBayesBoundary
                countableUniformBoolPrior countableHistoryDependentBoolScore
                (countablePathPosterior x n) (1 / 20)
                (geometricForwardTiltIndex n) n x) ∧
        (∀ x ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦
              trajectoryCountableEmpiricalBernsteinPACBayesBoundary
                countableUniformBoolPrior countableHistoryDependentBoolScore
                (countablePathPosterior x n) (1 / 20)
                (geometricForwardTiltIndex n) n x)
            Filter.atTop (nhds 0)) := by
  exact
    exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event
      (ι := Bool) countableHistoryDependentBoolKernel false
      countableHistoryDependentBoolScore_mem_Icc
      countableUniformBoolPrior_isFullSupportPMF
      (delta := (1 / 20 : ℝ)) (by norm_num) (by norm_num)
      countablePathPosterior countablePathPosterior_isPMF

/-! Public theorem and concrete receipt audit. -/

#check trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
#check trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_singleton
#check trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent_mass_le
#check trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
#check trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
#check exists_trajectoryCountableEmpiricalBernsteinPACBayes_event
#check trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_le_rate
#check trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_tendsto_zero
#check exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event

#print axioms trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
#print axioms trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_singleton
#print axioms trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent_mass_le
#print axioms trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
#print axioms trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
#print axioms exists_trajectoryCountableEmpiricalBernsteinPACBayes_event
#print axioms trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_le_rate
#print axioms trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_tendsto_zero
#print axioms exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event

#check countableHistoryDependentBool_kernel_witness
#check countableHistoryDependentBool_allTime_vanishing_certificate

#print axioms countableHistoryDependentBool_kernel_witness
#print axioms countableHistoryDependentBool_allTime_vanishing_certificate

end

end FormalSLT.Examples.CheckTrajectoryEmpiricalBernsteinPACBayesCountable
