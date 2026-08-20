/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueReindex
import FormalSLT.StochasticDynamics.ControlledKernelTV
import Mathlib.Data.Rat.Cast.Order

/-!
# Typed controlled-queue model

This module turns the generated exact rational kernel and policy tables into
finite `PMF` objects.  The conversion is direct: every mass is read from
`candidateKernelTable` or `policyTable`, with proof-carrying bounds for every
nested `List.get`.  There is no default value and no reconstructed copy of the
queue model.

The generated kernel rows are state-major/action-minor, while controlled
observations are action--state pairs.  For a transition
`(previousAction, state) -> (action, nextState)`, the environment row is
`transitionRow current next`, hence it depends on `state` and `action`; the
next state is only the column index.

The behavior policy is exactly uniform.  Consequently an augmented
behavior-kernel row-TV bound `eta` controls any one action-conditioned
environment row by `2 * eta`.  This is the inverse behavior-probability price,
not an additional total-variation normalization factor.

This remains a typed model bridge.  It does not identify any candidate with
the true environment, import the frozen trace, or prove a target-policy OPE
certificate.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

noncomputable section

/-- Indices of the three generated candidate environments. -/
abbrev CandidateIndex := Fin 3

/-- Indices of the generated behavior policy followed by four target policies. -/
abbrev PolicyIndex := Fin 5

/-- Indices of the four generated target policies. -/
abbrev TargetPolicyIndex := Fin 4

/-- The behavior policy occupies row zero of `policyTable`. -/
def behaviorPolicyIndex : PolicyIndex := 0

/-- Target policy `i` occupies policy-table row `i + 1`. -/
def targetPolicyTableIndex (target : TargetPolicyIndex) : PolicyIndex :=
  ⟨target.val + 1, by omega⟩

private theorem candidateKernelTable_length :
    candidateKernelTable.length = 3 := rfl

private abbrev candidateRows (candidate : CandidateIndex) : List (List ℚ) :=
  candidateKernelTable.get
    (Fin.cast candidateKernelTable_length.symm candidate)

private theorem candidateRows_length (candidate : CandidateIndex) :
    (candidateRows candidate).length = 48 := by
  fin_cases candidate <;> rfl

private abbrev candidateRow
    (candidate : CandidateIndex) (row : Fin 48) : List ℚ :=
  (candidateRows candidate).get
    (Fin.cast (candidateRows_length candidate).symm row)

private theorem candidateRow_length
    (candidate : CandidateIndex) (row : Fin 48) :
    (candidateRow candidate row).length = 24 := by
  fin_cases candidate <;> fin_cases row <;> rfl

/-- Exact rational mass in a generated candidate environment row. -/
def candidateKernelTableMass
    (candidate : CandidateIndex) (row : Fin 48)
    (nextState : PhysicalState) : ℚ :=
  (candidateRow candidate row).get
    (Fin.cast (candidateRow_length candidate row).symm nextState)

private theorem policyTable_length : policyTable.length = 5 := rfl

private abbrev policyRows (policy : PolicyIndex) : List (List ℚ) :=
  policyTable.get (Fin.cast policyTable_length.symm policy)

private theorem policyRows_length (policy : PolicyIndex) :
    (policyRows policy).length = 24 := by
  fin_cases policy <;> rfl

private abbrev policyRow
    (policy : PolicyIndex) (state : PhysicalState) : List ℚ :=
  (policyRows policy).get
    (Fin.cast (policyRows_length policy).symm state)

private theorem policyRow_length
    (policy : PolicyIndex) (state : PhysicalState) :
    (policyRow policy state).length = 2 := by
  fin_cases policy <;> fin_cases state <;> rfl

/-- Exact rational action mass in a generated policy row. -/
def policyTableMass
    (policy : PolicyIndex) (state : PhysicalState) (action : Action) : ℚ :=
  (policyRow policy state).get
    (Fin.cast (policyRow_length policy state).symm action)

private theorem candidateRows_all_pos_0 :
    ∀ row ∈ candidateRows (0 : CandidateIndex),
      ∀ mass ∈ row, 0 < mass := by
  norm_num [candidateRows, candidateKernelTable]

private theorem candidateRows_all_pos_1 :
    ∀ row ∈ candidateRows (1 : CandidateIndex),
      ∀ mass ∈ row, 0 < mass := by
  norm_num [candidateRows, candidateKernelTable]

private theorem candidateRows_all_pos_2 :
    ∀ row ∈ candidateRows (2 : CandidateIndex),
      ∀ mass ∈ row, 0 < mass := by
  norm_num [candidateRows, candidateKernelTable]

private theorem candidateRows_all_pos
    (candidate : CandidateIndex) :
    ∀ row ∈ candidateRows candidate, ∀ mass ∈ row, 0 < mass := by
  fin_cases candidate
  · exact candidateRows_all_pos_0
  · exact candidateRows_all_pos_1
  · exact candidateRows_all_pos_2

/-- Every generated candidate-kernel entry is strictly positive. -/
theorem candidateKernelTableMass_pos
    (candidate : CandidateIndex) (row : Fin 48)
    (nextState : PhysicalState) :
    0 < candidateKernelTableMass candidate row nextState := by
  exact candidateRows_all_pos candidate
    (candidateRow candidate row) (List.get_mem _ _)
    (candidateKernelTableMass candidate row nextState) (List.get_mem _ _)

private theorem candidateRows_sum_one_0 :
    ∀ row ∈ candidateRows (0 : CandidateIndex), row.sum = 1 := by
  norm_num [candidateRows, candidateKernelTable]

private theorem candidateRows_sum_one_1 :
    ∀ row ∈ candidateRows (1 : CandidateIndex), row.sum = 1 := by
  norm_num [candidateRows, candidateKernelTable]

private theorem candidateRows_sum_one_2 :
    ∀ row ∈ candidateRows (2 : CandidateIndex), row.sum = 1 := by
  norm_num [candidateRows, candidateKernelTable]

private theorem candidateRows_sum_one (candidate : CandidateIndex) :
    ∀ row ∈ candidateRows candidate, row.sum = 1 := by
  fin_cases candidate
  · exact candidateRows_sum_one_0
  · exact candidateRows_sum_one_1
  · exact candidateRows_sum_one_2

private theorem sum_get_cast_eq_sum
    (xs : List ℚ) {n : ℕ} (h : xs.length = n) :
    (∑ i : Fin n, xs.get (Fin.cast h.symm i)) = xs.sum := by
  subst n
  simp

private theorem candidateKernelTableMass_sum_one_rat
    (candidate : CandidateIndex) (row : Fin 48) :
    ∑ nextState : PhysicalState,
      candidateKernelTableMass candidate row nextState = 1 := by
  calc
    ∑ nextState : PhysicalState,
        candidateKernelTableMass candidate row nextState =
        (candidateRow candidate row).sum := by
          simpa only [candidateKernelTableMass] using
            sum_get_cast_eq_sum (candidateRow candidate row)
              (candidateRow_length candidate row)
    _ = 1 := candidateRows_sum_one candidate
      (candidateRow candidate row) (List.get_mem _ _)

/-- Every generated candidate-kernel row has exact real mass one. -/
theorem candidateKernelTableMass_sum_one
    (candidate : CandidateIndex) (row : Fin 48) :
    ∑ nextState : PhysicalState,
      (candidateKernelTableMass candidate row nextState : ℝ) = 1 := by
  exact_mod_cast candidateKernelTableMass_sum_one_rat candidate row

private theorem policyRows_all_bounds_0 :
    ∀ row ∈ policyRows (0 : PolicyIndex), ∀ mass ∈ row,
      0 < mass ∧ (mass : ℝ) ≤ 3 / 4 := by
  norm_num [policyRows, policyTable]

private theorem policyRows_all_bounds_1 :
    ∀ row ∈ policyRows (1 : PolicyIndex), ∀ mass ∈ row,
      0 < mass ∧ (mass : ℝ) ≤ 3 / 4 := by
  norm_num [policyRows, policyTable]

private theorem policyRows_all_bounds_2 :
    ∀ row ∈ policyRows (2 : PolicyIndex), ∀ mass ∈ row,
      0 < mass ∧ (mass : ℝ) ≤ 3 / 4 := by
  norm_num [policyRows, policyTable]

private theorem policyRows_all_bounds_3 :
    ∀ row ∈ policyRows (3 : PolicyIndex), ∀ mass ∈ row,
      0 < mass ∧ (mass : ℝ) ≤ 3 / 4 := by
  norm_num [policyRows, policyTable]

private theorem policyRows_all_bounds_4 :
    ∀ row ∈ policyRows (4 : PolicyIndex), ∀ mass ∈ row,
      0 < mass ∧ (mass : ℝ) ≤ 3 / 4 := by
  norm_num [policyRows, policyTable]

private theorem policyRows_all_bounds (policy : PolicyIndex) :
    ∀ row ∈ policyRows policy, ∀ mass ∈ row,
      0 < mass ∧ (mass : ℝ) ≤ 3 / 4 := by
  fin_cases policy
  · exact policyRows_all_bounds_0
  · exact policyRows_all_bounds_1
  · exact policyRows_all_bounds_2
  · exact policyRows_all_bounds_3
  · exact policyRows_all_bounds_4

/-- Every generated policy entry is strictly positive. -/
theorem policyTableMass_pos
    (policy : PolicyIndex) (state : PhysicalState) (action : Action) :
    0 < policyTableMass policy state action := by
  exact (policyRows_all_bounds policy
    (policyRow policy state) (List.get_mem _ _)
    (policyTableMass policy state action) (List.get_mem _ _)).1

private theorem policyTableMass_le_three_quarters
    (policy : PolicyIndex) (state : PhysicalState) (action : Action) :
    (policyTableMass policy state action : ℝ) ≤ 3 / 4 := by
  exact (policyRows_all_bounds policy
    (policyRow policy state) (List.get_mem _ _)
    (policyTableMass policy state action) (List.get_mem _ _)).2

private theorem policyTableMass_sum_one_0 (state : PhysicalState) :
    ∑ action : Action,
      (policyTableMass (0 : PolicyIndex) state action : ℝ) = 1 := by
  fin_cases state <;>
    norm_num [policyTableMass, policyRow, policyRows, policyTable,
      Fin.sum_univ_succ]

private theorem policyTableMass_sum_one_1 (state : PhysicalState) :
    ∑ action : Action,
      (policyTableMass (1 : PolicyIndex) state action : ℝ) = 1 := by
  fin_cases state <;>
    norm_num [policyTableMass, policyRow, policyRows, policyTable,
      Fin.sum_univ_succ]

private theorem policyTableMass_sum_one_2 (state : PhysicalState) :
    ∑ action : Action,
      (policyTableMass (2 : PolicyIndex) state action : ℝ) = 1 := by
  fin_cases state <;>
    norm_num [policyTableMass, policyRow, policyRows, policyTable,
      Fin.sum_univ_succ]

private theorem policyTableMass_sum_one_3 (state : PhysicalState) :
    ∑ action : Action,
      (policyTableMass (3 : PolicyIndex) state action : ℝ) = 1 := by
  fin_cases state <;>
    norm_num [policyTableMass, policyRow, policyRows, policyTable,
      Fin.sum_univ_succ]

private theorem policyTableMass_sum_one_4 (state : PhysicalState) :
    ∑ action : Action,
      (policyTableMass (4 : PolicyIndex) state action : ℝ) = 1 := by
  fin_cases state <;>
    norm_num [policyTableMass, policyRow, policyRows, policyTable,
      Fin.sum_univ_succ]

/-- Every generated policy row has exact real mass one. -/
theorem policyTableMass_sum_one
    (policy : PolicyIndex) (state : PhysicalState) :
    ∑ action : Action, (policyTableMass policy state action : ℝ) = 1 := by
  fin_cases policy
  · exact policyTableMass_sum_one_0 state
  · exact policyTableMass_sum_one_1 state
  · exact policyTableMass_sum_one_2 state
  · exact policyTableMass_sum_one_3 state
  · exact policyTableMass_sum_one_4 state

/-- Typed environment kernel read directly from one generated candidate table. -/
noncomputable def candidateEnvironment
    (candidate : CandidateIndex) :
    PhysicalState → Action → PMF PhysicalState :=
  fun state action ↦
    PMF.ofFintype
      (fun nextState ↦ ENNReal.ofReal
        (candidateKernelTableMass candidate
          (stateActionRowEquiv (state, action)) nextState : ℝ))
      (by
        rw [← ENNReal.ofReal_one,
          ← candidateKernelTableMass_sum_one candidate
            (stateActionRowEquiv (state, action))]
        exact Eq.symm (ENNReal.ofReal_sum_of_nonneg
          (s := Finset.univ)
          (f := fun nextState ↦
            (candidateKernelTableMass candidate
              (stateActionRowEquiv (state, action)) nextState : ℝ))
          (fun nextState _hnextState ↦ by
            exact_mod_cast le_of_lt
              (candidateKernelTableMass_pos candidate
                (stateActionRowEquiv (state, action)) nextState))))

/-- Typed state-based policy read directly from one generated policy table. -/
noncomputable def queuePolicy
    (policy : PolicyIndex) : PhysicalState → PMF Action :=
  fun state ↦
    PMF.ofFintype
      (fun action ↦ ENNReal.ofReal
        (policyTableMass policy state action : ℝ))
      (by
        rw [← ENNReal.ofReal_one,
          ← policyTableMass_sum_one policy state]
        exact Eq.symm (ENNReal.ofReal_sum_of_nonneg
          (s := Finset.univ)
          (f := fun action ↦ (policyTableMass policy state action : ℝ))
          (fun action _haction ↦ by
            exact_mod_cast le_of_lt
              (policyTableMass_pos policy state action))))

/-- The generated uniform behavior policy as a typed Markov behavior policy. -/
noncomputable def behaviorPolicy :
    MarkovBehaviorPolicy PhysicalState Action :=
  queuePolicy behaviorPolicyIndex

/-- A typed target policy.  This function type is definitionally the
`MarkovTargetPolicy` interface once that OPE module is imported. -/
noncomputable def targetPolicy
    (target : TargetPolicyIndex) : PhysicalState → PMF Action :=
  queuePolicy (targetPolicyTableIndex target)

@[simp]
theorem candidateEnvironment_apply_toReal
    (candidate : CandidateIndex) (state : PhysicalState)
    (action : Action) (nextState : PhysicalState) :
    (candidateEnvironment candidate state action nextState).toReal =
      (candidateKernelTableMass candidate
        (stateActionRowEquiv (state, action)) nextState : ℝ) := by
  change (ENNReal.ofReal
      (candidateKernelTableMass candidate
        (stateActionRowEquiv (state, action)) nextState : ℝ)).toReal = _
  exact ENNReal.toReal_ofReal (by
    exact_mod_cast le_of_lt
      (candidateKernelTableMass_pos candidate
        (stateActionRowEquiv (state, action)) nextState))

@[simp]
theorem queuePolicy_apply_toReal
    (policy : PolicyIndex) (state : PhysicalState) (action : Action) :
    (queuePolicy policy state action).toReal =
      (policyTableMass policy state action : ℝ) := by
  change (ENNReal.ofReal
      (policyTableMass policy state action : ℝ)).toReal = _
  exact ENNReal.toReal_ofReal (by
    exact_mod_cast le_of_lt (policyTableMass_pos policy state action))

@[simp]
theorem behaviorPolicy_apply_toReal
    (state : PhysicalState) (action : Action) :
    (behaviorPolicy state action).toReal = 1 / 2 := by
  change (queuePolicy behaviorPolicyIndex state action).toReal = 1 / 2
  rw [queuePolicy_apply_toReal]
  fin_cases state <;> fin_cases action <;>
    norm_num [behaviorPolicyIndex, policyTableMass, policyRow, policyRows,
      policyTable]

@[simp]
theorem targetPolicy_apply_toReal
    (target : TargetPolicyIndex) (state : PhysicalState) (action : Action) :
    (targetPolicy target state action).toReal =
      (policyTableMass (targetPolicyTableIndex target) state action : ℝ) := by
  simp only [targetPolicy, queuePolicy_apply_toReal]

/-- Every generated target-policy probability is at most `3/2` times the
uniform behavior probability. -/
theorem targetPolicy_probability_le_three_halves_behavior
    (target : TargetPolicyIndex) (state : PhysicalState) (action : Action) :
    (targetPolicy target state action).toReal ≤
      (3 / 2 : ℝ) * (behaviorPolicy state action).toReal := by
  rw [targetPolicy_apply_toReal, behaviorPolicy_apply_toReal]
  have h := policyTableMass_le_three_quarters
    (targetPolicyTableIndex target) state action
  norm_num at h ⊢
  exact h

/-- A typed candidate transition reads the generated row selected by the
current state and next action. -/
@[simp]
theorem candidateEnvironment_transition_apply_toReal
    (candidate : CandidateIndex)
    (previousAction action : Action)
    (state nextState : PhysicalState) :
    (candidateEnvironment candidate state action nextState).toReal =
      (candidateKernelTableMass candidate
        (transitionRow (previousAction, state) (action, nextState))
        nextState : ℝ) := by
  rw [candidateEnvironment_apply_toReal, transitionRow_pair]

/-- Exact generated-table mass of one action-major augmented behavior
transition. -/
@[simp]
theorem augmentedCandidateBehaviorKernel_apply_toReal
    (candidate : CandidateIndex)
    (previousAction action : Action)
    (state nextState : PhysicalState) :
    (augmentedBehaviorKernel
        (candidateEnvironment candidate) behaviorPolicy
        (previousAction, state) (action, nextState)).toReal =
      (1 / 2 : ℝ) *
        (candidateKernelTableMass candidate
          (transitionRow (previousAction, state) (action, nextState))
          nextState : ℝ) := by
  rw [augmentedBehaviorKernel_apply, ENNReal.toReal_mul,
    behaviorPolicy_apply_toReal, candidateEnvironment_transition_apply_toReal]

/-- Under uniform behavior, augmented-row TV is exactly the average of the
two action-conditioned physical row TVs. -/
theorem augmentedBehavior_candidateEnvironment_rowTV_eq_sum
    (P : PhysicalState → Action → PMF PhysicalState)
    (candidate : CandidateIndex) (current : Observation) :
    finitePMFTotalVariation
        (augmentedBehaviorKernel P behaviorPolicy current)
        (augmentedBehaviorKernel
          (candidateEnvironment candidate) behaviorPolicy current) =
      ∑ action : Action, (1 / 2 : ℝ) *
        finitePMFTotalVariation
          (P current.2 action)
          (candidateEnvironment candidate current.2 action) := by
  rw [finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum]
  simp only [behaviorPolicy_apply_toReal]

/-- Under the uniform behavior policy, an augmented-row TV bound `eta`
controls any one physical environment row at the exact inverse-probability
price `eta / (1/2) = 2 * eta`. -/
theorem environmentRowTV_candidate_le_two_mul_augmentedRowTV
    (P : PhysicalState → Action → PMF PhysicalState)
    (candidate : CandidateIndex)
    (previousAction action : Action) (state : PhysicalState)
    {eta : ℝ}
    (haugmented :
      finitePMFTotalVariation
          (augmentedBehaviorKernel P behaviorPolicy
            (previousAction, state))
          (augmentedBehaviorKernel
            (candidateEnvironment candidate) behaviorPolicy
            (previousAction, state)) ≤ eta) :
    finitePMFTotalVariation
        (P state action)
        (candidateEnvironment candidate state action) ≤
      2 * eta := by
  have h :=
    environmentKernel_rowTV_le_augmentedKernel_rowTV_div_actionProbability
      P (candidateEnvironment candidate) behaviorPolicy
      previousAction action state (eta := eta)
      (by norm_num [behaviorPolicy_apply_toReal])
      haugmented
  calc
    finitePMFTotalVariation
        (P state action)
        (candidateEnvironment candidate state action) ≤
      eta / (1 / 2 : ℝ) := by
        simpa only [behaviorPolicy_apply_toReal] using h
    _ = 2 * eta := by ring

end

end FormalSLT.Applications.ControlledQueue
