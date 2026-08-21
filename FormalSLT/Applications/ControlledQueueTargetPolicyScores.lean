/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueTypedModel
import FormalSLT.StochasticDynamics.StationaryTargetPolicyRobustCandidate

/-!
# Controlled-queue target-policy scores

This module reads the generated fixed-predictor, control-cost, and
overload-outcome tables through proof-carrying `List.get` operations.  It
reconstructs Brier loss from the forecast and binary outcome, then turns both
loss families into the bounded transition-score interface used by the
stationary target-policy OPE theorems.

The three fixed predictors are stationary scores.  The two causal Beta
predictors in the frozen trace are deliberately excluded: they depend on past
outcomes and belong to the dynamic comparator interface unless learner memory
is added to the state.

The generated behavior policy has mass `1/2` on both actions, while every
target-policy mass is at most `3/4`.  Consequently all four target policies
satisfy overlap and the exact declared ratio cap `3/2`.

The unit-range score certificate also gives the universal centered row-risk
oscillation envelope `D = 1` for every candidate, target policy, predictor, and
reference PMF. This module does not construct invariant laws, prove candidate
contraction, import the trace, or instantiate a statistical event.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

noncomputable section

/-- Indices of the three generated fixed overload predictors. -/
abbrev FixedPredictorIndex := Fin 3

private theorem fixedPredictorTable_length : fixedPredictorTable.length = 3 := rfl

private abbrev fixedPredictorRow (predictor : FixedPredictorIndex) : List ℚ :=
  fixedPredictorTable.get
    (Fin.cast fixedPredictorTable_length.symm predictor)

private theorem fixedPredictorRow_length (predictor : FixedPredictorIndex) :
    (fixedPredictorRow predictor).length = 48 := by
  fin_cases predictor <;> rfl

/-- Exact generated forecast probability in one state-action row. -/
def fixedPredictorTableValue
    (predictor : FixedPredictorIndex) (row : Fin 48) : ℚ :=
  (fixedPredictorRow predictor).get
    (Fin.cast (fixedPredictorRow_length predictor).symm row)

/-- Exact generated forecast probability indexed directly by physical state
and action in state-major/action-minor order. -/
def fixedPredictorTableValueStateAction
    (predictor : FixedPredictorIndex) (state : PhysicalState)
    (action : Action) : ℚ :=
  (fixedPredictorRow predictor).get
    (Fin.cast (fixedPredictorRow_length predictor).symm
      ⟨2 * state.val + action.val, by omega⟩)

@[simp]
theorem fixedPredictorTableValue_stateActionRowEquiv
    (predictor : FixedPredictorIndex) (state : PhysicalState)
    (action : Action) :
    fixedPredictorTableValue predictor
        (stateActionRowEquiv (state, action)) =
      fixedPredictorTableValueStateAction predictor state action := by
  unfold fixedPredictorTableValue fixedPredictorTableValueStateAction
  congr 1
  apply Fin.ext
  exact stateActionRowEquiv_apply_val state action

private theorem controlCostTable_length : controlCostTable.length = 2 := rfl

private abbrev controlCostRow (action : Action) : List ℚ :=
  controlCostTable.get (Fin.cast controlCostTable_length.symm action)

private theorem controlCostRow_length (action : Action) :
    (controlCostRow action).length = 24 := by
  fin_cases action <;> rfl

/-- Exact generated control cost for an action and next state. -/
def controlCostTableValue (action : Action) (nextState : PhysicalState) : ℚ :=
  (controlCostRow action).get
    (Fin.cast (controlCostRow_length action).symm nextState)

private theorem overloadOutcomeTable_length :
    overloadOutcomeTable.length = 24 := rfl

/-- Exact generated binary overload outcome for a next state. -/
def overloadOutcomeTableValue (nextState : PhysicalState) : ℚ :=
  overloadOutcomeTable.get
    (Fin.cast overloadOutcomeTable_length.symm nextState)

/-- Real-valued forecast probability selected by the state-action row map. -/
def fixedPredictorProbability
    (predictor : FixedPredictorIndex) (state : PhysicalState)
    (action : Action) : ℝ :=
  fixedPredictorTableValue predictor (stateActionRowEquiv (state, action))

/-- Real-valued binary overload outcome. -/
def overloadOutcome (nextState : PhysicalState) : ℝ :=
  overloadOutcomeTableValue nextState

/-- Fixed-predictor Brier loss, reconstructed from the generated forecast and
binary-outcome tables, as a target-policy transition score. -/
def fixedBrierScore
    (predictor : FixedPredictorIndex) :
    TargetPolicyTransitionScore PhysicalState Action :=
  fun state action nextState ↦
    (fixedPredictorProbability predictor state action -
      overloadOutcome nextState) ^ 2

/-- Generated normalized control cost as a target-policy transition score. -/
def controlCostScore : TargetPolicyTransitionScore PhysicalState Action :=
  fun _state action nextState ↦ controlCostTableValue action nextState

private theorem fixedPredictorRow_all_bounds_0 :
    ∀ value ∈ fixedPredictorRow (0 : FixedPredictorIndex),
      (value : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [fixedPredictorRow, fixedPredictorTable]

private theorem fixedPredictorRow_all_bounds_1 :
    ∀ value ∈ fixedPredictorRow (1 : FixedPredictorIndex),
      (value : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [fixedPredictorRow, fixedPredictorTable]

private theorem fixedPredictorRow_all_bounds_2 :
    ∀ value ∈ fixedPredictorRow (2 : FixedPredictorIndex),
      (value : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [fixedPredictorRow, fixedPredictorTable]

private theorem fixedPredictorRow_all_bounds
    (predictor : FixedPredictorIndex) :
    ∀ value ∈ fixedPredictorRow predictor,
      (value : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases predictor
  · exact fixedPredictorRow_all_bounds_0
  · exact fixedPredictorRow_all_bounds_1
  · exact fixedPredictorRow_all_bounds_2

/-- Every generated fixed forecast probability lies in the unit interval. -/
theorem fixedPredictorProbability_mem_Icc
    (predictor : FixedPredictorIndex) (state : PhysicalState)
    (action : Action) :
    fixedPredictorProbability predictor state action ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fixedPredictorProbability,
    fixedPredictorTableValue_stateActionRowEquiv]
  exact fixedPredictorRow_all_bounds predictor
    (fixedPredictorTableValueStateAction predictor state action)
    (List.get_mem _ _)

private theorem overloadOutcomeTable_all_bounds :
    ∀ value ∈ overloadOutcomeTable,
      (value : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [overloadOutcomeTable]

/-- Every generated overload outcome is binary, hence in the unit interval. -/
theorem overloadOutcome_mem_Icc (nextState : PhysicalState) :
    overloadOutcome nextState ∈ Set.Icc (0 : ℝ) 1 := by
  exact overloadOutcomeTable_all_bounds
    (overloadOutcomeTableValue nextState) (List.get_mem _ _)

private theorem controlCostRows_all_bounds :
    ∀ row ∈ controlCostTable,
      ∀ value ∈ row, (value : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [controlCostTable]

/-- The fixed Brier score is exactly squared forecast error against the
generated binary overload outcome. -/
@[simp]
theorem fixedBrierScore_eq_squaredError
    (predictor : FixedPredictorIndex) (state : PhysicalState)
    (action : Action) (nextState : PhysicalState) :
    fixedBrierScore predictor state action nextState =
      (fixedPredictorProbability predictor state action -
        overloadOutcome nextState) ^ 2 := rfl

/-- Every generated fixed-predictor Brier score lies in the unit interval. -/
theorem fixedBrierScore_mem_Icc
    (predictor : FixedPredictorIndex) (state : PhysicalState)
    (action : Action) (nextState : PhysicalState) :
    fixedBrierScore predictor state action nextState ∈ Set.Icc (0 : ℝ) 1 := by
  let p := fixedPredictorProbability predictor state action
  let y := overloadOutcome nextState
  have hp := fixedPredictorProbability_mem_Icc predictor state action
  have hy := overloadOutcome_mem_Icc nextState
  have hlo : -1 ≤ p - y := by
    dsimp [p, y]
    linarith [hp.1, hy.2]
  have hhi : p - y ≤ 1 := by
    dsimp [p, y]
    linarith [hp.2, hy.1]
  have hplus : 0 ≤ 1 + (p - y) := by linarith
  have hproduct : 0 ≤ (1 - (p - y)) * (1 + (p - y)) :=
    mul_nonneg (sub_nonneg.mpr hhi) hplus
  rw [fixedBrierScore_eq_squaredError]
  constructor
  · positivity
  · dsimp [p, y] at hproduct
    nlinarith

/-- Every generated fixed Brier score has centered target-policy row-risk
oscillation at most one, uniformly over candidates, target policies, and
reference PMFs. -/
theorem fixedBrierScore_centeredTargetPolicyRowRisk_finiteOscillation_le_one
    (candidate : CandidateIndex) (target : TargetPolicyIndex)
    (reference : PMF PhysicalState) (predictor : FixedPredictorIndex) :
    finiteOscillation
        (centeredMarkovRowRisk
          (targetPolicyKernel
            (candidateEnvironment candidate) (targetPolicy target))
          reference
          (targetPolicyRowScore
            (candidateEnvironment candidate) (targetPolicy target)
            (fixedBrierScore predictor))) ≤ 1 := by
  exact centered_targetPolicyRowScore_finiteOscillation_le_one
    (candidateEnvironment candidate) (targetPolicy target) reference
    (fixedBrierScore_mem_Icc predictor)

/-- Every generated normalized control-cost score lies in the unit interval. -/
theorem controlCostScore_mem_Icc
    (state : PhysicalState) (action : Action) (nextState : PhysicalState) :
    controlCostScore state action nextState ∈ Set.Icc (0 : ℝ) 1 := by
  exact controlCostRows_all_bounds
    (controlCostRow action) (List.get_mem _ _)
    (controlCostTableValue action nextState) (List.get_mem _ _)

/-- Uniform behavior assigns positive mass to every action, so every generated
target policy satisfies pointwise overlap. -/
theorem behavior_targetPolicy_overlap (target : TargetPolicyIndex) :
    ControlledPolicyOverlap
      (markovBehaviorPolicyAsHistory behaviorPolicy)
      (markovTargetPolicyAsHistory (targetPolicy target)) := by
  intro n u action hzero
  have hfalse : (1 / 2 : ℝ) = 0 := by
    simpa only [markovBehaviorPolicyAsHistory, behaviorPolicy_apply_toReal]
      using hzero
  norm_num at hfalse

/-- Every generated target policy satisfies the exact target-to-behavior
ratio cap `3/2`. -/
theorem behavior_targetPolicy_ratioBound_three_halves
    (target : TargetPolicyIndex) :
    ControlledPolicyRatioBound
      (markovBehaviorPolicyAsHistory behaviorPolicy)
      (markovTargetPolicyAsHistory (targetPolicy target)) (3 / 2 : ℝ) := by
  intro n u action
  simpa only [markovBehaviorPolicyAsHistory, markovTargetPolicyAsHistory]
    using targetPolicy_probability_le_three_halves_behavior target
      (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 action

end

end FormalSLT.Applications.ControlledQueue
