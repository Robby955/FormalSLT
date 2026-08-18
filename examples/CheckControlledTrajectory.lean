/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledTrajectory

/-!
# Controlled-trajectory semantic receipt

The Boolean receipt uses a behavior policy which reads the action at time zero
even when the current decision--outcome coordinate is identical.  At a
displayed prefix, the behavior probabilities are `3/4` and `1/4`, while the
first target policy is uniform, so the two checked importance ratios are
exactly `2/3` and `2`.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckControlledTrajectory

open FormalSLT.StochasticDynamics

noncomputable section

/-- Boolean PMF assigning mass `3/4` to `favored` and `1/4` to the other
outcome. -/
def biasedBoolPMF (favored : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun b ↦ if b = favored
      then ((3 / 4 : NNReal) : ENNReal)
      else ((1 / 4 : NNReal) : ENNReal))
    (by
      have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hsum : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      cases favored <;>
        simpa [Fintype.sum_bool, add_comm] using hsum)

/-- Uniform Boolean PMF. -/
def fairBoolPMF : PMF Bool :=
  PMF.ofFintype
    (fun _ ↦ ((1 / 2 : NNReal) : ENNReal))
    (by
      have hsumNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
      have hsum : ((1 / 2 : NNReal) : ENNReal) +
          ((1 / 2 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      simpa [Fintype.sum_bool, two_mul] using hsum)

/-- A nondegenerate environment row which depends on both the current state
and current action. -/
def boolControlledEnvironment (s a : Bool) : PMF Bool :=
  biasedBoolPMF (s == a)

/-- The initial action is a genuine historical feature at every later time. -/
def initialAction (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool) : Bool :=
  (u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1

/-- History-dependent behavior: after the next state is revealed, favor the
action used at time zero. -/
def historyDependentBehavior : BehaviorPolicy Bool Bool :=
  fun n u ↦ biasedBoolPMF (initialAction n u)

/-- A two-policy catalog.  The `false` atom is uniform; the `true` atom favors
`true` with probability `3/4`. -/
def boolTargetPolicyCatalog (i : Bool) : TargetPolicy Bool Bool :=
  fun _n _u ↦ if i then biasedBoolPMF true else fairBoolPMF

/-- The uniform target needs cap `2`; the biased target needs cap `3` across
both possible history-dependent behavior rows. -/
def boolImportanceCap (i : Bool) : ℝ := if i then 3 else 2

/-- Two bounded transition scores depending on the next state and action. -/
def boolControlledScore (i : Bool) : ControlledTransitionScore Bool Bool :=
  fun _n _u a y ↦ if (y == a) = i then 1 else 0

theorem boolControlledScore_mem_Icc :
    ∀ i n u a y, boolControlledScore i n u a y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u a y
  simp only [boolControlledScore]
  split_ifs <;> norm_num

theorem historyDependentBehavior_overlap (i : Bool) :
    ControlledPolicyOverlap historyDependentBehavior
      (boolTargetPolicyCatalog i) := by
  intro n u a hzero
  simp only [historyDependentBehavior, biasedBoolPMF,
    PMF.ofFintype_apply] at hzero
  split_ifs at hzero <;> norm_num at hzero

theorem historyDependentBehavior_ratioBound (i : Bool) :
    ControlledPolicyRatioBound historyDependentBehavior
      (boolTargetPolicyCatalog i) (boolImportanceCap i) := by
  intro n u a
  fin_cases i <;> fin_cases a <;>
    simp only [boolTargetPolicyCatalog, boolImportanceCap, Bool.false_eq_true,
      fairBoolPMF, historyDependentBehavior, biasedBoolPMF,
      PMF.ofFintype_apply] <;>
    split_ifs <;> norm_num

theorem boolImportanceCap_pos (i : Bool) : 0 < boolImportanceCap i := by
  fin_cases i <;> norm_num [boolImportanceCap]

/-- Two paths with the same current decision--outcome coordinate at time two, but
different initial actions. -/
def initialTrueActionPath (n : ℕ) : ControlledObservation Bool Bool :=
  if n = 0 then (true, false) else (false, false)

def allFalseControlledPath (_n : ℕ) : ControlledObservation Bool Bool :=
  (false, false)

theorem behaviorWitness_same_current :
    initialTrueActionPath 2 = allFalseControlledPath 2 := by
  norm_num [initialTrueActionPath, allFalseControlledPath]

theorem behaviorWitness_different_initial_action :
    (initialTrueActionPath 0).1 ≠ (allFalseControlledPath 0).1 := by
  norm_num [initialTrueActionPath, allFalseControlledPath]

/-- Despite the same current coordinate, behavior assigns different next-action
mass because it reads the earlier action. -/
theorem historyDependentBehavior_witness :
    historyDependentBehavior 2
        (Preorder.frestrictLe 2 initialTrueActionPath) true = 3 / 4 ∧
      historyDependentBehavior 2
        (Preorder.frestrictLe 2 allFalseControlledPath) true = 1 / 4 := by
  constructor <;>
    norm_num [historyDependentBehavior, biasedBoolPMF, initialAction,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply,
      initialTrueActionPath, allFalseControlledPath]

/-- At the first witness prefix, the uniform target produces both the small
and large importance weights: `2/3` on the favored action and `2` on the
unfavored action. -/
theorem both_importance_weights_witness :
    controlledImportanceRatio historyDependentBehavior
        (boolTargetPolicyCatalog false) 2
        (Preorder.frestrictLe 2 initialTrueActionPath) true = 2 / 3 ∧
      controlledImportanceRatio historyDependentBehavior
        (boolTargetPolicyCatalog false) 2
        (Preorder.frestrictLe 2 initialTrueActionPath) false = 2 := by
  constructor <;>
    norm_num [controlledImportanceRatio, historyDependentBehavior,
      boolTargetPolicyCatalog, fairBoolPMF, biasedBoolPMF, initialAction,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply,
      initialTrueActionPath]

/-- The complete finite catalog discharges the exact interfaces consumed by
the predictable-mean empirical-Bernstein PAC--Bayes theorem. -/
theorem boolControlledCatalog_interfaces :
    (∀ i, FormalSLT.AnytimeValid.IncrementAdapted
        (Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Bool Bool))
        (controlledObservedImportanceScore historyDependentBehavior
          (boolTargetPolicyCatalog i) (boolControlledScore i)
          (boolImportanceCap i))) ∧
      (∀ i, StronglyAdapted
        (Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Bool Bool))
        (controlledTargetConditionalMean boolControlledEnvironment
          (boolTargetPolicyCatalog i) (boolControlledScore i)
          (boolImportanceCap i))) ∧
      (∀ i n x,
        0 ≤ controlledObservedImportanceScore historyDependentBehavior
            (boolTargetPolicyCatalog i) (boolControlledScore i)
            (boolImportanceCap i) n x ∧
          controlledObservedImportanceScore historyDependentBehavior
              (boolTargetPolicyCatalog i) (boolControlledScore i)
              (boolImportanceCap i) n x ≤ 1) ∧
      (∀ i n,
        (controlledTrajectoryMeasure boolControlledEnvironment
            historyDependentBehavior (false, false))[
          controlledObservedImportanceScore historyDependentBehavior
            (boolTargetPolicyCatalog i) (boolControlledScore i)
            (boolImportanceCap i) n |
          Filtration.piLE
            (X := fun _ : ℕ ↦ ControlledObservation Bool Bool) n] =ᵐ[
          controlledTrajectoryMeasure boolControlledEnvironment
            historyDependentBehavior (false, false)]
          controlledTargetConditionalMean boolControlledEnvironment
            (boolTargetPolicyCatalog i) (boolControlledScore i)
            (boolImportanceCap i) n) := by
  exact controlledImportanceCatalog_predictableMean_interfaces
    boolControlledEnvironment historyDependentBehavior (false, false)
    boolTargetPolicyCatalog boolControlledScore boolImportanceCap
    historyDependentBehavior_overlap historyDependentBehavior_ratioBound
    boolImportanceCap_pos boolControlledScore_mem_Icc

#check controlledContinuationPMF
#check controlledTrajectoryMeasure
#check controlledObservedImportanceScore_condExp
#check controlledImportanceCatalog_predictableMean_interfaces
#check both_importance_weights_witness

#print axioms controlledObservedImportanceScore_condExp
#print axioms controlledImportanceCatalog_predictableMean_interfaces
#print axioms boolControlledCatalog_interfaces

end

end FormalSLT.Examples.CheckControlledTrajectory
