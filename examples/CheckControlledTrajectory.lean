/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledTrajectory

/-!
# Controlled-trajectory semantic receipt

The Boolean receipt uses a behavior policy which reads the interior action at
coordinate one even when the deterministic initial and current coordinates
are identical.  At a
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

/-- Both atoms have positive mass in every biased Boolean row. -/
theorem biasedBoolPMF_pos (favored b : Bool) :
    0 < biasedBoolPMF favored b := by
  simp only [biasedBoolPMF, PMF.ofFintype_apply]
  split_ifs <;> norm_num

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

/-- Read the action at coordinate one when it exists, with coordinate zero as
the total fallback.  At time two this is a genuinely interior feature. -/
def interiorAction (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool) : Bool :=
  if h : 1 ≤ n then
    (u ⟨1, Finset.mem_Iic.mpr h⟩).1
  else
    (u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1

/-- History-dependent behavior: favor the recorded interior action. -/
def historyDependentBehavior : BehaviorPolicy Bool Bool :=
  fun n u ↦ biasedBoolPMF (interiorAction n u)

/-- Every behavior row gives positive mass to every action. -/
theorem historyDependentBehavior_pos (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool) (a : Bool) :
    0 < historyDependentBehavior n u a :=
  biasedBoolPMF_pos _ _

/-- Every environment row gives positive mass to every outcome. -/
theorem boolControlledEnvironment_pos (s a y : Bool) :
    0 < boolControlledEnvironment s a y :=
  biasedBoolPMF_pos _ _

/-- Consequently every action--outcome continuation atom has positive mass
from every completed prefix. -/
theorem controlledContinuationPMF_pos (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool)
    (next : ControlledObservation Bool Bool) :
    0 < controlledContinuationPMF boolControlledEnvironment
      historyDependentBehavior n u next := by
  rw [show next = (next.1, next.2) by exact Prod.eta next,
    controlledContinuationPMF_apply]
  exact ENNReal.mul_pos_iff.2
    ⟨historyDependentBehavior_pos n u next.1,
      boolControlledEnvironment_pos _ _ _⟩

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

/-- Two paths with the same deterministic initial and current coordinates at
time two, but different actions at the interior coordinate one. -/
def interiorTrueActionPath (n : ℕ) : ControlledObservation Bool Bool :=
  if n = 1 then (true, false) else (false, false)

def allFalseControlledPath (_n : ℕ) : ControlledObservation Bool Bool :=
  (false, false)

theorem behaviorWitness_same_initial_and_current :
    interiorTrueActionPath 0 = (false, false) ∧
      allFalseControlledPath 0 = (false, false) ∧
      interiorTrueActionPath 2 = allFalseControlledPath 2 := by
  norm_num [interiorTrueActionPath, allFalseControlledPath]

theorem behaviorWitness_different_interior_action :
    (interiorTrueActionPath 1).1 ≠ (allFalseControlledPath 1).1 := by
  norm_num [interiorTrueActionPath, allFalseControlledPath]

/-- Despite the same current coordinate, behavior assigns different next-action
mass because it reads the earlier action. -/
theorem historyDependentBehavior_witness :
    historyDependentBehavior 2
        (Preorder.frestrictLe 2 interiorTrueActionPath) true = 3 / 4 ∧
      historyDependentBehavior 2
        (Preorder.frestrictLe 2 allFalseControlledPath) true = 1 / 4 := by
  constructor <;>
    norm_num [historyDependentBehavior, biasedBoolPMF, interiorAction,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply,
      interiorTrueActionPath, allFalseControlledPath]

/-- At the first witness prefix, the uniform target produces both the small
and large importance weights: `2/3` on the favored action and `2` on the
unfavored action. -/
theorem both_importance_weights_witness :
    controlledImportanceRatio historyDependentBehavior
        (boolTargetPolicyCatalog false) 2
        (Preorder.frestrictLe 2 interiorTrueActionPath) true = 2 / 3 ∧
      controlledImportanceRatio historyDependentBehavior
        (boolTargetPolicyCatalog false) 2
        (Preorder.frestrictLe 2 interiorTrueActionPath) false = 2 := by
  constructor <;>
    norm_num [controlledImportanceRatio, historyDependentBehavior,
      boolTargetPolicyCatalog, fairBoolPMF, biasedBoolPMF, interiorAction,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply,
      interiorTrueActionPath]

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
#check controlledContinuationPMF_pos
#check both_importance_weights_witness

#print axioms controlledObservedImportanceScore_condExp
#print axioms controlledImportanceCatalog_predictableMean_interfaces
#print axioms controlledContinuationPMF_pos
#print axioms boolControlledCatalog_interfaces

end

end FormalSLT.Examples.CheckControlledTrajectory
