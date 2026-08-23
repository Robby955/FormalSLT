/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledMarkovization
import FormalSLT.StochasticDynamics.StationaryPoissonDobrushin

/-!
# Action-conditioned total variation for controlled kernels

When two controlled environments use the same state-based behavior policy,
the total variation between their augmented action--state transition rows is
the behavior-weighted sum of their action-conditioned environment-row total
variations.  Thus an action whose behavior probability is positive can be
identified at the unavoidable price `1 / beta(state, action)`.  A uniform
positive behavior floor replaces this denominator by one declared constant.

The augmented observation remains action-major:
`ControlledObservation Z A = A × Z`.  In a current pair
`(previousAction, state)`, only the second coordinate selects the environment
and behavior rows.  The first coordinate records the previous action.

There is no extra factor two: `finitePMFTotalVariation` already uses the
probabilists' `L¹ / 2` convention.  If an action has zero behavior mass, its
environment row is not identifiable from the augmented kernel, and no such
division theorem is stated.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A : Type*}
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Under a shared behavior policy, augmented-row total variation is exactly
the behavior-weighted sum of the action-conditioned environment-row total
variations. -/
theorem finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum
    (P Q : Z → A → PMF Z) (beta : MarkovBehaviorPolicy Z A)
    (current : ControlledObservation Z A) :
    finitePMFTotalVariation
        (augmentedBehaviorKernel P beta current)
        (augmentedBehaviorKernel Q beta current) =
      ∑ action : A, (beta current.2 action).toReal *
        finitePMFTotalVariation
          (P current.2 action) (Q current.2 action) := by
  classical
  unfold finitePMFTotalVariation
  rw [Fintype.sum_prod_type]
  simp_rw [augmentedBehaviorKernel_apply, ENNReal.toReal_mul,
    ← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    (1 / 2 : ℝ) * ∑ action : A, ∑ nextState : Z,
        (beta current.2 action).toReal *
          |(P current.2 action nextState).toReal -
            (Q current.2 action nextState).toReal| =
      ∑ action : A, (1 / 2 : ℝ) *
        (∑ nextState : Z, (beta current.2 action).toReal *
          |(P current.2 action nextState).toReal -
            (Q current.2 action nextState).toReal|) := by
      rw [Finset.mul_sum]
    _ = ∑ action : A, (beta current.2 action).toReal *
        ((1 / 2 : ℝ) * ∑ nextState : Z,
          |(P current.2 action nextState).toReal -
            (Q current.2 action nextState).toReal|) := by
      apply Finset.sum_congr rfl
      intro action _ha
      rw [← Finset.mul_sum]
      ring

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- One behavior-weighted action row is bounded by the augmented-row total
variation. -/
theorem actionProbability_mul_environmentKernel_rowTV_le_augmentedKernel_rowTV
    (P Q : Z → A → PMF Z) (beta : MarkovBehaviorPolicy Z A)
    (current : ControlledObservation Z A) (action : A) :
    (beta current.2 action).toReal *
        finitePMFTotalVariation
          (P current.2 action) (Q current.2 action) ≤
      finitePMFTotalVariation
        (augmentedBehaviorKernel P beta current)
        (augmentedBehaviorKernel Q beta current) := by
  rw [finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum]
  exact Finset.single_le_sum
    (fun candidate _hcandidate ↦ mul_nonneg ENNReal.toReal_nonneg
      (finitePMFTotalVariation_nonneg
        (P current.2 candidate) (Q current.2 candidate)))
    (Finset.mem_univ action)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A positive behavior probability turns augmented-row TV control into
action-conditioned environment-row TV control.  The first coordinate of the
current augmented observation is the previous action. -/
theorem environmentKernel_rowTV_le_augmentedKernel_rowTV_div_actionProbability
    (P Q : Z → A → PMF Z) (beta : MarkovBehaviorPolicy Z A)
    (previousAction action : A) (state : Z) {eta : ℝ}
    (hbeta : 0 < (beta state action).toReal)
    (haugmented :
      finitePMFTotalVariation
          (augmentedBehaviorKernel P beta (previousAction, state))
          (augmentedBehaviorKernel Q beta (previousAction, state)) ≤ eta) :
    finitePMFTotalVariation (P state action) (Q state action) ≤
      eta / (beta state action).toReal := by
  rw [le_div_iff₀ hbeta]
  calc
    finitePMFTotalVariation (P state action) (Q state action) *
        (beta state action).toReal =
      (beta state action).toReal *
        finitePMFTotalVariation (P state action) (Q state action) := by
          rw [mul_comm]
    _ ≤ finitePMFTotalVariation
        (augmentedBehaviorKernel P beta (previousAction, state))
        (augmentedBehaviorKernel Q beta (previousAction, state)) :=
      actionProbability_mul_environmentKernel_rowTV_le_augmentedKernel_rowTV
        P Q beta (previousAction, state) action
    _ ≤ eta := haugmented

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A uniform positive behavior floor turns uniform augmented-row TV control
into simultaneous control of every state--action environment row.  The price
is exactly `1 / behaviorFloor`. -/
theorem environmentKernel_rowTV_le_div_behaviorFloor
    (P Q : Z → A → PMF Z) (beta : MarkovBehaviorPolicy Z A)
    {behaviorFloor eta : ℝ} (hbehaviorFloor_pos : 0 < behaviorFloor)
    (hbehaviorFloor :
      ∀ state action, behaviorFloor ≤ (beta state action).toReal)
    (haugmented : ∀ current : ControlledObservation Z A,
      finitePMFTotalVariation
          (augmentedBehaviorKernel P beta current)
          (augmentedBehaviorKernel Q beta current) ≤ eta) :
    ∀ state action,
      finitePMFTotalVariation (P state action) (Q state action) ≤
        eta / behaviorFloor := by
  intro state action
  rw [le_div_iff₀ hbehaviorFloor_pos]
  calc
    finitePMFTotalVariation (P state action) (Q state action) * behaviorFloor =
      behaviorFloor *
        finitePMFTotalVariation (P state action) (Q state action) := by
          rw [mul_comm]
    _ ≤ (beta state action).toReal *
        finitePMFTotalVariation (P state action) (Q state action) := by
      exact mul_le_mul_of_nonneg_right
        (hbehaviorFloor state action)
        (finitePMFTotalVariation_nonneg (P state action) (Q state action))
    _ ≤ finitePMFTotalVariation
        (augmentedBehaviorKernel P beta (action, state))
        (augmentedBehaviorKernel Q beta (action, state)) :=
      actionProbability_mul_environmentKernel_rowTV_le_augmentedKernel_rowTV
        P Q beta (action, state) action
    _ ≤ eta := haugmented (action, state)

end

end FormalSLT.StochasticDynamics
