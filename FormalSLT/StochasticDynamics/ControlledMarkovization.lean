/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledTrajectory

/-!
# Markovization of state-based controlled behavior

This file embeds a state-based behavior policy into the history-dependent
controlled-trajectory interface.  The resulting process on action--state
pairs is exactly an ordinary finite Markov chain, so the controlled prefix
kernel and path law can be rewritten using the existing homogeneous Markov
API.

The augmented state is `ControlledObservation Z A = A × Z`: the action is
the first component and the state revealed after that action is the second.
This convention is independent of any state-major ordering used by generated
application tables; converting such tables requires an explicit index map.

These are semantic identities.  They require no stationarity, contraction,
policy overlap, or statistical confidence assumptions.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A : Type*}
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A behavior policy which depends only on the currently observed state. -/
abbrev MarkovBehaviorPolicy (Z A : Type*) := Z → PMF A

/-- View a state-based behavior policy as a history policy by reading the
state in the last completed action--state coordinate. -/
def markovBehaviorPolicyAsHistory
    (β : MarkovBehaviorPolicy Z A) : BehaviorPolicy Z A :=
  fun n u ↦ β (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2

/-- Homogeneous transition PMF on action--state pairs induced by a controlled
environment and a state-based behavior policy. -/
def augmentedBehaviorKernel
    (P : Z → A → PMF Z) (β : MarkovBehaviorPolicy Z A) :
    ControlledObservation Z A → PMF (ControlledObservation Z A) :=
  fun current ↦
    (β current.2).bind fun a ↦
      (P current.2 a).map fun y ↦ (a, y)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Exact mass of an action--state continuation under the augmented behavior
kernel. -/
@[simp]
theorem augmentedBehaviorKernel_apply
    (P : Z → A → PMF Z) (β : MarkovBehaviorPolicy Z A)
    (current next : ControlledObservation Z A) :
    augmentedBehaviorKernel P β current next =
      β current.2 next.1 * P current.2 next.1 next.2 := by
  classical
  rcases next with ⟨a, y⟩
  simp only [augmentedBehaviorKernel, PMF.bind_apply, PMF.map_apply,
    tsum_fintype]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha
    simp [Ne.symm ha]
  · simp

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The history-interface continuation under a state-based policy is exactly
the homogeneous augmented-state transition row at the current coordinate. -/
@[simp]
theorem controlledContinuationPMF_markovBehaviorPolicy
    (P : Z → A → PMF Z) (β : MarkovBehaviorPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A) :
    controlledContinuationPMF P (markovBehaviorPolicyAsHistory β) n u =
      augmentedBehaviorKernel P β
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  classical
  ext next
  rw [show next = (next.1, next.2) by exact Prod.eta next,
    controlledContinuationPMF_apply, augmentedBehaviorKernel_apply]
  rfl

/-- The controlled prefix kernel for a state-based behavior policy is the
ordinary Markov prefix kernel of the augmented action--state chain. -/
theorem controlledPrefixKernel_markovBehaviorPolicy
    (P : Z → A → PMF Z) (β : MarkovBehaviorPolicy Z A) (n : ℕ) :
    controlledPrefixKernel P (markovBehaviorPolicyAsHistory β) n =
      prefixKernel (augmentedBehaviorKernel P β) n := by
  apply Kernel.ext
  intro u
  change
    (controlledContinuationPMF P (markovBehaviorPolicyAsHistory β) n u).toMeasure =
      (augmentedBehaviorKernel P β
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  rw [controlledContinuationPMF_markovBehaviorPolicy]

/-- Consequently, the controlled behavior-law trajectory is exactly the
ordinary Markov path law of the augmented action--state chain. -/
theorem controlledTrajectoryMeasure_markovBehaviorPolicy
    (P : Z → A → PMF Z) (β : MarkovBehaviorPolicy Z A)
    (initial : ControlledObservation Z A) :
    controlledTrajectoryMeasure P (markovBehaviorPolicyAsHistory β) initial =
      markovPathMeasure (augmentedBehaviorKernel P β) initial := by
  unfold controlledTrajectoryMeasure markovPathMeasure trajectoryMeasure
  have hkernel :
      controlledPrefixKernel P (markovBehaviorPolicyAsHistory β) =
        prefixKernel (augmentedBehaviorKernel P β) := by
    funext n
    exact controlledPrefixKernel_markovBehaviorPolicy P β n
  cases hkernel
  rfl

end

end FormalSLT.StochasticDynamics
