/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueContraction
import FormalSLT.Applications.ControlledQueuePersistenceConfidence
import FormalSLT.StochasticDynamics.FiniteInvariantUniqueness

/-!
# Invariant-law uniqueness for the controlled-queue refresh family

Every admissible persistence parameter gives the same uniform common
minorization used by the generated candidate kernels. The resulting Dobrushin
bound is strictly below one, so every state-based target policy has one
invariant PMF.

The coefficient is bounded above by the persistence parameter; equality is
not claimed. This module identifies the invariant law but does not compute a
closed form or a stationary risk.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

noncomputable section

private theorem refreshTargetPolicyKernel_common_minorization
    (gamma : PersistenceParameter)
    (pi : MarkovTargetPolicy PhysicalState Action)
    (state nextState : PhysicalState) :
    (1 - (gamma : ℝ)) * (uniformStateReference nextState).toReal ≤
      (targetPolicyKernel (refreshEnvironment gamma) pi
        state nextState).toReal := by
  unfold targetPolicyKernel
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro action _haction
    exact ENNReal.mul_ne_top
      ((pi state).apply_ne_top action)
      ((refreshEnvironment gamma state action).apply_ne_top nextState))]
  simp only [ENNReal.toReal_mul, refreshEnvironment_apply_toReal]
  rw [uniformStateReference_apply_toReal]
  calc
    (1 - (gamma : ℝ)) * (1 / 24 : ℝ) =
        ∑ action : Action,
          (pi state action).toReal * ((1 - (gamma : ℝ)) / 24) := by
      rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]
      ring
    _ ≤ ∑ action : Action,
        (pi state action).toReal *
          refreshEnvironmentMass gamma state action nextState := by
      apply Finset.sum_le_sum
      intro action _haction
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases hstep :
          nextState = candidateKernelStepStateAction state action
      · simp [refreshEnvironmentMass, hstep, gamma.property.1]
      · simp [refreshEnvironmentMass, hstep]

/-- The target-policy kernel induced by any admissible member of the refresh
family has Dobrushin coefficient at most its persistence parameter. -/
theorem refreshTargetPolicyKernel_dobrushin_le_gamma
    (gamma : PersistenceParameter)
    (pi : MarkovTargetPolicy PhysicalState Action) :
    finiteDobrushinCoefficient
        (targetPolicyKernel (refreshEnvironment gamma) pi) ≤
      (gamma : ℝ) := by
  exact finiteDobrushinCoefficient_le_of_common_minorization
    (targetPolicyKernel (refreshEnvironment gamma) pi)
    uniformStateReference
    (refreshTargetPolicyKernel_common_minorization gamma pi)

/-- Every admissible refresh-family target-policy kernel has exactly one
invariant PMF. -/
theorem refreshTargetPolicyKernel_existsUnique_invariantPMF
    (gamma : PersistenceParameter)
    (pi : MarkovTargetPolicy PhysicalState Action) :
    ∃! stationary : PMF PhysicalState,
      IsInvariantPMF (targetPolicyKernel (refreshEnvironment gamma) pi)
        stationary := by
  exact existsUnique_invariantPMF_of_finiteDobrushinCoefficient_lt_one _
    ((refreshTargetPolicyKernel_dobrushin_le_gamma gamma pi).trans_lt
      gamma.property.2)

end

end FormalSLT.Applications.ControlledQueue
