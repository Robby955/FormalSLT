/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueTargetPolicyScores
import Mathlib.Probability.Distributions.Uniform

/-!
# Controlled-queue candidate contraction

Every generated queue candidate has a common uniform-refresh component.  This
module turns the generated table-wide cell floor into a target-policy kernel
minorization and then into a Dobrushin upper bound.  The proof evaluates three
candidate tables once; it does not enumerate all pairs of the twenty-four
target-kernel rows.

The contraction certificate holds for every state-based target policy, not
only the four generated policies.  Equality of the Dobrushin coefficient is
neither needed nor claimed.  The uniform PMF below is a finite-depth Poisson
reference; it is not claimed invariant for an arbitrary target policy.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

noncomputable section

/-- Uniform reference PMF on the twenty-four physical queue states. -/
def uniformStateReference : PMF PhysicalState :=
  PMF.uniformOfFintype PhysicalState

@[simp]
theorem uniformStateReference_apply_toReal (state : PhysicalState) :
    (uniformStateReference state).toReal = 1 / 24 := by
  rw [uniformStateReference, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv]
  norm_num

private theorem candidateRefreshBase_le_targetPolicyKernel_apply_toReal
    (candidate : CandidateIndex)
    (pi : MarkovTargetPolicy PhysicalState Action)
    (state nextState : PhysicalState) :
    candidateRefreshBase candidate ≤
      (targetPolicyKernel (candidateEnvironment candidate) pi
        state nextState).toReal := by
  unfold targetPolicyKernel
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro action _haction
    exact ENNReal.mul_ne_top
      ((pi state).apply_ne_top action)
      ((candidateEnvironment candidate state action).apply_ne_top nextState))]
  simp only [ENNReal.toReal_mul, candidateEnvironment_apply_toReal]
  calc
    candidateRefreshBase candidate =
        (∑ action : Action, (pi state action).toReal) *
          candidateRefreshBase candidate := by
            rw [finitePMF_real_mass_sum, one_mul]
    _ = ∑ action : Action,
        (pi state action).toReal * candidateRefreshBase candidate := by
          rw [Finset.sum_mul]
    _ ≤ ∑ action : Action,
        (pi state action).toReal *
          (candidateKernelTableMass candidate
            (stateActionRowEquiv (state, action)) nextState : ℝ) := by
      apply Finset.sum_le_sum
      intro action _haction
      exact mul_le_mul_of_nonneg_left
        (candidateRefreshBase_le_candidateKernelTableMass candidate
          (stateActionRowEquiv (state, action)) nextState)
        ENNReal.toReal_nonneg

/-- Every row of a candidate's induced target-policy kernel contains the
candidate's declared common uniform component. -/
theorem candidateTargetPolicyKernel_common_minorization
    (candidate : CandidateIndex)
    (pi : MarkovTargetPolicy PhysicalState Action)
    (state nextState : PhysicalState) :
    (1 - candidateGamma candidate) *
        (uniformStateReference nextState).toReal ≤
      (targetPolicyKernel (candidateEnvironment candidate) pi
        state nextState).toReal := by
  rw [uniformStateReference_apply_toReal]
  have h := candidateRefreshBase_le_targetPolicyKernel_apply_toReal
    candidate pi state nextState
  calc
    (1 - candidateGamma candidate) * (1 / 24 : ℝ) =
        candidateRefreshBase candidate := by
      unfold candidateRefreshBase
      ring
    _ ≤ (targetPolicyKernel (candidateEnvironment candidate) pi
        state nextState).toReal := h

/-- Any two rows of a candidate's induced target-policy kernel are within the
candidate persistence weight in total variation. -/
theorem candidateTargetPolicyKernel_rowTV_le_gamma
    (candidate : CandidateIndex)
    (pi : MarkovTargetPolicy PhysicalState Action)
    (state otherState : PhysicalState) :
    finitePMFTotalVariation
        (targetPolicyKernel (candidateEnvironment candidate) pi state)
        (targetPolicyKernel (candidateEnvironment candidate) pi otherState) ≤
      candidateGamma candidate := by
  exact finitePMFTotalVariation_le_of_common_minorization
    (targetPolicyKernel (candidateEnvironment candidate) pi state)
    (targetPolicyKernel (candidateEnvironment candidate) pi otherState)
    uniformStateReference
    (candidateTargetPolicyKernel_common_minorization candidate pi state)
    (candidateTargetPolicyKernel_common_minorization candidate pi otherState)

/-- The induced target-policy kernel's Dobrushin coefficient is at most the
candidate persistence weight. -/
theorem candidateTargetPolicyKernel_dobrushin_le_gamma
    (candidate : CandidateIndex)
    (pi : MarkovTargetPolicy PhysicalState Action) :
    finiteDobrushinCoefficient
        (targetPolicyKernel (candidateEnvironment candidate) pi) ≤
      candidateGamma candidate := by
  exact finiteDobrushinCoefficient_le_of_common_minorization
    (targetPolicyKernel (candidateEnvironment candidate) pi)
    uniformStateReference
    (candidateTargetPolicyKernel_common_minorization candidate pi)

/-- The generated candidate target-policy kernel contracts finite oscillation
by its declared persistence weight. -/
theorem candidateTargetPolicyKernel_isOscillationContraction
    (candidate : CandidateIndex)
    (pi : MarkovTargetPolicy PhysicalState Action) :
    IsOscillationContraction
      (targetPolicyKernel (candidateEnvironment candidate) pi)
      (candidateGamma candidate) := by
  exact isOscillationContraction_of_finiteDobrushinCoefficient_le _
    (candidateTargetPolicyKernel_dobrushin_le_gamma candidate pi)

/-- All generated candidate persistence weights are nonnegative and strictly below
one. -/
theorem candidateGamma_mem_Ico (candidate : CandidateIndex) :
    candidateGamma candidate ∈ Set.Ico (0 : ℝ) 1 := by
  fin_cases candidate <;>
    norm_num [candidateGamma, ControlledQueueData.candidateGammaTable]

end

end FormalSLT.Applications.ControlledQueue
