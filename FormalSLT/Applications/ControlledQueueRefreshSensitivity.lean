/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueuePersistenceConfidence
import FormalSLT.StochasticDynamics.StationaryTargetPolicyRobustCandidate

/-!
# Exact refresh-family drift sensitivity for the controlled queue

The controlled-queue environments form a one-parameter uniform-refresh
family.  This module records the corresponding exact affine identity for a
target-policy Poisson drift.  The coefficient is written in terms of the
observable persistence-hit probability, rather than the latent persistence
parameter, which introduces the normalization factor `24 / 23`.

This is a deterministic application bridge.  It does not construct a
confidence event, select a candidate, evaluate a frozen trace, or assert that
any particular path belongs to a theorem-produced event.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

/-- Derivative of a target-policy Poisson drift with respect to the
persistence-hit probability of the 24-state refresh family.  The two sums
separate the transition-score and potential contributions so downstream
finite-state receipts can certify either contribution without expanding the
other one. -/
def refreshTargetPolicyPoissonDriftSensitivity
    (target : MarkovTargetPolicy PhysicalState Action)
    (score : TargetPolicyTransitionScore PhysicalState Action)
    (potential : PhysicalState → ℝ) (state : PhysicalState) : ℝ :=
  (24 / 23 : ℝ) *
    ((∑ action : Action, (target state action).toReal *
        (score state action
            (candidateKernelStepStateAction state action) -
          (1 / 24 : ℝ) *
            ∑ nextState : PhysicalState, score state action nextState)) +
      ∑ action : Action, (target state action).toReal *
        (potential (candidateKernelStepStateAction state action) -
          (1 / 24 : ℝ) *
            ∑ nextState : PhysicalState, potential nextState))

private theorem refreshEnvironment_expectation_eq
    (gamma : PersistenceParameter) (state : PhysicalState) (action : Action)
    (f : PhysicalState → ℝ) :
    (∑ nextState : PhysicalState,
        (refreshEnvironment gamma state action nextState).toReal *
          f nextState) =
      ((1 - (gamma : ℝ)) / 24) *
          ∑ nextState : PhysicalState, f nextState +
        (gamma : ℝ) *
          f (candidateKernelStepStateAction state action) := by
  simp_rw [refreshEnvironment_apply_toReal, refreshEnvironmentMass, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

private theorem refreshEnvironment_expectation_sub_eq
    (gamma gamma' : PersistenceParameter) (state : PhysicalState)
    (action : Action) (f : PhysicalState → ℝ) :
    (∑ nextState : PhysicalState,
        (refreshEnvironment gamma state action nextState).toReal *
          f nextState) -
        ∑ nextState : PhysicalState,
          (refreshEnvironment gamma' state action nextState).toReal *
            f nextState =
      ((gamma : ℝ) - (gamma' : ℝ)) *
        (f (candidateKernelStepStateAction state action) -
          (1 / 24 : ℝ) * ∑ nextState : PhysicalState, f nextState) := by
  rw [refreshEnvironment_expectation_eq,
    refreshEnvironment_expectation_eq]
  ring

private theorem refreshTargetPolicyExpectation_sub_eq
    (gamma gamma' : PersistenceParameter)
    (target : MarkovTargetPolicy PhysicalState Action)
    (f : Action → PhysicalState → ℝ) (state : PhysicalState) :
    (∑ action : Action, (target state action).toReal *
        ∑ nextState : PhysicalState,
          (refreshEnvironment gamma state action nextState).toReal *
            f action nextState) -
        ∑ action : Action, (target state action).toReal *
          ∑ nextState : PhysicalState,
            (refreshEnvironment gamma' state action nextState).toReal *
              f action nextState =
      ((gamma : ℝ) - (gamma' : ℝ)) *
        ∑ action : Action, (target state action).toReal *
          (f action (candidateKernelStepStateAction state action) -
            (1 / 24 : ℝ) *
              ∑ nextState : PhysicalState, f action nextState) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ action : Action,
        ((gamma : ℝ) - (gamma' : ℝ)) *
          ((target state action).toReal *
            (f action (candidateKernelStepStateAction state action) -
              (1 / 24 : ℝ) *
                ∑ nextState : PhysicalState, f action nextState)) := by
      apply Finset.sum_congr rfl
      intro action _haction
      rw [← mul_sub, refreshEnvironment_expectation_sub_eq]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- The true refresh-family drift minus any generated candidate drift is
exactly the persistence-hit discrepancy times the normalized refresh
sensitivity.  In particular, no factor two is introduced by centering or by
total variation. -/
theorem targetPolicyPoissonDrift_refresh_sub_candidate_eq
    (gamma : PersistenceParameter) (candidate : CandidateIndex)
    (target : MarkovTargetPolicy PhysicalState Action)
    (score : TargetPolicyTransitionScore PhysicalState Action)
    (potential : PhysicalState → ℝ) (state : PhysicalState) :
    targetPolicyPoissonDrift (refreshEnvironment gamma) target
          score potential state -
        targetPolicyPoissonDrift (candidateEnvironment candidate) target
          score potential state =
      (persistenceHitProbability gamma -
          candidatePersistenceHitProbability candidate) *
        refreshTargetPolicyPoissonDriftSensitivity
          target score potential state := by
  rw [candidateEnvironment_eq_refreshEnvironment]
  unfold targetPolicyPoissonDrift
  rw [show
      targetPolicyRowRisk (refreshEnvironment gamma) target score state +
            targetPolicyPotentialMean (refreshEnvironment gamma) target
              potential state - potential state -
          (targetPolicyRowRisk
              (refreshEnvironment (candidatePersistenceParameter candidate))
                target score state +
            targetPolicyPotentialMean
              (refreshEnvironment (candidatePersistenceParameter candidate))
                target potential state - potential state) =
        (targetPolicyRowRisk (refreshEnvironment gamma) target score state -
          targetPolicyRowRisk
            (refreshEnvironment (candidatePersistenceParameter candidate))
              target score state) +
        (targetPolicyPotentialMean (refreshEnvironment gamma) target
              potential state -
          targetPolicyPotentialMean
            (refreshEnvironment (candidatePersistenceParameter candidate))
              target potential state) by ring]
  unfold targetPolicyRowRisk targetPolicyPotentialMean
  rw [refreshTargetPolicyExpectation_sub_eq gamma
      (candidatePersistenceParameter candidate) target
      (fun action nextState ↦ score state action nextState) state,
    refreshTargetPolicyExpectation_sub_eq gamma
      (candidatePersistenceParameter candidate) target
      (fun _action nextState ↦ potential nextState) state]
  unfold candidatePersistenceHitProbability candidatePersistenceParameter
    persistenceHitProbability
    refreshTargetPolicyPoissonDriftSensitivity
  ring

/-- Sharp residual transfer specialized to the queue refresh family.  A
candidate-drift oscillation certificate and a sensitivity-oscillation
certificate compose with any upper bound on the observable persistence-hit
discrepancy. -/
theorem abs_approximateTargetPolicyPoissonResidual_le_refreshSensitivity
    (gamma : PersistenceParameter) (candidate : CandidateIndex)
    (target : MarkovTargetPolicy PhysicalState Action)
    (stationary : PMF PhysicalState)
    (hstationary : IsInvariantPMF
      (targetPolicyKernel (refreshEnvironment gamma) target) stationary)
    {score : TargetPolicyTransitionScore PhysicalState Action}
    {potential : PhysicalState → ℝ} {epsilon sensitivityBound eta : ℝ}
    (hcandidate :
      finiteOscillation
          (targetPolicyPoissonDrift (candidateEnvironment candidate)
            target score potential) ≤ epsilon)
    (hsensitivity :
      finiteOscillation
          (refreshTargetPolicyPoissonDriftSensitivity
            target score potential) ≤ sensitivityBound)
    (hhit :
      |persistenceHitProbability gamma -
        candidatePersistenceHitProbability candidate| ≤ eta)
    (state : PhysicalState) :
    |approximateTargetPolicyPoissonResidual
        (refreshEnvironment gamma) target stationary score potential state| ≤
      epsilon + sensitivityBound * eta := by
  apply abs_approximateTargetPolicyPoissonResidual_le_affineDrift
    (refreshEnvironment gamma) (candidateEnvironment candidate)
    target stationary hstationary
    (refreshTargetPolicyPoissonDriftSensitivity target score potential)
  · intro nextState
    have hexact := targetPolicyPoissonDrift_refresh_sub_candidate_eq
      gamma candidate target score potential nextState
    calc
      targetPolicyPoissonDrift (refreshEnvironment gamma) target
          score potential nextState =
        (targetPolicyPoissonDrift (refreshEnvironment gamma) target
            score potential nextState -
          targetPolicyPoissonDrift (candidateEnvironment candidate) target
            score potential nextState) +
          targetPolicyPoissonDrift (candidateEnvironment candidate) target
            score potential nextState := by ring
      _ = (persistenceHitProbability gamma -
            candidatePersistenceHitProbability candidate) *
            refreshTargetPolicyPoissonDriftSensitivity
              target score potential nextState +
          targetPolicyPoissonDrift (candidateEnvironment candidate) target
            score potential nextState := by rw [hexact]
      _ = targetPolicyPoissonDrift (candidateEnvironment candidate) target
            score potential nextState +
          (persistenceHitProbability gamma -
            candidatePersistenceHitProbability candidate) *
            refreshTargetPolicyPoissonDriftSensitivity
              target score potential nextState := by ring
  · exact hcandidate
  · exact hsensitivity
  · exact hhit

end

end FormalSLT.Applications.ControlledQueue
