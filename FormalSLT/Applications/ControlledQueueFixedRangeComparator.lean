/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueSharpStructuredOPE
import FormalSLT.Applications.ControlledQueueFixedRangePersistenceConfidence
import FormalSLT.StochasticDynamics.StationaryTargetPolicyFixedRangeOPE

/-!
# Non-variance-adaptive controlled-queue comparator

This module instantiates the fixed-range stationary target-policy OPE event
for the controlled queue and intersects it with the fixed-range two-sided
persistence-hit event.  It keeps the same selected target policy, predictor,
depth-twelve potential, importance cap, tilts, and `1 / 40 + 1 / 40`
allocation as the predeclared matched-comparison row.  Only the two
empirical-Bernstein stochastic corrections are replaced by fixed-range
sub-gamma corrections.

The theorem is an event-level comparator.  It does not evaluate a trace,
prove membership of a named path, certify a numerical endpoint, modify the
prospective protocol, or make a novelty claim.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

/-- Fixed-range target-policy risk boundary for the selected depth-twelve
potential and the same risk tilt used by the primary structured row. -/
def fixedRangeSelectedRiskBoundary
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  stationaryTargetPolicyFixedRangeOPEBoundary
    queueHypothesisPrior queueRiskTiltWeight knownKernelRiskTilt
    (markovBehaviorPolicyAsHistory behaviorPolicy)
    queueHypothesisTargetPolicy queueHypothesisScore knownKernelPotential
    knownKernelPotentialSpan (3 / 2 : ℝ) knownKernelSelectedPosterior
    queueRiskFailureBudget () n path

/-- Candidate discrepancy plus the fixed-range two-sided persistence radius. -/
def fixedRangeStructuredPersistenceBudget
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  |candidatePersistenceHitProbability nominalCandidateIndex -
      empiricalPersistenceHitRate n path| +
    fixedRangePersistenceHitRadius sharpStructuredPersistenceTiltWeight
      sharpStructuredPersistenceTilt
      sharpStructuredPersistenceFailureBudget () n

/-- The same checked affine refresh-sensitivity residual used by the primary
row, now fed the fixed-range persistence budget. -/
def fixedRangeStructuredResidual
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  sharpSelectedCandidateDriftOscillation +
    sharpSelectedRefreshSensitivityOscillation *
      fixedRangeStructuredPersistenceBudget n path

/-- Complete selected non-variance-adaptive comparator boundary. -/
def fixedRangeStructuredOPEBoundary
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  fixedRangeSelectedRiskBoundary n path +
    fixedRangeStructuredResidual n path

private theorem knownKernelRiskTilt_lt_three (atom : Unit) :
    knownKernelRiskTilt atom < 3 :=
  (knownKernelRiskTilt_lt_one atom).trans (by norm_num)

private theorem sharpStructuredPersistenceTilt_lt_three (atom : Unit) :
    sharpStructuredPersistenceTilt atom < 3 :=
  (sharpStructuredPersistenceTilt_lt_one atom).trans (by norm_num)

/-- For any fixed true refresh parameter and initial observation, one event
of complement mass at most `1 / 20` controls the selected stationary risk by
the fixed-range matched-comparison boundary at every positive time. -/
theorem exists_controlledQueueFixedRangeComparator_event
    (gamma : PersistenceParameter) (initial : Observation) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent, ∀ n : ℕ, 0 < n →
        stationaryTargetPolicyPosteriorRisk
            (refreshEnvironment gamma) queueHypothesisTargetPolicy
            (queueHypothesisStationary (refreshEnvironment gamma))
            queueHypothesisScore knownKernelSelectedPosterior <
          fixedRangeStructuredOPEBoundary n path := by
  let mu := controlledTrajectoryMeasure (refreshEnvironment gamma)
    (markovBehaviorPolicyAsHistory behaviorPolicy) initial
  rcases
      exists_stationaryApproximateTargetPolicyFixedRangeOPE_signedResidual_event
        (P := refreshEnvironment gamma)
        (markovBehaviorPolicyAsHistory behaviorPolicy) initial
        queueHypothesisTargetPolicy
        (queueHypothesisStationary (refreshEnvironment gamma))
        (queueHypothesisStationary_isInvariant (refreshEnvironment gamma))
        queueHypothesisScore queueHypothesisScore_mem_Icc
        knownKernelPotential
        (B := knownKernelPotentialSpan) (C := (3 / 2 : ℝ))
        (by norm_num [knownKernelPotentialSpan,
          ControlledQueueKnownKernelReceiptData.selectedPotentialSpan])
        (by norm_num) knownKernelPotential_span
        queueHypothesis_overlap queueHypothesis_ratioBound_three_halves
        queueHypothesisPrior_isFullSupport queueRiskTiltWeight_isFullSupport
        queueRiskFailureBudget_pos knownKernelRiskTilt_pos
        knownKernelRiskTilt_lt_three with
    ⟨riskGood, hriskMass, hriskGood⟩
  rcases exists_fixedRangePersistenceHitConfidence_event
      (τ := Unit) gamma initial
      sharpStructuredPersistenceTiltWeight_isFullSupport
      sharpStructuredPersistenceFailureBudget_pos
      sharpStructuredPersistenceTilt_pos
      sharpStructuredPersistenceTilt_lt_three with
    ⟨persistenceGood, hpersistenceMass, hpersistenceGood⟩
  let goodEvent : Set (ℕ → Observation) := riskGood ∩ persistenceGood
  refine ⟨goodEvent, ?_, ?_⟩
  · have hunion := measureReal_union_le
      (μ := mu) riskGoodᶜ persistenceGoodᶜ
    calc
      mu.real goodEventᶜ = mu.real (riskGoodᶜ ∪ persistenceGoodᶜ) := by
        congr 1
        ext path
        by_cases hrisk : path ∈ riskGood <;>
          by_cases hpersistence : path ∈ persistenceGood <;>
            simp [goodEvent, hrisk, hpersistence]
      _ ≤ mu.real riskGoodᶜ + mu.real persistenceGoodᶜ := hunion
      _ ≤ queueRiskFailureBudget +
          sharpStructuredPersistenceFailureBudget :=
        add_le_add hriskMass hpersistenceMass
      _ = 1 / 20 := by
        norm_num [queueRiskFailureBudget,
          sharpStructuredPersistenceFailureBudget]
  · intro path hpath n hn
    have hraw := hriskGood path hpath.1 () knownKernelSelectedPosterior
      knownKernelSelectedPosterior_isPMF n hn
    have hpersistence := hpersistenceGood path hpath.2 () n hn
    have hhit :
        |persistenceHitProbability gamma -
            candidatePersistenceHitProbability nominalCandidateIndex| ≤
          fixedRangeStructuredPersistenceBudget n path := by
      unfold fixedRangeStructuredPersistenceBudget
      calc
        |persistenceHitProbability gamma -
            candidatePersistenceHitProbability nominalCandidateIndex| =
          |candidatePersistenceHitProbability nominalCandidateIndex -
            persistenceHitProbability gamma| := abs_sub_comm _ _
        _ ≤
            |candidatePersistenceHitProbability nominalCandidateIndex -
                empiricalPersistenceHitRate n path| +
              |persistenceHitProbability gamma -
                empiricalPersistenceHitRate n path| := by
          have htriangle := abs_sub_le
            (candidatePersistenceHitProbability nominalCandidateIndex)
            (empiricalPersistenceHitRate n path)
            (persistenceHitProbability gamma)
          simpa only [abs_sub_comm
            (empiricalPersistenceHitRate n path)
            (persistenceHitProbability gamma)] using htriangle
        _ ≤
            |candidatePersistenceHitProbability nominalCandidateIndex -
                empiricalPersistenceHitRate n path| +
              fixedRangePersistenceHitRadius
                sharpStructuredPersistenceTiltWeight
                sharpStructuredPersistenceTilt
                sharpStructuredPersistenceFailureBudget () n := by
          exact add_le_add (le_refl _) hpersistence.le
    have hselectedResidual : ∀ state,
        |approximateTargetPolicyPoissonResidual
            (refreshEnvironment gamma)
            (queueHypothesisTargetPolicy
              queueThresholdNominalModelHypothesis)
            (queueHypothesisStationary (refreshEnvironment gamma)
              queueThresholdNominalModelHypothesis)
            (queueHypothesisScore queueThresholdNominalModelHypothesis)
            knownKernelSelectedPotential state| ≤
          fixedRangeStructuredResidual n path := by
      intro state
      simpa [fixedRangeStructuredResidual] using
        abs_approximateTargetPolicyPoissonResidual_le_refreshSensitivity
          gamma nominalCandidateIndex
          (queueHypothesisTargetPolicy
            queueThresholdNominalModelHypothesis)
          (queueHypothesisStationary (refreshEnvironment gamma)
            queueThresholdNominalModelHypothesis)
          (queueHypothesisStationary_isInvariant
            (refreshEnvironment gamma)
            queueThresholdNominalModelHypothesis)
          knownKernelSelectedCandidateDrift_finiteOscillation_le
          knownKernelSelectedRefreshSensitivity_finiteOscillation_le
          hhit state
    have hnegative :
        -stationaryTargetPolicyPosteriorResidualAverage
            (refreshEnvironment gamma) queueHypothesisTargetPolicy
            (queueHypothesisStationary (refreshEnvironment gamma))
            queueHypothesisScore knownKernelPotential
            knownKernelSelectedPosterior n path ≤
          fixedRangeStructuredResidual n path := by
      have hpotential :
          knownKernelPotential queueThresholdNominalModelHypothesis =
            knownKernelSelectedPotential := by
        funext state
        simp [knownKernelPotential]
      unfold stationaryTargetPolicyPosteriorResidualAverage
        knownKernelSelectedPosterior
      rw [pacBayesPosteriorAverage_dirac, hpotential]
      unfold forwardPrefixMean
      rw [← neg_div]
      apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
      have hsum :
          ∑ k ∈ Finset.range n,
              -approximateTargetPolicyPoissonResidual
                (refreshEnvironment gamma)
                (queueHypothesisTargetPolicy
                  queueThresholdNominalModelHypothesis)
                (queueHypothesisStationary (refreshEnvironment gamma)
                  queueThresholdNominalModelHypothesis)
                (queueHypothesisScore queueThresholdNominalModelHypothesis)
                knownKernelSelectedPotential (path k).2 ≤
            ∑ _k ∈ Finset.range n,
              fixedRangeStructuredResidual n path := by
        apply Finset.sum_le_sum
        intro k _hk
        exact (neg_le_abs _).trans (hselectedResidual (path k).2)
      rw [Finset.sum_neg_distrib] at hsum
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
    unfold fixedRangeStructuredOPEBoundary fixedRangeSelectedRiskBoundary
    linarith

end

end FormalSLT.Applications.ControlledQueue
