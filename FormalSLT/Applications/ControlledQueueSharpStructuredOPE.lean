/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelReceipt
import FormalSLT.Applications.ControlledQueueRefreshSensitivity

/-!
# Sharp structured controlled-queue OPE event

This module combines the signed-residual target-policy OPE event with the
one-dimensional persistence-confidence event for the queue refresh family.
It fixes the nominal candidate, the supplied shifted depth-twelve potential,
and the queue-threshold/nominal-model point posterior.  The residual transfer
uses the exact affine refresh sensitivity, so its pathwise cost is

`candidate drift oscillation + sensitivity oscillation * persistence budget`.

The prospective receipt wrapper fixes the true persistence parameter
`149 / 200`, initial observation `(eco, state 0)`, horizon `200000`, risk tilt
`1 / 16`, persistence tilt `1 / 64`, and failure allocation
`1 / 40 + 1 / 40 = 1 / 20`.  It does not generate a trace, prove membership of
any named path in the good event, or assert that the eventual numerical
endpoint is below the preregistered threshold.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

noncomputable section

/-! ## Frozen constants and pathwise boundary -/

/-- Singleton persistence tilt used by the prospective sharp receipt. -/
def sharpStructuredPersistenceTilt (_atom : Unit) : ℝ := 1 / 64

/-- Singleton allocation for the prospective persistence event. -/
def sharpStructuredPersistenceTiltWeight : Unit → ℝ :=
  finiteUniformRealPMF Unit

/-- Persistence-event failure allocation in the prospective receipt. -/
def sharpStructuredPersistenceFailureBudget : ℝ := 1 / 40

/-- Frozen exact rational upper bound on the nominal selected candidate-drift oscillation. -/
def sharpSelectedCandidateDriftOscillation : ℝ :=
  58989951 / 9007199254740992

/-- Frozen exact rational upper bound on the selected hit-normalized sensitivity oscillation. -/
def sharpSelectedRefreshSensitivityOscillation : ℝ :=
  831542406207231 / 3236962232172544

/-- Persistence-hit discrepancy budget against the nominal candidate. -/
def sharpStructuredPersistenceBudget
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  structuredCandidateTVBudget nominalCandidateIndex
    sharpStructuredPersistenceTiltWeight sharpStructuredPersistenceTilt
    sharpStructuredPersistenceFailureBudget () n path

/-- Sharp selected residual cost on the common risk/persistence event. -/
def sharpStructuredResidual
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  sharpSelectedCandidateDriftOscillation +
    sharpSelectedRefreshSensitivityOscillation *
      sharpStructuredPersistenceBudget n path

/-- Selected OPE boundary plus the sharp structured residual cost. -/
def sharpStructuredOPEBoundary
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  knownKernelOPEBoundary knownKernelSelectedPosterior n path +
    sharpStructuredResidual n path

/-- Prospectively fixed off-grid true persistence parameter `149 / 200`. -/
def sharpStructuredTruePersistence : PersistenceParameter :=
  ⟨149 / 200, by constructor <;> norm_num⟩

/-- Prospectively fixed initial observation `(eco, physical state 0)`. -/
def sharpStructuredInitial : Observation :=
  ((0 : Action), (0 : PhysicalState))

/-- Prospectively fixed terminal score horizon. -/
def sharpStructuredHorizon : ℕ := 200000

@[simp]
theorem sharpStructuredTruePersistence_apply :
    (sharpStructuredTruePersistence : ℝ) = 149 / 200 := rfl

@[simp]
theorem sharpStructuredInitial_eq :
    sharpStructuredInitial = ((0 : Action), (0 : PhysicalState)) := rfl

/-- The singleton persistence allocation has full support. -/
theorem sharpStructuredPersistenceTiltWeight_isFullSupport :
    IsFullSupportPMF sharpStructuredPersistenceTiltWeight :=
  finiteUniformRealPMF_isFullSupport Unit

/-- The prospective persistence tilt is positive. -/
theorem sharpStructuredPersistenceTilt_pos (atom : Unit) :
    0 < sharpStructuredPersistenceTilt atom := by
  cases atom
  norm_num [sharpStructuredPersistenceTilt]

/-- The prospective persistence tilt is strictly below one. -/
theorem sharpStructuredPersistenceTilt_lt_one (atom : Unit) :
    sharpStructuredPersistenceTilt atom < 1 := by
  cases atom
  norm_num [sharpStructuredPersistenceTilt]

/-- The prospective persistence-event allocation is positive. -/
theorem sharpStructuredPersistenceFailureBudget_pos :
    0 < sharpStructuredPersistenceFailureBudget := by
  norm_num [sharpStructuredPersistenceFailureBudget]

/-- Exact quadratic cumulant cost for the prospective risk tilt. -/
theorem knownKernelRiskTilt_psi_le_one_fourEighty :
    forwardEmpiricalBernsteinPsi (knownKernelRiskTilt ()) ≤ 1 / 480 := by
  have h := forwardEmpiricalBernsteinPsi_le_quadratic
    (lam := knownKernelRiskTilt ())
    (le_of_lt (knownKernelRiskTilt_pos ()))
    (knownKernelRiskTilt_lt_one ())
  norm_num [knownKernelRiskTilt] at h
  simpa [knownKernelRiskTilt] using h

/-- Exact quadratic cumulant cost for the prospective persistence tilt. -/
theorem sharpStructuredPersistenceTilt_psi_le_one_eightThousandSixtyFour :
    forwardEmpiricalBernsteinPsi (sharpStructuredPersistenceTilt ()) ≤
      1 / 8064 := by
  have h := forwardEmpiricalBernsteinPsi_le_quadratic
    (lam := sharpStructuredPersistenceTilt ())
    (le_of_lt (sharpStructuredPersistenceTilt_pos ()))
    (sharpStructuredPersistenceTilt_lt_one ())
  norm_num [sharpStructuredPersistenceTilt] at h
  simpa [sharpStructuredPersistenceTilt] using h

/-! ## Exact finite-state oscillation certificates -/

private def sharpSelectedResidualLower : ℝ :=
  -144000575053767 / 1193040362720997771575296

private def sharpSelectedResidualUpper : ℝ :=
  7669459585815921 / 1193040362720997771575296

private theorem knownKernelSelectedResidual_mem_Icc
    (state : PhysicalState) :
    knownKernelSelectedResidual state ∈
      Set.Icc sharpSelectedResidualLower sharpSelectedResidualUpper := by
  fin_cases state <;>
    norm_num [knownKernelSelectedResidual, sharpSelectedResidualLower,
      sharpSelectedResidualUpper, selectedResidualTable]

/-- The nominal selected candidate drift has the frozen tiny oscillation. -/
theorem knownKernelSelectedCandidateDrift_finiteOscillation_le :
    finiteOscillation
        (targetPolicyPoissonDrift nominalCandidateEnvironment
          (queueHypothesisTargetPolicy
            queueThresholdNominalModelHypothesis)
          (queueHypothesisScore queueThresholdNominalModelHypothesis)
          knownKernelSelectedPotential) ≤
      sharpSelectedCandidateDriftOscillation := by
  apply finiteOscillation_le
  intro state nextState
  have hstate := knownKernelSelectedPotential_residual_eq state
  have hnext := knownKernelSelectedPotential_residual_eq nextState
  have hdiff :
      targetPolicyPoissonDrift nominalCandidateEnvironment
            (queueHypothesisTargetPolicy
              queueThresholdNominalModelHypothesis)
            (queueHypothesisScore queueThresholdNominalModelHypothesis)
            knownKernelSelectedPotential nextState -
          targetPolicyPoissonDrift nominalCandidateEnvironment
            (queueHypothesisTargetPolicy
              queueThresholdNominalModelHypothesis)
            (queueHypothesisScore queueThresholdNominalModelHypothesis)
            knownKernelSelectedPotential state =
        knownKernelSelectedResidual nextState -
          knownKernelSelectedResidual state := by
    unfold approximateTargetPolicyPoissonResidual at hstate hnext
    linarith
  rw [hdiff, abs_le]
  rcases knownKernelSelectedResidual_mem_Icc state with
    ⟨hstateLower, hstateUpper⟩
  rcases knownKernelSelectedResidual_mem_Icc nextState with
    ⟨hnextLower, hnextUpper⟩
  have hwidth :
      sharpSelectedResidualUpper - sharpSelectedResidualLower =
        sharpSelectedCandidateDriftOscillation := by
    norm_num [sharpSelectedResidualUpper, sharpSelectedResidualLower,
      sharpSelectedCandidateDriftOscillation]
  constructor <;> linarith

private def sharpSelectedSensitivityLower : ℝ :=
  -25970216878939923 / 51791395714760704

private def sharpSelectedSensitivityUpper : ℝ :=
  -12665538379624227 / 51791395714760704

set_option maxHeartbeats 1000000 in
private theorem knownKernelSelectedRefreshSensitivity_mem_Icc
    (state : PhysicalState) :
    refreshTargetPolicyPoissonDriftSensitivity
        (queueHypothesisTargetPolicy queueThresholdNominalModelHypothesis)
        (queueHypothesisScore queueThresholdNominalModelHypothesis)
        knownKernelSelectedPotential state ∈
      Set.Icc sharpSelectedSensitivityLower sharpSelectedSensitivityUpper := by
  fin_cases state <;>
    norm_num [refreshTargetPolicyPoissonDriftSensitivity,
      sharpSelectedSensitivityLower, sharpSelectedSensitivityUpper,
      queueHypothesisTargetPolicy, queueHypothesisScore,
      queueThresholdNominalModelHypothesis, queueThresholdTargetIndex,
      nominalModelOverloadPredictorIndex, knownKernelSelectedPotential,
      selectedPotentialTable, targetPolicy_apply_toReal,
      targetPolicyTableIndex, policyTableMass, fixedBrierScore,
      fixedPredictorProbability,
      fixedPredictorTableValue_stateActionRowEquiv,
      fixedPredictorTableValueStateAction, overloadOutcome,
      overloadOutcomeTableValue, candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.fixedPredictorTable,
      ControlledQueueData.overloadOutcomeTable,
      ControlledQueueData.candidateKernelStepByRow,
      Fin.ext_iff, Fin.sum_univ_succ]

/-- The selected hit-normalized refresh sensitivity has the frozen exact
oscillation bound. -/
theorem knownKernelSelectedRefreshSensitivity_finiteOscillation_le :
    finiteOscillation
        (refreshTargetPolicyPoissonDriftSensitivity
          (queueHypothesisTargetPolicy
            queueThresholdNominalModelHypothesis)
          (queueHypothesisScore queueThresholdNominalModelHypothesis)
          knownKernelSelectedPotential) ≤
      sharpSelectedRefreshSensitivityOscillation := by
  apply finiteOscillation_le
  intro state nextState
  rw [abs_le]
  rcases knownKernelSelectedRefreshSensitivity_mem_Icc state with
    ⟨hstateLower, hstateUpper⟩
  rcases knownKernelSelectedRefreshSensitivity_mem_Icc nextState with
    ⟨hnextLower, hnextUpper⟩
  have hwidth :
      sharpSelectedSensitivityUpper - sharpSelectedSensitivityLower =
        sharpSelectedRefreshSensitivityOscillation := by
    norm_num [sharpSelectedSensitivityUpper, sharpSelectedSensitivityLower,
      sharpSelectedRefreshSensitivityOscillation]
  constructor <;> linarith

/-! ## Common sharp event -/

private theorem sharpCatalogStationaryRisk_mem_Icc
    (gamma : PersistenceParameter) (hypothesis : QueueHypothesis) :
    stationaryTargetPolicyRisk (refreshEnvironment gamma)
        (queueHypothesisTargetPolicy hypothesis)
        (queueHypothesisStationary (refreshEnvironment gamma) hypothesis)
        (queueHypothesisScore hypothesis) ∈ Set.Icc (0 : ℝ) 1 := by
  have hrow : ∀ state : PhysicalState,
      targetPolicyRowRisk (refreshEnvironment gamma)
          (queueHypothesisTargetPolicy hypothesis)
          (queueHypothesisScore hypothesis) state ∈ Set.Icc (0 : ℝ) 1 :=
    fun state ↦ targetPolicyRowRisk_mem_Icc
      (refreshEnvironment gamma) (queueHypothesisTargetPolicy hypothesis)
      (queueHypothesisScore_mem_Icc hypothesis) state
  unfold stationaryTargetPolicyRisk
  constructor
  · exact Finset.sum_nonneg fun state _stateMem ↦
      mul_nonneg ENNReal.toReal_nonneg (hrow state).1
  · calc
      ∑ state : PhysicalState,
          ((queueHypothesisStationary (refreshEnvironment gamma) hypothesis)
              state).toReal *
            targetPolicyRowRisk (refreshEnvironment gamma)
              (queueHypothesisTargetPolicy hypothesis)
              (queueHypothesisScore hypothesis) state ≤
          ∑ state : PhysicalState,
            ((queueHypothesisStationary (refreshEnvironment gamma) hypothesis)
                state).toReal * 1 :=
        Finset.sum_le_sum fun state _stateMem ↦
          mul_le_mul_of_nonneg_left (hrow state).2 ENNReal.toReal_nonneg
      _ = 1 := by
        rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]

private def sharpStructuredResidualEnvelope
    (n : ℕ) (path : ℕ → Observation)
    (hypothesis : QueueHypothesis) : ℝ :=
  if hypothesis = queueThresholdNominalModelHypothesis then
    sharpStructuredResidual n path
  else 1

/-- For any fixed true persistence parameter and initial observation, one
outer event of complement mass at most `1 / 20` controls the selected
stationary target-policy risk at every time `n >= 2`. -/
theorem exists_controlledQueueSharpStructuredOPE_event
    (gamma : PersistenceParameter) (initial : Observation) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
        stationaryTargetPolicyPosteriorRisk
            (refreshEnvironment gamma) queueHypothesisTargetPolicy
            (queueHypothesisStationary (refreshEnvironment gamma))
            queueHypothesisScore knownKernelSelectedPosterior <
          sharpStructuredOPEBoundary n path := by
  let mu := controlledTrajectoryMeasure (refreshEnvironment gamma)
    (markovBehaviorPolicyAsHistory behaviorPolicy) initial
  rcases exists_stationaryApproximateTargetPolicyOPE_signedResidual_event
      (P := refreshEnvironment gamma)
      (markovBehaviorPolicyAsHistory behaviorPolicy) initial
      queueHypothesisTargetPolicy
      (queueHypothesisStationary (refreshEnvironment gamma))
      (queueHypothesisStationary_isInvariant (refreshEnvironment gamma))
      queueHypothesisScore queueHypothesisScore_mem_Icc
      knownKernelPotential
      (B := knownKernelPotentialSpan) (C := (3 / 2 : ℝ))
      (by norm_num [knownKernelPotentialSpan, selectedPotentialSpan])
      (by norm_num) knownKernelPotential_span
      queueHypothesis_overlap queueHypothesis_ratioBound_three_halves
      queueHypothesisPrior_isFullSupport queueRiskTiltWeight_isFullSupport
      queueRiskFailureBudget_pos knownKernelRiskTilt_pos
      knownKernelRiskTilt_lt_one with
    ⟨riskGood, hriskMass, hriskGood⟩
  rcases exists_persistenceHitConfidence_event
      (τ := Unit) gamma initial
      sharpStructuredPersistenceTiltWeight_isFullSupport
      sharpStructuredPersistenceFailureBudget_pos
      sharpStructuredPersistenceTilt_pos
      sharpStructuredPersistenceTilt_lt_one with
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
          sharpStructuredPersistenceBudget n path := by
      unfold sharpStructuredPersistenceBudget structuredCandidateTVBudget
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
              persistenceHitRadius sharpStructuredPersistenceTiltWeight
                sharpStructuredPersistenceTilt
                sharpStructuredPersistenceFailureBudget () n path := by
          exact add_le_add (le_refl _) hpersistence.le
    have hresidual : ∀ hypothesis state,
        |approximateTargetPolicyPoissonResidual
            (refreshEnvironment gamma)
            (queueHypothesisTargetPolicy hypothesis)
            (queueHypothesisStationary
              (refreshEnvironment gamma) hypothesis)
            (queueHypothesisScore hypothesis)
            (knownKernelPotential hypothesis) state| ≤
          sharpStructuredResidualEnvelope n path hypothesis := by
      intro hypothesis state
      classical
      by_cases hselected :
          hypothesis = queueThresholdNominalModelHypothesis
      · subst hypothesis
        have hpotential :
            knownKernelPotential queueThresholdNominalModelHypothesis =
              knownKernelSelectedPotential := by
          funext currentState
          simp [knownKernelPotential]
        rw [hpotential]
        simpa [sharpStructuredResidualEnvelope,
          sharpStructuredResidual] using
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
      · have hrow := targetPolicyRowRisk_mem_Icc
          (refreshEnvironment gamma)
          (queueHypothesisTargetPolicy hypothesis)
          (queueHypothesisScore_mem_Icc hypothesis) state
        have hrisk := sharpCatalogStationaryRisk_mem_Icc gamma hypothesis
        have hpotential :
            knownKernelPotential hypothesis = fun _state ↦ 0 := by
          funext currentState
          simp [knownKernelPotential, hselected]
        rw [hpotential]
        simp only [sharpStructuredResidualEnvelope, if_neg hselected,
          approximateTargetPolicyPoissonResidual,
          targetPolicyPoissonDrift]
        have hmean :
            targetPolicyPotentialMean (refreshEnvironment gamma)
              (queueHypothesisTargetPolicy hypothesis)
              (fun _state ↦ 0) state = 0 := by
          simp [targetPolicyPotentialMean]
        rw [hmean]
        simp only [sub_zero]
        rw [abs_le]
        constructor <;>
          linarith [hrow.1, hrow.2, hrisk.1, hrisk.2]
    have hnpos : 0 < n := by omega
    have hnegative :=
      neg_stationaryTargetPolicyPosteriorResidualAverage_le
        (refreshEnvironment gamma) queueHypothesisTargetPolicy
        (queueHypothesisStationary (refreshEnvironment gamma))
        queueHypothesisScore knownKernelPotential hresidual
        knownKernelSelectedPosterior_isPMF n hnpos path
    have hposteriorResidual :
        posteriorAverage knownKernelSelectedPosterior
            (sharpStructuredResidualEnvelope n path) =
          sharpStructuredResidual n path := by
      unfold knownKernelSelectedPosterior
      rw [pacBayesPosteriorAverage_dirac]
      simp [sharpStructuredResidualEnvelope]
    rw [hposteriorResidual] at hnegative
    unfold sharpStructuredOPEBoundary knownKernelOPEBoundary
    linarith

/-- Prospectively frozen fixed-initial, fixed-horizon sharp receipt event.
The theorem gives outer complement mass at most `1 / 20`; the deterministic
numerical endpoint is a separate post-registration receipt theorem. -/
theorem exists_controlledQueueSharpStructuredReceipt_event :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure
          (refreshEnvironment sharpStructuredTruePersistence)
          (markovBehaviorPolicyAsHistory behaviorPolicy)
          sharpStructuredInitial).real goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent,
        stationaryTargetPolicyPosteriorRisk
            (refreshEnvironment sharpStructuredTruePersistence)
            queueHypothesisTargetPolicy
            (queueHypothesisStationary
              (refreshEnvironment sharpStructuredTruePersistence))
            queueHypothesisScore knownKernelSelectedPosterior <
          sharpStructuredOPEBoundary sharpStructuredHorizon path := by
  rcases exists_controlledQueueSharpStructuredOPE_event
      sharpStructuredTruePersistence sharpStructuredInitial with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro path hpath
  exact hgood path hpath sharpStructuredHorizon
    (by norm_num [sharpStructuredHorizon])

end

end FormalSLT.Applications.ControlledQueue
