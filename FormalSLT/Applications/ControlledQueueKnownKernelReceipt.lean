/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueInvariantRisk
import FormalSLT.Applications.ControlledQueueKnownKernelReceiptRows21To23

/-!
# Known-kernel controlled-queue OPE receipt interface

This module specializes the approximate target-policy OPE event to the known
nominal controlled-queue kernel.  The catalog still contains all twelve fixed
target-policy/predictor pairs.  Only the queue-threshold/nominal-model atom
uses the supplied shifted depth-twelve potential; the other eleven atoms use
the zero potential and the conservative residual envelope one.

The selected potential table is a deterministic receipt input.  Its common
span and exact signed residual table are checked directly against the
generated nominal kernel, explicit invariant law, and exact stationary-risk
receipt.  This module does not yet identify that input table with the generic
finite-depth constructor up to its additive shift.  The probability event has
failure mass at most `1 / 40`, uses the singleton tilt `1 / 16`, and is
simultaneous over posterior PMFs and times `n >= 2`.

The final section deliberately exposes an aligned suffix-edge-histogram
predicate and derives the two numerical score summaries from it.  A separate
trace layer may prove that histogram predicate for the frozen trace.  Nothing
here proves that a named path belongs to the theorem-produced good event,
verifies trace bytes or hashes, or gives an unknown-kernel certificate.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge FormalSLT.StochasticDynamics
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

noncomputable section

/-- The fixed potential depth in the known-kernel receipt. -/
def knownKernelReceiptDepth : ℕ := receiptDepth

/-- Singleton empirical-Bernstein tilt used by the known-kernel receipt. -/
def knownKernelRiskTilt (_atom : Unit) : ℝ := 1 / 16

/-- Generated affine normalization `C * (1 + 2B)`. -/
def knownKernelNormalizedScale : ℝ := (selectedNormalizedScale : ℝ)

/-- The generated normalization agrees with ratio cap `3 / 2` and the
selected span. -/
theorem knownKernelNormalizedScale_eq :
    (3 / 2 : ℝ) * (1 + 2 * knownKernelPotentialSpan) =
      knownKernelNormalizedScale := by
  norm_num [knownKernelPotentialSpan, knownKernelNormalizedScale,
    selectedPotentialSpan, selectedNormalizedScale]

/-- Exact pointwise residual envelope of the selected potential. -/
def knownKernelSelectedResidualEnvelope : ℝ :=
  (selectedResidualEnvelope : ℝ)

private theorem generatedSelectedResidualTable_length :
    selectedResidualTable.length = 24 := rfl

private theorem generatedSelectedRowRiskTable_length :
    selectedRowRiskTable.length = 24 := rfl

/-- Exact signed residual table for the selected potential. -/
def knownKernelSelectedResidual (state : PhysicalState) : ℝ :=
  (selectedResidualTable.get
      (Fin.cast generatedSelectedResidualTable_length.symm state) : ℚ)

private def knownKernelSelectedRowRisk (state : PhysicalState) : ℝ :=
  (selectedRowRiskTable.get
      (Fin.cast generatedSelectedRowRiskTable_length.symm state) : ℚ)

/-- Twelve-atom potential catalog: the selected atom receives the supplied
potential table and every other atom receives zero. -/
def knownKernelPotential
    (hypothesis : QueueHypothesis) (state : PhysicalState) : ℝ :=
  if hypothesis = queueThresholdNominalModelHypothesis then
    knownKernelSelectedPotential state
  else 0

/-- Twelve-atom residual catalog: the selected atom receives its exact small
envelope and every zero-potential atom receives the unit envelope. -/
def knownKernelResidualEnvelope (hypothesis : QueueHypothesis) : ℝ :=
  if hypothesis = queueThresholdNominalModelHypothesis then
    knownKernelSelectedResidualEnvelope
  else 1

/-- Point posterior selecting the queue-threshold/nominal-model atom. -/
def knownKernelSelectedPosterior : QueueHypothesis → ℝ :=
  diracPosterior queueThresholdNominalModelHypothesis

/-- Specialized known-kernel OPE boundary. -/
def knownKernelOPEBoundary
    (posterior : QueueHypothesis → ℝ) (n : ℕ)
    (path : ℕ → Observation) : ℝ :=
  stationaryTargetPolicyOPEBoundary
    queueHypothesisPrior queueRiskTiltWeight knownKernelRiskTilt
    (markovBehaviorPolicyAsHistory behaviorPolicy)
    queueHypothesisTargetPolicy queueHypothesisScore knownKernelPotential
    knownKernelPotentialSpan (3 / 2 : ℝ) posterior
    queueRiskFailureBudget () n path

/-- The selected potential lies between zero and the declared common span. -/
theorem knownKernelSelectedPotential_mem_Icc (state : PhysicalState) :
    knownKernelSelectedPotential state ∈
      Set.Icc (0 : ℝ) knownKernelPotentialSpan := by
  fin_cases state <;>
    norm_num [knownKernelSelectedPotential, knownKernelPotentialSpan,
      selectedPotentialTable, selectedPotentialSpan]

/-- The twelve-atom potential catalog obeys the common span bound. -/
theorem knownKernelPotential_span
    (hypothesis : QueueHypothesis) (state nextState : PhysicalState) :
    |knownKernelPotential hypothesis nextState -
        knownKernelPotential hypothesis state| ≤ knownKernelPotentialSpan := by
  classical
  by_cases hselected : hypothesis = queueThresholdNominalModelHypothesis
  · subst hypothesis
    change |knownKernelSelectedPotential nextState -
      knownKernelSelectedPotential state| ≤ knownKernelPotentialSpan
    rcases knownKernelSelectedPotential_mem_Icc state with
      ⟨hstateLower, hstateUpper⟩
    rcases knownKernelSelectedPotential_mem_Icc nextState with
      ⟨hnextLower, hnextUpper⟩
    rw [abs_le]
    constructor <;> linarith
  · simp [knownKernelPotential, hselected]
    norm_num [knownKernelPotentialSpan, selectedPotentialSpan]

/-- Every catalog stationary risk under the nominal environment is in the
unit interval. -/
theorem knownKernelCatalogStationaryRisk_mem_Icc
    (hypothesis : QueueHypothesis) :
    stationaryTargetPolicyRisk nominalCandidateEnvironment
        (queueHypothesisTargetPolicy hypothesis)
        (queueHypothesisStationary nominalCandidateEnvironment hypothesis)
        (queueHypothesisScore hypothesis) ∈ Set.Icc (0 : ℝ) 1 := by
  have hrow : ∀ state : PhysicalState,
      targetPolicyRowRisk nominalCandidateEnvironment
          (queueHypothesisTargetPolicy hypothesis)
          (queueHypothesisScore hypothesis) state ∈ Set.Icc (0 : ℝ) 1 :=
    fun state ↦ targetPolicyRowRisk_mem_Icc
      nominalCandidateEnvironment (queueHypothesisTargetPolicy hypothesis)
      (queueHypothesisScore_mem_Icc hypothesis) state
  unfold stationaryTargetPolicyRisk
  constructor
  · exact Finset.sum_nonneg fun state _stateMem ↦
      mul_nonneg ENNReal.toReal_nonneg (hrow state).1
  · calc
      ∑ state : PhysicalState,
          ((queueHypothesisStationary nominalCandidateEnvironment hypothesis)
              state).toReal *
            targetPolicyRowRisk nominalCandidateEnvironment
              (queueHypothesisTargetPolicy hypothesis)
              (queueHypothesisScore hypothesis) state ≤
          ∑ state : PhysicalState,
            ((queueHypothesisStationary nominalCandidateEnvironment hypothesis)
                state).toReal * 1 :=
        Finset.sum_le_sum fun state _stateMem ↦
          mul_le_mul_of_nonneg_left (hrow state).2 ENNReal.toReal_nonneg
      _ = 1 := by
        rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]

private theorem nominalCandidateEnvironment_apply_toReal_refreshMixture
    (state : PhysicalState) (action : Action) (nextState : PhysicalState) :
    (nominalCandidateEnvironment state action nextState).toReal =
      (1 / 96 : ℝ) +
        if nextState = candidateKernelStepStateAction state action then
          3 / 4 else 0 := by
  rw [nominalCandidateEnvironment, candidateEnvironment_apply_toReal,
    candidateKernelTableMass_eq_refreshMixture,
    candidateKernelStep_stateActionRowEquiv]
  by_cases hstep : nextState = candidateKernelStepStateAction state action <;>
    simp [hstep, nominalCandidateIndex, candidateGammaRat,
      ControlledQueueData.candidateGammaTable, div_eq_mul_inv] <;>
    norm_num

/-- Under the nominal refresh mixture, a target-policy potential mean is one
common uniform term plus the target-policy-weighted persistence term. -/
theorem nominalTargetPolicyPotentialMean_eq_refreshMixture
    (target : TargetPolicyIndex) (potential : PhysicalState → ℝ)
    (state : PhysicalState) :
    targetPolicyPotentialMean nominalCandidateEnvironment
        (targetPolicy target) potential state =
      (1 / 96 : ℝ) * (∑ nextState : PhysicalState, potential nextState) +
        (3 / 4 : ℝ) *
          ∑ action : Action,
            (targetPolicy target state action).toReal *
              potential (candidateKernelStepStateAction state action) := by
  have hinner : ∀ action : Action,
      (∑ nextState : PhysicalState,
          (nominalCandidateEnvironment state action nextState).toReal *
            potential nextState) =
        (1 / 96 : ℝ) * (∑ nextState : PhysicalState, potential nextState) +
          (3 / 4 : ℝ) *
            potential (candidateKernelStepStateAction state action) := by
    intro action
    simp_rw [nominalCandidateEnvironment_apply_toReal_refreshMixture,
      add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hpolicyMass :
      ∑ action : Action, (targetPolicy target state action).toReal = 1 :=
    finitePMF_real_mass_sum (targetPolicy target state)
  unfold targetPolicyPotentialMean
  simp_rw [hinner]
  calc
    (∑ action : Action,
        (targetPolicy target state action).toReal *
          ((1 / 96 : ℝ) *
              (∑ nextState : PhysicalState, potential nextState) +
            (3 / 4 : ℝ) *
              potential (candidateKernelStepStateAction state action))) =
      ∑ action : Action,
        ((targetPolicy target state action).toReal *
            ((1 / 96 : ℝ) *
              (∑ nextState : PhysicalState, potential nextState)) +
          (3 / 4 : ℝ) *
            ((targetPolicy target state action).toReal *
              potential (candidateKernelStepStateAction state action))) := by
        apply Finset.sum_congr rfl
        intro action _haction
        ring
    _ = (∑ action : Action,
          (targetPolicy target state action).toReal) *
            ((1 / 96 : ℝ) *
              (∑ nextState : PhysicalState, potential nextState)) +
          (3 / 4 : ℝ) *
            ∑ action : Action,
              (targetPolicy target state action).toReal *
                potential (candidateKernelStepStateAction state action) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = (1 / 96 : ℝ) *
            (∑ nextState : PhysicalState, potential nextState) +
          (3 / 4 : ℝ) *
            ∑ action : Action,
              (targetPolicy target state action).toReal *
                potential (candidateKernelStepStateAction state action) := by
      rw [hpolicyMass, one_mul]

private theorem knownKernelSelectedPotential_sum_eq :
    (∑ state : PhysicalState, knownKernelSelectedPotential state) =
      1162349910795555 / 2251799813685248 := by
  norm_num [knownKernelSelectedPotential, selectedPotentialTable,
    Fin.sum_univ_succ]

private theorem queueThresholdNominalModelRowRisk_eq_generated
    (state : PhysicalState) :
    (queueThresholdNominalModelRowRisk state : ℝ) =
      knownKernelSelectedRowRisk state := by
  unfold knownKernelSelectedRowRisk
  apply congrArg (fun mass : ℚ ↦ (mass : ℝ))
  fin_cases state <;> rfl

set_option maxHeartbeats 1000000 in
/-- Direct finite-state check of the selected potential's exact signed
residual table. -/
theorem knownKernelSelectedPotential_residual_eq
    (state : PhysicalState) :
    approximateTargetPolicyPoissonResidual
        nominalCandidateEnvironment
        (queueHypothesisTargetPolicy queueThresholdNominalModelHypothesis)
        (queueHypothesisStationary nominalCandidateEnvironment
          queueThresholdNominalModelHypothesis)
        (queueHypothesisScore queueThresholdNominalModelHypothesis)
        knownKernelSelectedPotential state =
      knownKernelSelectedResidual state := by
  unfold approximateTargetPolicyPoissonResidual targetPolicyPoissonDrift
  rw [queueThreshold_nominalModelOverload_catalogStationaryRisk]
  change
    targetPolicyRowRisk nominalCandidateEnvironment
          (targetPolicy queueThresholdTargetIndex)
          (fixedBrierScore nominalModelOverloadPredictorIndex) state +
        targetPolicyPotentialMean nominalCandidateEnvironment
          (targetPolicy queueThresholdTargetIndex)
        knownKernelSelectedPotential state -
        knownKernelSelectedPotential state -
        4338268437 / 67816493056 =
      knownKernelSelectedResidual state
  rw [queueThreshold_nominalModelOverload_rowRisk,
    nominalTargetPolicyPotentialMean_eq_refreshMixture,
    knownKernelSelectedPotential_sum_eq,
    queueThresholdNominalModelRowRisk_eq_generated]
  fin_cases state <;>
    norm_num [knownKernelSelectedPotential, knownKernelSelectedResidual,
      knownKernelSelectedRowRisk, selectedPotentialTable,
      selectedResidualTable, selectedRowRiskTable,
      queueThresholdTargetIndex, targetPolicy_apply_toReal,
      targetPolicyTableIndex, policyTableMass,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
      Fin.sum_univ_succ]

/-- The exact signed residual table is controlled by the selected envelope. -/
theorem knownKernelSelectedPotential_residual_le
    (state : PhysicalState) :
    |approximateTargetPolicyPoissonResidual
        nominalCandidateEnvironment
        (queueHypothesisTargetPolicy queueThresholdNominalModelHypothesis)
        (queueHypothesisStationary nominalCandidateEnvironment
          queueThresholdNominalModelHypothesis)
        (queueHypothesisScore queueThresholdNominalModelHypothesis)
        knownKernelSelectedPotential state| ≤
      knownKernelSelectedResidualEnvelope := by
  rw [knownKernelSelectedPotential_residual_eq]
  fin_cases state <;>
    norm_num [knownKernelSelectedResidual,
      knownKernelSelectedResidualEnvelope, selectedResidualTable,
      selectedResidualEnvelope]

/-- The selected exact envelope and the eleven conservative unit envelopes
control every atom in the approximate-OPE catalog. -/
theorem knownKernelPotential_residual_le
    (hypothesis : QueueHypothesis) (state : PhysicalState) :
    |approximateTargetPolicyPoissonResidual
        nominalCandidateEnvironment
        (queueHypothesisTargetPolicy hypothesis)
        (queueHypothesisStationary nominalCandidateEnvironment hypothesis)
        (queueHypothesisScore hypothesis)
        (knownKernelPotential hypothesis) state| ≤
      knownKernelResidualEnvelope hypothesis := by
  classical
  by_cases hselected : hypothesis = queueThresholdNominalModelHypothesis
  · subst hypothesis
    have hpotential :
        knownKernelPotential queueThresholdNominalModelHypothesis =
          knownKernelSelectedPotential := by
      funext currentState
      simp [knownKernelPotential]
    have henvelope :
        knownKernelResidualEnvelope queueThresholdNominalModelHypothesis =
          knownKernelSelectedResidualEnvelope := by
      simp [knownKernelResidualEnvelope]
    rw [hpotential, henvelope]
    exact knownKernelSelectedPotential_residual_le state
  · have hrow := targetPolicyRowRisk_mem_Icc
      nominalCandidateEnvironment (queueHypothesisTargetPolicy hypothesis)
      (queueHypothesisScore_mem_Icc hypothesis) state
    have hrisk := knownKernelCatalogStationaryRisk_mem_Icc hypothesis
    have hpotential : knownKernelPotential hypothesis = fun _state ↦ 0 := by
      funext currentState
      simp [knownKernelPotential, hselected]
    rw [hpotential]
    simp only [knownKernelResidualEnvelope, if_neg hselected]
    simp only [approximateTargetPolicyPoissonResidual,
      targetPolicyPoissonDrift]
    have hmean :
        targetPolicyPotentialMean nominalCandidateEnvironment
          (queueHypothesisTargetPolicy hypothesis) (fun _state ↦ 0) state = 0 := by
      simp [targetPolicyPotentialMean]
    rw [hmean]
    simp only [sub_zero]
    rw [abs_le]
    constructor <;> linarith [hrow.1, hrow.2, hrisk.1, hrisk.2]

/-- The selected point posterior is a PMF. -/
theorem knownKernelSelectedPosterior_isPMF :
    IsPMF knownKernelSelectedPosterior := by
  exact diracPosterior_isPMF queueThresholdNominalModelHypothesis

/-- The selected point posterior has the exact stationary risk of its single
queue-threshold/nominal-model atom. -/
theorem knownKernelSelectedPosteriorRisk_eq :
    stationaryTargetPolicyPosteriorRisk
        nominalCandidateEnvironment queueHypothesisTargetPolicy
        (queueHypothesisStationary nominalCandidateEnvironment)
        queueHypothesisScore knownKernelSelectedPosterior =
      4338268437 / 67816493056 := by
  unfold stationaryTargetPolicyPosteriorRisk knownKernelSelectedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  exact queueThreshold_nominalModelOverload_catalogStationaryRisk

/-- The singleton receipt tilt is positive. -/
theorem knownKernelRiskTilt_pos (atom : Unit) :
    0 < knownKernelRiskTilt atom := by
  cases atom
  norm_num [knownKernelRiskTilt]

/-- The singleton receipt tilt is below one. -/
theorem knownKernelRiskTilt_lt_one (atom : Unit) :
    knownKernelRiskTilt atom < 1 := by
  cases atom
  norm_num [knownKernelRiskTilt]

/-- Generated fixed initial observation for the receipt law: action index one
and physical-state index one. -/
def knownKernelReceiptInitial : Observation :=
  (⟨receiptInitialActionIndex, by norm_num [receiptInitialActionIndex]⟩,
    ⟨receiptInitialStateIndex, by norm_num [receiptInitialStateIndex]⟩)

/-- The generated receipt initial observation is exactly `(action = 1,
state = 1)`. -/
theorem knownKernelReceiptInitial_eq :
    knownKernelReceiptInitial = ((1 : Action), (1 : PhysicalState)) := by
  norm_num [knownKernelReceiptInitial, receiptInitialActionIndex,
    receiptInitialStateIndex]

/-- One `39 / 40` known-kernel event controls all twelve fixed hypotheses,
all posterior PMFs, and every time `n >= 2`. -/
theorem exists_controlledQueueKnownKernelOPE_event
    (initial : Observation) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure nominalCandidateEnvironment
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 40 ∧
      ∀ path ∈ goodEvent,
        ∀ posterior : QueueHypothesis → ℝ, IsPMF posterior →
          ∀ n : ℕ, 2 ≤ n →
            stationaryTargetPolicyPosteriorRisk
                nominalCandidateEnvironment queueHypothesisTargetPolicy
                (queueHypothesisStationary nominalCandidateEnvironment)
                queueHypothesisScore posterior <
              knownKernelOPEBoundary posterior n path +
                posteriorAverage posterior knownKernelResidualEnvelope := by
  rcases exists_stationaryApproximateTargetPolicyOPE_event
      (P := nominalCandidateEnvironment)
      (markovBehaviorPolicyAsHistory behaviorPolicy) initial
      queueHypothesisTargetPolicy
      (queueHypothesisStationary nominalCandidateEnvironment)
      (queueHypothesisStationary_isInvariant nominalCandidateEnvironment)
      queueHypothesisScore queueHypothesisScore_mem_Icc
      knownKernelPotential
      (B := knownKernelPotentialSpan) (C := (3 / 2 : ℝ))
      (by norm_num [knownKernelPotentialSpan, selectedPotentialSpan]) (by norm_num)
      knownKernelPotential_span knownKernelPotential_residual_le
      queueHypothesis_overlap queueHypothesis_ratioBound_three_halves
      queueHypothesisPrior_isFullSupport queueRiskTiltWeight_isFullSupport
      queueRiskFailureBudget_pos knownKernelRiskTilt_pos
      knownKernelRiskTilt_lt_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · simpa [queueRiskFailureBudget] using hmass
  · intro path hpath posterior hposterior n hn
    simpa only [knownKernelOPEBoundary] using
      hgood path hpath () posterior hposterior n hn

/-- Fixed-initial form of the known-kernel event for the generated receipt
law, whose initial observation is `(action = 1, state = 1)`. -/
theorem exists_controlledQueueKnownKernelReceiptOPE_event :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure nominalCandidateEnvironment
          (markovBehaviorPolicyAsHistory behaviorPolicy)
          knownKernelReceiptInitial).real goodEventᶜ ≤ 1 / 40 ∧
      ∀ path ∈ goodEvent,
        ∀ posterior : QueueHypothesis → ℝ, IsPMF posterior →
          ∀ n : ℕ, 2 ≤ n →
            stationaryTargetPolicyPosteriorRisk
                nominalCandidateEnvironment queueHypothesisTargetPolicy
                (queueHypothesisStationary nominalCandidateEnvironment)
                queueHypothesisScore posterior <
              knownKernelOPEBoundary posterior n path +
                posteriorAverage posterior knownKernelResidualEnvelope := by
  exact exists_controlledQueueKnownKernelOPE_event knownKernelReceiptInitial

/-! ## Deterministic selected-path numerical interface -/

/-- Exact selected centered sum of squares implied by the two summary sums. -/
def knownKernelReceiptBesselQ : ℝ := (observedScoreBesselQ : ℝ)

/-- Exact affine first-branch hybrid-Bessel penalty at the supplied summary. -/
def knownKernelReceiptAffinePenalty : ℝ :=
  (observedHybridPenaltyUpper : ℝ)

/-- Rational upper bound obtained from log-cost `9` and cumulant bound
`1 / 240`. -/
def knownKernelReceiptD9Bound : ℝ :=
  (certifiedKnownKernelUpperBound : ℝ)

private theorem generatedSuffixEdgeHistogram_rowCertificate
    (state : PhysicalState) :
    KnownKernelReceiptInternal.RowCertificate state := by
  fin_cases state
  · exact certificates00To02.1
  · exact certificates00To02.2.1
  · exact certificates00To02.2.2
  · exact certificates03To05.1
  · exact certificates03To05.2.1
  · exact certificates03To05.2.2
  · exact certificates06To08.1
  · exact certificates06To08.2.1
  · exact certificates06To08.2.2
  · exact certificates09To11.1
  · exact certificates09To11.2.1
  · exact certificates09To11.2.2
  · exact certificates12To14.1
  · exact certificates12To14.2.1
  · exact certificates12To14.2.2
  · exact certificates15To17.1
  · exact certificates15To17.2.1
  · exact certificates15To17.2.2
  · exact certificates18To20.1
  · exact certificates18To20.2.1
  · exact certificates18To20.2.2
  · exact certificates21To23.1
  · exact certificates21To23.2.1
  · exact certificates21To23.2.2

private theorem generatedSuffixEdgeHistogram_selectedScoreRow_eq
    (state : PhysicalState) (action : Action) :
    (∑ nextState : PhysicalState,
      (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
        knownKernelSelectedTransitionScore state action nextState) =
      (selectedScoreRowSum state action : ℝ) :=
  (generatedSuffixEdgeHistogram_rowCertificate state).score action

private theorem generatedSuffixEdgeHistogram_selectedSquaredScoreRow_eq
    (state : PhysicalState) (action : Action) :
    (∑ nextState : PhysicalState,
      (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
        (knownKernelSelectedTransitionScore state action nextState) ^ 2) =
      (selectedScoreSquareRowSum state action : ℝ) :=
  (generatedSuffixEdgeHistogram_rowCertificate state).square action

set_option maxHeartbeats 1000000 in
private theorem generatedSuffixEdgeHistogram_selectedScoreSum_eq :
    (∑ state : PhysicalState, ∑ action : Action,
      ∑ nextState : PhysicalState,
        (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
          knownKernelSelectedTransitionScore state action nextState) =
      knownKernelReceiptScoreSum := by
  simp_rw [generatedSuffixEdgeHistogram_selectedScoreRow_eq]
  norm_num [selectedScoreRowSum, knownKernelReceiptScoreSum,
    observedScoreSum, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
private theorem generatedSuffixEdgeHistogram_selectedSquaredScoreSum_eq :
    (∑ state : PhysicalState, ∑ action : Action,
      ∑ nextState : PhysicalState,
        (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
          (knownKernelSelectedTransitionScore state action nextState) ^ 2) =
      knownKernelReceiptSquaredScoreSum := by
  simp_rw [generatedSuffixEdgeHistogram_selectedSquaredScoreRow_eq]
  norm_num [selectedScoreSquareRowSum,
    knownKernelReceiptSquaredScoreSum, observedScoreSquareSum,
    Fin.sum_univ_succ]

/-- The aligned generated suffix histogram implies both exact numerical score
summaries. -/
theorem knownKernelReceiptPathSummary_of_suffixEdgeHistogram
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path) :
    KnownKernelReceiptPathSummary path := by
  change (∀ f : PhysicalState → Action → PhysicalState → ℝ,
    (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      f (path k).2 (path (k + 1)).1 (path (k + 1)).2) =
    ∑ state : PhysicalState, ∑ action : Action,
      ∑ nextState : PhysicalState,
        (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
          f state action nextState) at hhist
  constructor
  · calc
      (∑ k ∈ Finset.range knownKernelReceiptHorizon,
          knownKernelSelectedObservedScore path k) =
          ∑ k ∈ Finset.range knownKernelReceiptHorizon,
            knownKernelSelectedTransitionScore
              (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact knownKernelSelectedObservedScore_eq_transitionScore path k
      _ = ∑ state : PhysicalState, ∑ action : Action,
          ∑ nextState : PhysicalState,
            (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
              knownKernelSelectedTransitionScore state action nextState :=
        hhist knownKernelSelectedTransitionScore
      _ = knownKernelReceiptScoreSum :=
        generatedSuffixEdgeHistogram_selectedScoreSum_eq
  · calc
      (∑ k ∈ Finset.range knownKernelReceiptHorizon,
          (knownKernelSelectedObservedScore path k) ^ 2) =
          ∑ k ∈ Finset.range knownKernelReceiptHorizon,
            (knownKernelSelectedTransitionScore
              (path k).2 (path (k + 1)).1 (path (k + 1)).2) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [knownKernelSelectedObservedScore_eq_transitionScore]
      _ = ∑ state : PhysicalState, ∑ action : Action,
          ∑ nextState : PhysicalState,
            (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
              (knownKernelSelectedTransitionScore state action nextState) ^ 2 :=
        hhist (fun state action nextState ↦
          (knownKernelSelectedTransitionScore state action nextState) ^ 2)
      _ = knownKernelReceiptSquaredScoreSum :=
        generatedSuffixEdgeHistogram_selectedSquaredScoreSum_eq

private theorem knownKernel_forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardBesselQ v n =
      (∑ k ∈ Finset.range n, (v k) ^ 2) -
        (∑ k ∈ Finset.range n, v k) ^ 2 / (n : ℝ) := by
  let m : ℝ := forwardPrefixMean v n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdecomp :
      (∑ k ∈ Finset.range n, (v k) ^ 2) =
        forwardBesselQ v n + (n : ℝ) * m ^ 2 := by
    have h :=
      FormalSLT.Statistics.ClassicalEstimation.sum_sq_sub_eq_sum_sq_sub_mean_add_card
        hn (fun i : Fin n ↦ v i) 0
    have hsum (f : ℕ → ℝ) :
        (∑ i : Fin n, f i) = ∑ i ∈ Finset.range n, f i :=
      Fin.sum_univ_eq_sum_range f n
    rw [hsum (fun i ↦ (v i - 0) ^ 2),
      hsum (fun i ↦ (v i - FormalSLT.Statistics.sampleMean
        (fun j : Fin n ↦ v j)) ^ 2)] at h
    rw [← forwardPrefixMean_eq_sampleMean v n] at h
    simpa [m, forwardBesselQ] using h
  have hsum : (∑ k ∈ Finset.range n, v k) = (n : ℝ) * m := by
    unfold m forwardPrefixMean
    field_simp [hn0]
  rw [hdecomp, hsum]
  field_simp [hn0]
  ring

/-- The two deterministic score sums imply the displayed exact Bessel
statistic. -/
theorem knownKernelReceipt_besselQ_eq
    (path : ℕ → Observation) (hsummary : KnownKernelReceiptPathSummary path) :
    forwardBesselQ (knownKernelSelectedObservedScore path)
        knownKernelReceiptHorizon = knownKernelReceiptBesselQ := by
  rw [knownKernel_forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v := knownKernelSelectedObservedScore path)
    (n := knownKernelReceiptHorizon)
    (by norm_num [knownKernelReceiptHorizon, receiptHorizon])]
  rw [hsummary.1, hsummary.2]
  norm_num [knownKernelReceiptHorizon, knownKernelReceiptScoreSum,
    knownKernelReceiptSquaredScoreSum, knownKernelReceiptBesselQ,
    receiptHorizon, observedScoreSum, observedScoreSquareSum,
    observedScoreBesselQ]

/-- The selected empirical posterior score is the supplied sum divided by
the supplied horizon. -/
theorem knownKernelReceipt_selectedEmpiricalScore_eq
    (path : ℕ → Observation) (hsummary : KnownKernelReceiptPathSummary path) :
    stationaryTargetPolicyPosteriorEmpiricalScore
        (markovBehaviorPolicyAsHistory behaviorPolicy)
        queueHypothesisTargetPolicy queueHypothesisScore knownKernelPotential
        knownKernelPotentialSpan (3 / 2 : ℝ) knownKernelSelectedPosterior
        knownKernelReceiptHorizon path =
      knownKernelReceiptScoreSum / knownKernelReceiptHorizon := by
  unfold stationaryTargetPolicyPosteriorEmpiricalScore
    knownKernelSelectedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  change forwardPrefixMean (knownKernelSelectedObservedScore path)
      knownKernelReceiptHorizon = _
  unfold forwardPrefixMean
  rw [hsummary.1]

/-- The selected posterior hybrid penalty is at most the exact affine
first-branch value. -/
theorem knownKernelReceipt_selectedPenalty_le
    (path : ℕ → Observation) (hsummary : KnownKernelReceiptPathSummary path) :
    forwardPosteriorHybridBesselPenalty knownKernelSelectedPosterior
        (fun hypothesis k path ↦
          stationaryTargetPolicyObservedScore
            (markovBehaviorPolicyAsHistory behaviorPolicy)
            (queueHypothesisTargetPolicy hypothesis)
            (queueHypothesisScore hypothesis)
            (knownKernelPotential hypothesis) knownKernelPotentialSpan
            (3 / 2 : ℝ) k path)
        knownKernelReceiptHorizon path ≤
      knownKernelReceiptAffinePenalty := by
  unfold forwardPosteriorHybridBesselPenalty knownKernelSelectedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  change forwardHybridBesselPenalty (knownKernelSelectedObservedScore path)
      knownKernelReceiptHorizon ≤ knownKernelReceiptAffinePenalty
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ (knownKernelSelectedObservedScore path)
            knownKernelReceiptHorizon)
        ((knownKernelReceiptHorizon : ℝ) /
            ((knownKernelReceiptHorizon : ℝ) - 1) *
              forwardBesselQ (knownKernelSelectedObservedScore path)
                knownKernelReceiptHorizon +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (knownKernelReceiptHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ (knownKernelSelectedObservedScore path)
          knownKernelReceiptHorizon := min_le_left _ _
    _ = knownKernelReceiptAffinePenalty := by
      rw [knownKernelReceipt_besselQ_eq path hsummary]
      norm_num [knownKernelReceiptAffinePenalty, knownKernelReceiptBesselQ,
        observedHybridPenaltyUpper, observedScoreBesselQ]

private theorem knownKernel_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

/-- The selected point posterior and `1 / 40` event cost at most nine nats
under the uniform twelve-atom prior. -/
theorem knownKernelReceipt_selectedLogCost_le_nine :
    klDiv knownKernelSelectedPosterior queueHypothesisPrior +
        Real.log (1 / (queueRiskFailureBudget * queueRiskTiltWeight ())) ≤ 9 := by
  rw [show queueHypothesisPrior = finiteUniformRealPMF QueueHypothesis by rfl]
  unfold knownKernelSelectedPosterior
  rw [klDiv_dirac_finiteUniformRealPMF]
  rw [queueHypothesis_card]
  norm_num [queueRiskFailureBudget, queueRiskTiltWeight, finiteUniformRealPMF]
  rw [← Real.log_mul (by norm_num : (12 : ℝ) ≠ 0)
    (by norm_num : (40 : ℝ) ≠ 0)]
  calc
    Real.log ((12 : ℝ) * 40) ≤ Real.log 512 :=
      Real.log_le_log (by norm_num) (by norm_num)
    _ = Real.log ((2 : ℝ) ^ (9 : ℕ)) := by norm_num
    _ = 9 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 9 := by linarith [knownKernel_log_two_le_one]

/-- At tilt `1 / 16`, the empirical-Bernstein cumulant is at most
`1 / 240`. -/
theorem knownKernelReceipt_psi_one_sixteen_le_one_twoForty :
    forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) ≤ 1 / 240 := by
  have hlog : Real.log ((16 : ℝ) / 15) ≤ 1 / 15 := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 16 / 15 by norm_num)
    norm_num at h ⊢
    exact h
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 16 : ℝ)) = 15 / 16 by norm_num, ← Real.log_inv]
  norm_num only [inv_div]
  linarith

/-- Unaligned arithmetic lemma: the two scalar score summaries make the
selected boundary plus exact residual no larger than the displayed rational
`d9` bound.  The public aligned endpoint below obtains these summaries from
the suffix histogram. -/
theorem knownKernelReceipt_selectedBoundary_add_residual_le_d9
    (path : ℕ → Observation) (hsummary : KnownKernelReceiptPathSummary path) :
    knownKernelOPEBoundary knownKernelSelectedPosterior
        knownKernelReceiptHorizon path +
        knownKernelSelectedResidualEnvelope ≤ knownKernelReceiptD9Bound := by
  have hpen := knownKernelReceipt_selectedPenalty_le path hsummary
  have hpsi := knownKernelReceipt_psi_one_sixteen_le_one_twoForty
  have hpsi0 : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hproduct :
      forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) *
          forwardPosteriorHybridBesselPenalty knownKernelSelectedPosterior
            (fun hypothesis k path ↦
              stationaryTargetPolicyObservedScore
                (markovBehaviorPolicyAsHistory behaviorPolicy)
                (queueHypothesisTargetPolicy hypothesis)
                (queueHypothesisScore hypothesis)
                (knownKernelPotential hypothesis) knownKernelPotentialSpan
                (3 / 2 : ℝ) k path)
            knownKernelReceiptHorizon path ≤
        (1 / 240 : ℝ) * knownKernelReceiptAffinePenalty := by
    calc
      _ ≤ forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) *
          knownKernelReceiptAffinePenalty :=
        mul_le_mul_of_nonneg_left hpen hpsi0
      _ ≤ (1 / 240 : ℝ) * knownKernelReceiptAffinePenalty :=
        mul_le_mul_of_nonneg_right hpsi
          (by norm_num [knownKernelReceiptAffinePenalty,
            observedHybridPenaltyUpper])
  have hcost := knownKernelReceipt_selectedLogCost_le_nine
  have hemp := knownKernelReceipt_selectedEmpiricalScore_eq path hsummary
  unfold knownKernelOPEBoundary stationaryTargetPolicyOPEBoundary
    forwardPredictableMeanBesselPACBayesBoundary
  rw [hemp]
  norm_num [knownKernelRiskTilt, knownKernelReceiptHorizon,
    knownKernelPotentialSpan, knownKernelSelectedResidualEnvelope,
    knownKernelReceiptScoreSum, knownKernelReceiptAffinePenalty,
    knownKernelReceiptD9Bound, receiptHorizon, selectedPotentialSpan,
    selectedResidualEnvelope, observedScoreSum,
    observedHybridPenaltyUpper, certifiedKnownKernelUpperBound]
    at hproduct hcost ⊢
  nlinarith

/-- The generated aligned suffix histogram makes the selected boundary plus
exact residual no larger than the displayed rational `d9` bound. -/
theorem knownKernelReceipt_selectedBoundary_add_residual_le_d9_of_suffixEdgeHistogram
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path) :
    knownKernelOPEBoundary knownKernelSelectedPosterior
        knownKernelReceiptHorizon path +
        knownKernelSelectedResidualEnvelope ≤ knownKernelReceiptD9Bound := by
  exact knownKernelReceipt_selectedBoundary_add_residual_le_d9 path
    (knownKernelReceiptPathSummary_of_suffixEdgeHistogram path hhist)

/-- The rational `d9` endpoint is strictly below seven hundredths. -/
theorem knownKernelReceipt_d9_lt_seven_hundredths :
    knownKernelReceiptD9Bound < 7 / 100 := by
  norm_num [knownKernelReceiptD9Bound, certifiedKnownKernelUpperBound]

/-- Aligned deterministic composition interface.  A path with the generated
suffix edge histogram receives the `< 7 / 100` selected-risk conclusion
whenever the selected specialization of the theorem-produced event inequality
is available.  This theorem does not assert either premise for a named trace. -/
theorem knownKernelReceipt_selectedRisk_lt_seven_hundredths
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path)
    (hevent :
      stationaryTargetPolicyPosteriorRisk
          nominalCandidateEnvironment queueHypothesisTargetPolicy
          (queueHypothesisStationary nominalCandidateEnvironment)
          queueHypothesisScore knownKernelSelectedPosterior <
        knownKernelOPEBoundary knownKernelSelectedPosterior
            knownKernelReceiptHorizon path +
          posteriorAverage knownKernelSelectedPosterior
            knownKernelResidualEnvelope) :
    stationaryTargetPolicyPosteriorRisk
        nominalCandidateEnvironment queueHypothesisTargetPolicy
        (queueHypothesisStationary nominalCandidateEnvironment)
        queueHypothesisScore knownKernelSelectedPosterior < 7 / 100 := by
  have hresidualAverage :
      posteriorAverage knownKernelSelectedPosterior
          knownKernelResidualEnvelope = knownKernelSelectedResidualEnvelope := by
    unfold knownKernelSelectedPosterior
    rw [pacBayesPosteriorAverage_dirac]
    simp [knownKernelResidualEnvelope]
  rw [hresidualAverage] at hevent
  exact hevent.trans_le
    ((knownKernelReceipt_selectedBoundary_add_residual_le_d9_of_suffixEdgeHistogram
        path hhist).trans knownKernelReceipt_d9_lt_seven_hundredths.le)

end

end FormalSLT.Applications.ControlledQueue
