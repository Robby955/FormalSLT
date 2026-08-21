/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelSelection

/-!
# Explicit controlled-queue invariant law and stationary risk

This module gives an executable invariant-law receipt for the nominal queue
environment under the generated queue-threshold target policy.  It then
evaluates the exact stationary Brier risk of the generated nominal-model
overload predictor.

The law is an explicit twenty-four-entry rational PMF.  Its invariance is
checked against the generated candidate-kernel and policy tables, rather than
inferred from finite-state existence.  This closes one concrete stationary
target in the twelve-atom queue OPE catalog.  It does not bind the frozen
trace, prove good-event membership, or evaluate a confidence boundary.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

@[simp]
private theorem candidateGammaRat_one_eq_three_fourths :
    candidateGammaRat (1 : CandidateIndex) = (3 / 4 : ℚ) := by
  norm_num [candidateGammaRat,
    ControlledQueueData.candidateGammaTable]

@[simp]
private theorem nominalCandidateGammaRat_eq_three_fourths :
    candidateGammaRat nominalCandidateIndex = (3 / 4 : ℚ) := by
  simp [nominalCandidateIndex]

private def queueThresholdStationaryNumerators : List ℕ :=
  [13983799152411887344,
   66647387414985104446,
   13983799152411887344,
   13983799152411887344,
   122105167865955318754,
   173427188348420542663,
   169002077514428725792,
   95354521254951135568,
   77120201260760085028,
   69641067262278790144,
   50663914146336980944,
   65478159470343226516,
   75017994253346540032,
   40881615307763177584,
   43027076264651711596,
   40203095238084653056,
   38005287541394183920,
   32269723175201012956,
   34417308085707409408,
   19839880193382606448,
   25569663711902812684,
   31232432218510501888,
   13983799152411887344,
   16605761493489116221]

private theorem queueThresholdStationaryNumerators_length :
    queueThresholdStationaryNumerators.length = 24 := rfl

/-- Exact rational mass of one physical state under the queue-threshold
stationary law for the nominal candidate. -/
def queueThresholdStationaryMassRat (state : PhysicalState) : ℚ :=
  (queueThresholdStationaryNumerators.get
      (Fin.cast queueThresholdStationaryNumerators_length.symm state) : ℚ) /
    1342444718631541185024

/-- The explicit rational mass vector is a probability mass function. -/
theorem queueThresholdStationaryMass_isPMF :
    IsPMF (fun state : PhysicalState ↦
      (queueThresholdStationaryMassRat state : ℝ)) := by
  constructor
  · intro state
    fin_cases state <;>
      norm_num [queueThresholdStationaryMassRat,
        queueThresholdStationaryNumerators]
  · norm_num [queueThresholdStationaryMassRat,
      queueThresholdStationaryNumerators, Fin.sum_univ_succ]

/-- Explicit stationary PMF for the nominal candidate under the generated
queue-threshold target policy. -/
def queueThresholdStationaryLaw : PMF PhysicalState :=
  queueThresholdStationaryMass_isPMF.toPMF

@[simp]
theorem queueThresholdStationaryLaw_apply_toReal (state : PhysicalState) :
    (queueThresholdStationaryLaw state).toReal =
      (queueThresholdStationaryMassRat state : ℝ) := by
  exact IsPMF.toPMF_apply_toReal queueThresholdStationaryMass_isPMF state

private theorem queueThresholdNominalTargetKernel_sum_apply_toReal
    (state nextState : PhysicalState) :
    (targetPolicyKernel nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex) state nextState).toReal =
      ∑ action : Action,
        (policyTableMass
            (targetPolicyTableIndex queueThresholdTargetIndex)
            state action : ℝ) *
          (candidateKernelTableMass nominalCandidateIndex
            (stateActionRowEquiv (state, action)) nextState : ℝ) := by
  unfold targetPolicyKernel
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro action _haction
    exact ENNReal.mul_ne_top
      ((targetPolicy queueThresholdTargetIndex state).apply_ne_top action)
      ((nominalCandidateEnvironment state action).apply_ne_top nextState))]
  simp only [ENNReal.toReal_mul, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, nominalCandidateEnvironment]

private def queueThresholdNominalKernelMassTable : List (List ℚ) :=
  [[1 / 96, 73 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 73 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 73 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 73 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 73 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 73 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 19 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 55 / 96, 1 / 96, 1 / 96, 19 / 96],
   [1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 1 / 96, 73 / 96, 1 / 96, 1 / 96]]

private theorem queueThresholdNominalKernelMassTable_length :
    queueThresholdNominalKernelMassTable.length = 24 := rfl

private abbrev queueThresholdNominalKernelMassRow
    (state : PhysicalState) : List ℚ :=
  queueThresholdNominalKernelMassTable.get
    (Fin.cast queueThresholdNominalKernelMassTable_length.symm state)

private theorem queueThresholdNominalKernelMassRow_length
    (state : PhysicalState) :
    (queueThresholdNominalKernelMassRow state).length = 24 := by
  fin_cases state <;> rfl

/-- Exact rational induced-kernel mass for the nominal candidate and generated
queue-threshold target policy. -/
def queueThresholdNominalKernelMassRat
    (state nextState : PhysicalState) : ℚ :=
  (queueThresholdNominalKernelMassRow state).get
    (Fin.cast (queueThresholdNominalKernelMassRow_length state).symm nextState)

private abbrev QueueThresholdNominalTargetKernelRowAt
    (state : PhysicalState) : Prop :=
  ∀ nextState : PhysicalState,
    (targetPolicyKernel nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex) state nextState).toReal =
      (queueThresholdNominalKernelMassRat state nextState : ℝ)

private theorem queueThresholdNominalTargetKernel_row_00 :
    QueueThresholdNominalTargetKernelRowAt (0 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_01 :
    QueueThresholdNominalTargetKernelRowAt (1 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_02 :
    QueueThresholdNominalTargetKernelRowAt (2 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_03 :
    QueueThresholdNominalTargetKernelRowAt (3 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_04 :
    QueueThresholdNominalTargetKernelRowAt (4 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_05 :
    QueueThresholdNominalTargetKernelRowAt (5 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_06 :
    QueueThresholdNominalTargetKernelRowAt (6 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_07 :
    QueueThresholdNominalTargetKernelRowAt (7 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_08 :
    QueueThresholdNominalTargetKernelRowAt (8 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_09 :
    QueueThresholdNominalTargetKernelRowAt (9 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_10 :
    QueueThresholdNominalTargetKernelRowAt (10 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_11 :
    QueueThresholdNominalTargetKernelRowAt (11 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_12 :
    QueueThresholdNominalTargetKernelRowAt (12 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_13 :
    QueueThresholdNominalTargetKernelRowAt (13 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_14 :
    QueueThresholdNominalTargetKernelRowAt (14 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_15 :
    QueueThresholdNominalTargetKernelRowAt (15 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_16 :
    QueueThresholdNominalTargetKernelRowAt (16 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_17 :
    QueueThresholdNominalTargetKernelRowAt (17 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_18 :
    QueueThresholdNominalTargetKernelRowAt (18 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_19 :
    QueueThresholdNominalTargetKernelRowAt (19 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_20 :
    QueueThresholdNominalTargetKernelRowAt (20 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_21 :
    QueueThresholdNominalTargetKernelRowAt (21 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_22 :
    QueueThresholdNominalTargetKernelRowAt (22 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

private theorem queueThresholdNominalTargetKernel_row_23 :
    QueueThresholdNominalTargetKernelRowAt (23 : PhysicalState) := by
  intro nextState
  rw [queueThresholdNominalTargetKernel_sum_apply_toReal]
  fin_cases nextState <;>
    norm_num [queueThresholdNominalKernelMassRat,
      queueThresholdNominalKernelMassRow,
      queueThresholdNominalKernelMassTable, queueThresholdTargetIndex,
      nominalCandidateIndex, targetPolicyTableIndex, policyTableMass,
      candidateKernelTableMass_eq_refreshMixture,
      nominalCandidateGammaRat_eq_three_fourths,
      candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
      ControlledQueueData.policyTable,
      ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff, Fin.sum_univ_succ]

/-- The explicit rational induced-kernel table agrees with the generated
nominal environment and queue-threshold target policy. -/
theorem queueThresholdNominalTargetKernel_apply_toReal
    (state nextState : PhysicalState) :
    (targetPolicyKernel nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex) state nextState).toReal =
      (queueThresholdNominalKernelMassRat state nextState : ℝ) := by
  fin_cases state
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_00 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_01 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_02 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_03 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_04 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_05 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_06 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_07 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_08 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_09 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_10 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_11 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_12 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_13 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_14 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_15 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_16 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_17 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_18 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_19 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_20 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_21 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_22 nextState
  · simpa [QueueThresholdNominalTargetKernelRowAt] using
      queueThresholdNominalTargetKernel_row_23 nextState

private theorem queueThresholdStationary_balance_rat_00 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (0 : PhysicalState)) =
      queueThresholdStationaryMassRat (0 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_01 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (1 : PhysicalState)) =
      queueThresholdStationaryMassRat (1 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_02 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (2 : PhysicalState)) =
      queueThresholdStationaryMassRat (2 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_03 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (3 : PhysicalState)) =
      queueThresholdStationaryMassRat (3 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_04 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (4 : PhysicalState)) =
      queueThresholdStationaryMassRat (4 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_05 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (5 : PhysicalState)) =
      queueThresholdStationaryMassRat (5 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_06 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (6 : PhysicalState)) =
      queueThresholdStationaryMassRat (6 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_07 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (7 : PhysicalState)) =
      queueThresholdStationaryMassRat (7 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_08 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (8 : PhysicalState)) =
      queueThresholdStationaryMassRat (8 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_09 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (9 : PhysicalState)) =
      queueThresholdStationaryMassRat (9 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_10 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (10 : PhysicalState)) =
      queueThresholdStationaryMassRat (10 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_11 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (11 : PhysicalState)) =
      queueThresholdStationaryMassRat (11 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_12 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (12 : PhysicalState)) =
      queueThresholdStationaryMassRat (12 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_13 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (13 : PhysicalState)) =
      queueThresholdStationaryMassRat (13 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_14 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (14 : PhysicalState)) =
      queueThresholdStationaryMassRat (14 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_15 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (15 : PhysicalState)) =
      queueThresholdStationaryMassRat (15 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_16 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (16 : PhysicalState)) =
      queueThresholdStationaryMassRat (16 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_17 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (17 : PhysicalState)) =
      queueThresholdStationaryMassRat (17 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_18 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (18 : PhysicalState)) =
      queueThresholdStationaryMassRat (18 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_19 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (19 : PhysicalState)) =
      queueThresholdStationaryMassRat (19 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_20 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (20 : PhysicalState)) =
      queueThresholdStationaryMassRat (20 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_21 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (21 : PhysicalState)) =
      queueThresholdStationaryMassRat (21 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_22 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (22 : PhysicalState)) =
      queueThresholdStationaryMassRat (22 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]

private theorem queueThresholdStationary_balance_rat_23 :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state (23 : PhysicalState)) =
      queueThresholdStationaryMassRat (23 : PhysicalState) := by
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalKernelMassRat,
    queueThresholdNominalKernelMassRow,
    queueThresholdNominalKernelMassTable, Fin.sum_univ_succ]


private theorem queueThresholdStationary_balance_rat
    (nextState : PhysicalState) :
    (∑ state : PhysicalState,
        queueThresholdStationaryMassRat state *
          queueThresholdNominalKernelMassRat state nextState) =
      queueThresholdStationaryMassRat nextState := by
  fin_cases nextState
  · simpa using queueThresholdStationary_balance_rat_00
  · simpa using queueThresholdStationary_balance_rat_01
  · simpa using queueThresholdStationary_balance_rat_02
  · simpa using queueThresholdStationary_balance_rat_03
  · simpa using queueThresholdStationary_balance_rat_04
  · simpa using queueThresholdStationary_balance_rat_05
  · simpa using queueThresholdStationary_balance_rat_06
  · simpa using queueThresholdStationary_balance_rat_07
  · simpa using queueThresholdStationary_balance_rat_08
  · simpa using queueThresholdStationary_balance_rat_09
  · simpa using queueThresholdStationary_balance_rat_10
  · simpa using queueThresholdStationary_balance_rat_11
  · simpa using queueThresholdStationary_balance_rat_12
  · simpa using queueThresholdStationary_balance_rat_13
  · simpa using queueThresholdStationary_balance_rat_14
  · simpa using queueThresholdStationary_balance_rat_15
  · simpa using queueThresholdStationary_balance_rat_16
  · simpa using queueThresholdStationary_balance_rat_17
  · simpa using queueThresholdStationary_balance_rat_18
  · simpa using queueThresholdStationary_balance_rat_19
  · simpa using queueThresholdStationary_balance_rat_20
  · simpa using queueThresholdStationary_balance_rat_21
  · simpa using queueThresholdStationary_balance_rat_22
  · simpa using queueThresholdStationary_balance_rat_23

private theorem queueThresholdStationary_balance
    (nextState : PhysicalState) :
    ∑ state : PhysicalState,
        (queueThresholdStationaryLaw state).toReal *
          (targetPolicyKernel nominalCandidateEnvironment
            (targetPolicy queueThresholdTargetIndex)
            state nextState).toReal =
      (queueThresholdStationaryLaw nextState).toReal := by
  simp_rw [queueThresholdStationaryLaw_apply_toReal,
    queueThresholdNominalTargetKernel_apply_toReal]
  exact_mod_cast queueThresholdStationary_balance_rat nextState

/-- The explicit law is invariant under the nominal candidate and generated
queue-threshold target policy. -/
theorem queueThresholdStationaryLaw_isInvariant :
    IsInvariantPMF
      (targetPolicyKernel nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex))
      queueThresholdStationaryLaw := by
  unfold IsInvariantPMF
  apply PMF.ext
  intro nextState
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (queueThresholdStationaryLaw.bind
        (targetPolicyKernel nominalCandidateEnvironment
          (targetPolicy queueThresholdTargetIndex))) nextState)
    (PMF.apply_ne_top queueThresholdStationaryLaw nextState)).mp
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro state _hstate
    exact ENNReal.mul_ne_top
      (queueThresholdStationaryLaw.apply_ne_top state)
      ((targetPolicyKernel nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex) state).apply_ne_top nextState))]
  simpa only [ENNReal.toReal_mul] using
    queueThresholdStationary_balance nextState

/-- The explicit invariant law is the canonical finite invariant witness used
by the corresponding queue-catalog atom.  Identification uses strict
Dobrushin contraction, not the choice principle alone. -/
theorem queueThresholdStationaryLaw_eq_catalogStationary :
    queueThresholdStationaryLaw =
      queueHypothesisStationary nominalCandidateEnvironment
        queueThresholdNominalModelHypothesis := by
  unfold queueHypothesisStationary queueThresholdNominalModelHypothesis
    queueHypothesisTargetPolicy
  apply invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one
  · exact lt_of_le_of_lt
      (candidateTargetPolicyKernel_dobrushin_le_gamma
        nominalCandidateIndex (targetPolicy queueThresholdTargetIndex))
      (by rw [nominalCandidateGamma_eq_three_fourths]; norm_num)
  · exact queueThresholdStationaryLaw_isInvariant
  · exact finiteInvariantPMF_isInvariant _

private def queueThresholdNominalModelRowRiskTable : List ℚ :=
  [15 / 256, 15 / 256, 15 / 256, 15 / 256, 15 / 256, 15 / 256,
   15 / 256, 15 / 256, 15 / 256, 15 / 256, 15 / 256, 15 / 256,
   15 / 256, 15 / 256, 15 / 256, 15 / 256, 15 / 256, 21 / 256,
   15 / 256, 21 / 256, 39 / 256, 21 / 256, 39 / 256, 39 / 256]

private theorem queueThresholdNominalModelRowRiskTable_length :
    queueThresholdNominalModelRowRiskTable.length = 24 := rfl

/-- Exact one-step Brier row risk for the queue-threshold policy and the
nominal-model overload predictor. -/
def queueThresholdNominalModelRowRisk (state : PhysicalState) : ℚ :=
  queueThresholdNominalModelRowRiskTable.get
    (Fin.cast queueThresholdNominalModelRowRiskTable_length.symm state)

private abbrev QueueThresholdNominalModelRowRiskAt
    (state : PhysicalState) : Prop :=
  targetPolicyRowRisk nominalCandidateEnvironment
      (targetPolicy queueThresholdTargetIndex)
      (fixedBrierScore nominalModelOverloadPredictorIndex) state =
    (queueThresholdNominalModelRowRisk state : ℝ)

private theorem queueThreshold_nominalModelOverload_rowRisk_00 :
    QueueThresholdNominalModelRowRiskAt (0 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_01 :
    QueueThresholdNominalModelRowRiskAt (1 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_02 :
    QueueThresholdNominalModelRowRiskAt (2 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_03 :
    QueueThresholdNominalModelRowRiskAt (3 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_04 :
    QueueThresholdNominalModelRowRiskAt (4 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_05 :
    QueueThresholdNominalModelRowRiskAt (5 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_06 :
    QueueThresholdNominalModelRowRiskAt (6 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_07 :
    QueueThresholdNominalModelRowRiskAt (7 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_08 :
    QueueThresholdNominalModelRowRiskAt (8 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_09 :
    QueueThresholdNominalModelRowRiskAt (9 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_10 :
    QueueThresholdNominalModelRowRiskAt (10 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_11 :
    QueueThresholdNominalModelRowRiskAt (11 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_12 :
    QueueThresholdNominalModelRowRiskAt (12 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_13 :
    QueueThresholdNominalModelRowRiskAt (13 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_14 :
    QueueThresholdNominalModelRowRiskAt (14 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_15 :
    QueueThresholdNominalModelRowRiskAt (15 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_16 :
    QueueThresholdNominalModelRowRiskAt (16 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_17 :
    QueueThresholdNominalModelRowRiskAt (17 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_18 :
    QueueThresholdNominalModelRowRiskAt (18 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_19 :
    QueueThresholdNominalModelRowRiskAt (19 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_20 :
    QueueThresholdNominalModelRowRiskAt (20 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_21 :
    QueueThresholdNominalModelRowRiskAt (21 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_22 :
    QueueThresholdNominalModelRowRiskAt (22 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem queueThreshold_nominalModelOverload_rowRisk_23 :
    QueueThresholdNominalModelRowRiskAt (23 : PhysicalState) := by
  norm_num [QueueThresholdNominalModelRowRiskAt, targetPolicyRowRisk,
    nominalCandidateEnvironment, queueThresholdTargetIndex,
    nominalModelOverloadPredictorIndex, queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, fixedBrierScore,
    fixedPredictorProbability, fixedPredictorTableValue, overloadOutcome,
    overloadOutcomeTableValue, targetPolicy_apply_toReal,
    candidateEnvironment_apply_toReal, targetPolicyTableIndex,
    policyTableMass, candidateKernelTableMass_eq_refreshMixture,
    nominalCandidateGammaRat_eq_three_fourths,
    candidateKernelStep_stateActionRowEquiv,
      candidateKernelStepStateAction,
    ControlledQueueData.policyTable,
    ControlledQueueData.candidateKernelStepByRow, Fin.ext_iff,
    ControlledQueueData.fixedPredictorTable,
    ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]


/-- The generated target-policy row risk agrees with the explicit rational
twenty-four-state vector. -/
theorem queueThreshold_nominalModelOverload_rowRisk
    (state : PhysicalState) :
    targetPolicyRowRisk nominalCandidateEnvironment
      (targetPolicy queueThresholdTargetIndex)
      (fixedBrierScore nominalModelOverloadPredictorIndex) state =
      (queueThresholdNominalModelRowRisk state : ℝ) := by
  fin_cases state
  · exact queueThreshold_nominalModelOverload_rowRisk_00
  · exact queueThreshold_nominalModelOverload_rowRisk_01
  · exact queueThreshold_nominalModelOverload_rowRisk_02
  · exact queueThreshold_nominalModelOverload_rowRisk_03
  · exact queueThreshold_nominalModelOverload_rowRisk_04
  · exact queueThreshold_nominalModelOverload_rowRisk_05
  · exact queueThreshold_nominalModelOverload_rowRisk_06
  · exact queueThreshold_nominalModelOverload_rowRisk_07
  · exact queueThreshold_nominalModelOverload_rowRisk_08
  · exact queueThreshold_nominalModelOverload_rowRisk_09
  · exact queueThreshold_nominalModelOverload_rowRisk_10
  · exact queueThreshold_nominalModelOverload_rowRisk_11
  · exact queueThreshold_nominalModelOverload_rowRisk_12
  · exact queueThreshold_nominalModelOverload_rowRisk_13
  · exact queueThreshold_nominalModelOverload_rowRisk_14
  · exact queueThreshold_nominalModelOverload_rowRisk_15
  · exact queueThreshold_nominalModelOverload_rowRisk_16
  · exact queueThreshold_nominalModelOverload_rowRisk_17
  · exact queueThreshold_nominalModelOverload_rowRisk_18
  · exact queueThreshold_nominalModelOverload_rowRisk_19
  · exact queueThreshold_nominalModelOverload_rowRisk_20
  · exact queueThreshold_nominalModelOverload_rowRisk_21
  · exact queueThreshold_nominalModelOverload_rowRisk_22
  · exact queueThreshold_nominalModelOverload_rowRisk_23

/-- Exact stationary Brier risk of the nominal-model overload predictor under
the nominal environment and generated queue-threshold target policy. -/
theorem queueThreshold_nominalModelOverload_stationaryRisk :
    stationaryTargetPolicyRisk nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex)
        queueThresholdStationaryLaw
        (fixedBrierScore nominalModelOverloadPredictorIndex) =
      4338268437 / 67816493056 := by
  unfold stationaryTargetPolicyRisk
  simp_rw [queueThresholdStationaryLaw_apply_toReal,
    queueThreshold_nominalModelOverload_rowRisk]
  norm_num [queueThresholdStationaryMassRat,
    queueThresholdStationaryNumerators,
    queueThresholdNominalModelRowRisk,
    queueThresholdNominalModelRowRiskTable, Fin.sum_univ_succ]

/-- Catalog-facing form of the exact stationary Brier-risk receipt. -/
theorem queueThreshold_nominalModelOverload_catalogStationaryRisk :
    stationaryTargetPolicyRisk nominalCandidateEnvironment
        (queueHypothesisTargetPolicy queueThresholdNominalModelHypothesis)
        (queueHypothesisStationary nominalCandidateEnvironment
          queueThresholdNominalModelHypothesis)
        (queueHypothesisScore queueThresholdNominalModelHypothesis) =
      4338268437 / 67816493056 := by
  change stationaryTargetPolicyRisk nominalCandidateEnvironment
      (targetPolicy queueThresholdTargetIndex)
      (queueHypothesisStationary nominalCandidateEnvironment
        queueThresholdNominalModelHypothesis)
      (fixedBrierScore nominalModelOverloadPredictorIndex) =
    4338268437 / 67816493056
  rw [← queueThresholdStationaryLaw_eq_catalogStationary]
  exact queueThreshold_nominalModelOverload_stationaryRisk

end

end FormalSLT.Applications.ControlledQueue
