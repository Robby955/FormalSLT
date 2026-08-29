/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayData
import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingSuffixVarianceOracle
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Kernel-checked arithmetic for the GJP Brier-monitor replay

The generated data module records exact rational inputs extracted from the
hash-bound GJP replay.  The generator independently verifies the stream and
receipt digests and recomputes the posterior empirical Brier loss and the
forward-predictor quadratic variation from all 175 monitor observations.

This module starts at that explicit trust boundary.  Lean treats the generated
exact rationals as certificate inputs, checks the posterior and all subsequent
KL, confidence-allocation, cumulant, and endpoint arithmetic, and proves a
conservative nonvacuous endpoint.  It does not parse JSON inside Lean or prove
that the named replay belongs to a theorem-produced good event.

The conditional target is posterior-averaged conditional loss encountered on
the monitored prefix.  It is not future, population, stationary, or deployment
risk without another theorem.  The preregistered study verdict also remains
`FAIL`: the B2 win count is zero and the shuffled-time control is incomplete.
-/

open Finset
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators

namespace FormalSLT.Applications.GJPBrierMonitorReplayReceipt

noncomputable section

abbrev Model := GJPBrierMonitorReplayData.Model

/-- Uniform four-model prior used by the replay. -/
def uniformPrior (_model : Model) : Real := 1 / 4

/-- Exact posterior weights recorded by the hash-bound replay. -/
def selectedPosterior (model : Model) : Real :=
  (GJPBrierMonitorReplayData.posteriorQ model : Real)

theorem uniformPrior_isFullSupportPMF : IsFullSupportPMF uniformPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro model
    norm_num [uniformPrior]
  · rw [Fintype.sum_prod_type]
    norm_num [uniformPrior, Fintype.sum_bool]
  · intro model
    norm_num [uniformPrior]

theorem selectedPosterior_isPMF : IsPMF selectedPosterior := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b⟩
    cases a <;> cases b <;>
      norm_num [selectedPosterior, GJPBrierMonitorReplayData.posteriorQ]
  · rw [Fintype.sum_prod_type]
    norm_num [selectedPosterior, GJPBrierMonitorReplayData.posteriorQ,
      Fintype.sum_bool]

theorem selectedPosterior_pos (model : Model) :
    0 < selectedPosterior model := by
  rcases model with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [selectedPosterior, GJPBrierMonitorReplayData.posteriorQ]

theorem selectedPosterior_le_one (model : Model) :
    selectedPosterior model ≤ 1 :=
  finitePMF_apply_le_one selectedPosterior_isPMF model

/-! ## Exact aggregation of the four model summaries -/

def reconstructedPosteriorEmpiricalBrierRiskQ : Rat :=
  ∑ model, GJPBrierMonitorReplayData.posteriorQ model *
    GJPBrierMonitorReplayData.monitorEmpiricalBrierQ model

def reconstructedPosteriorQuadraticVariationQ : Rat :=
  ∑ model, GJPBrierMonitorReplayData.posteriorQ model *
    GJPBrierMonitorReplayData.monitorQuadraticVariationQ model

theorem reconstructedPosteriorEmpiricalBrierRiskQ_eq :
    reconstructedPosteriorEmpiricalBrierRiskQ =
      GJPBrierMonitorReplayData.posteriorEmpiricalBrierRisk := by
  unfold reconstructedPosteriorEmpiricalBrierRiskQ
  rw [Fintype.sum_prod_type]
  norm_num [GJPBrierMonitorReplayData.posteriorQ,
    GJPBrierMonitorReplayData.monitorEmpiricalBrierQ, Fintype.sum_bool,
    GJPBrierMonitorReplayData.posteriorEmpiricalBrierRisk]

theorem reconstructedPosteriorQuadraticVariationQ_eq :
    reconstructedPosteriorQuadraticVariationQ =
      GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation := by
  unfold reconstructedPosteriorQuadraticVariationQ
  rw [Fintype.sum_prod_type]
  norm_num [GJPBrierMonitorReplayData.posteriorQ,
    GJPBrierMonitorReplayData.monitorQuadraticVariationQ, Fintype.sum_bool,
    GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation]

private theorem selectedPosterior_kl_le_log_four :
    klDiv selectedPosterior uniformPrior ≤ Real.log 4 := by
  unfold klDiv
  calc
    (∑ model, selectedPosterior model *
        Real.log (selectedPosterior model / uniformPrior model)) ≤
        ∑ model, selectedPosterior model * Real.log 4 := by
      apply Finset.sum_le_sum
      intro model _hmodel
      have hposteriorPos : 0 < selectedPosterior model :=
        selectedPosterior_pos model
      have hratioPos :
          0 < selectedPosterior model / uniformPrior model := by
        exact div_pos hposteriorPos (by norm_num [uniformPrior])
      have hratioLe :
          selectedPosterior model / uniformPrior model ≤ 4 := by
        have hposteriorLe := selectedPosterior_le_one model
        norm_num [uniformPrior] at ⊢
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log hratioPos hratioLe) hposteriorPos.le
    _ = Real.log 4 := by
      rw [← Finset.sum_mul, selectedPosterior_isPMF.sum_one, one_mul]

private theorem log_four_eq_two_log_two :
    Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
  norm_num

/-- A simple prior-only KL ceiling, sufficient for the finite replay bound. -/
theorem selectedPosterior_kl_lt_seven_fifths :
    klDiv selectedPosterior uniformPrior < (7 : Real) / 5 := by
  have hlogTwo : Real.log 2 < (7 : Real) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  calc
    klDiv selectedPosterior uniformPrior ≤ Real.log 4 :=
      selectedPosterior_kl_le_log_four
    _ = 2 * Real.log 2 := log_four_eq_two_log_two
    _ < 2 * ((7 : Real) / 10) :=
      mul_lt_mul_of_pos_left hlogTwo (by norm_num)
    _ = (7 : Real) / 5 := by norm_num

private theorem psi_half_eq :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) =
      Real.log 2 - 1 / 2 := by
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num]
  rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  ring

private theorem psi_half_nonneg :
    0 ≤ forwardEmpiricalBernsteinPsi (1 / 2 : Real) :=
  forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)

private theorem psi_half_lt_one_fifth :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) < 1 / 5 := by
  rw [psi_half_eq]
  have hlogTwo : Real.log 2 < (7 : Real) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  linarith

private theorem log_five_fourths_le_one_fourth :
    Real.log (5 / 4 : Real) ≤ 1 / 4 := by
  have h := Real.log_le_sub_one_of_pos
    (show (0 : Real) < 5 / 4 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_sixHundredForty_eq :
    Real.log 640 = 9 * Real.log 2 + Real.log (5 / 4 : Real) := by
  calc
    Real.log 640 = Real.log ((2 : Real) ^ 9 * (5 / 4)) := by norm_num
    _ = Real.log ((2 : Real) ^ 9) + Real.log (5 / 4 : Real) := by
      rw [Real.log_mul (by positivity) (by norm_num)]
    _ = 9 * Real.log 2 + Real.log (5 / 4 : Real) := by
      rw [Real.log_pow]
      norm_num

private theorem log_sixHundredForty_lt_oneHundredThirtyOne_twentieths :
    Real.log 640 < (131 : Real) / 20 := by
  rw [log_sixHundredForty_eq]
  have hlogTwo : Real.log 2 < (7 : Real) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlogFiveFourths := log_five_fourths_le_one_fourth
  linarith

theorem tracked_empiricalBrierRisk_lt_fortyEight_thousandths :
    (GJPBrierMonitorReplayData.posteriorEmpiricalBrierRisk : Real) <
      (48 : Real) / 1000 := by
  norm_num [GJPBrierMonitorReplayData.posteriorEmpiricalBrierRisk]

theorem tracked_quadraticVariation_nonneg :
    0 ≤ (GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation : Real) := by
  norm_num [GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation]

theorem tracked_quadraticVariation_lt_four :
    (GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation : Real) < 4 := by
  norm_num [GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation]

private theorem tracked_psi_mul_quadraticVariation_lt_four_fifths :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
        (GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation : Real) <
      (4 : Real) / 5 := by
  calc
    _ ≤ forwardEmpiricalBernsteinPsi (1 / 2 : Real) * 4 :=
      mul_le_mul_of_nonneg_left tracked_quadraticVariation_lt_four.le
        psi_half_nonneg
    _ < (1 / 5 : Real) * 4 :=
      mul_lt_mul_of_pos_right psi_half_lt_one_fifth (by norm_num)
    _ = (4 : Real) / 5 := by norm_num

/-- The replay's supported `lambda = 1/2` atom, written entirely from exact
generated summaries and the public finite PAC-Bayes primitives. -/
def summaryInstantiatedEndpoint : Real :=
  (GJPBrierMonitorReplayData.posteriorEmpiricalBrierRisk : Real) +
    (klDiv selectedPosterior uniformPrior + Real.log 640 +
      forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
        (GJPBrierMonitorReplayData.suffixPredictorQuadraticVariation : Real)) /
      ((1 / 2 : Real) * GJPBrierMonitorReplayData.horizon)

/-- Conservative kernel-checked endpoint for the exact generated summaries.
The looser `0.148` value avoids trusting external floating-point logarithms. -/
theorem summaryInstantiatedEndpoint_lt_oneHundredFortyEight_thousandths :
    summaryInstantiatedEndpoint < (148 : Real) / 1000 := by
  unfold summaryInstantiatedEndpoint
  have hemp := tracked_empiricalBrierRisk_lt_fortyEight_thousandths
  have hkl := selectedPosterior_kl_lt_seven_fifths
  have hlog := log_sixHundredForty_lt_oneHundredThirtyOne_twentieths
  have hquad := tracked_psi_mul_quadraticVariation_lt_four_fifths
  norm_num [GJPBrierMonitorReplayData.horizon] at ⊢
  nlinarith

theorem trackedBoundaryUpper_lt_oneHundredThirtyNine_thousandths :
    GJPBrierMonitorReplayData.selectedBoundaryUpper < (139 : Rat) / 1000 := by
  norm_num [GJPBrierMonitorReplayData.selectedBoundaryUpper]

theorem summaryEndpoint_lt_constantModelMonitorEmpiricalBrier :
    summaryInstantiatedEndpoint <
      (GJPBrierMonitorReplayData.constantModelMonitorEmpiricalBrier : Real) := by
  exact summaryInstantiatedEndpoint_lt_oneHundredFortyEight_thousandths.trans
    (by
      norm_num [GJPBrierMonitorReplayData.constantModelMonitorEmpiricalBrier])

theorem summaryEndpoint_lt_trainBaseRateBrierThreshold :
    summaryInstantiatedEndpoint <
      (GJPBrierMonitorReplayData.trainBaseRateBrierThreshold : Real) := by
  exact summaryInstantiatedEndpoint_lt_oneHundredFortyEight_thousandths.trans
    (by
      norm_num [GJPBrierMonitorReplayData.trainBaseRateBrierThreshold])

/-- Conditional receipt composition.  The premise is the statistical
good-event inequality for the replay summaries; this module does not prove
named-path membership in that event. -/
theorem conditionalMonitoredRisk_lt_oneHundredFortyEight_thousandths
    {monitoredConditionalRisk : Real}
    (hgood : monitoredConditionalRisk < summaryInstantiatedEndpoint) :
    monitoredConditionalRisk < (148 : Real) / 1000 :=
  hgood.trans summaryInstantiatedEndpoint_lt_oneHundredFortyEight_thousandths

end

end FormalSLT.Applications.GJPBrierMonitorReplayReceipt
