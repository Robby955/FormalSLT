/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathData

/-!
# Full score/path theorem instance for the GJP Brier replay

The generated calculation modules reconstruct the 175 observed Brier losses,
their prefix predictors, and their quadratic variation from the hash-bound
outcome and forecast streams. This module connects those checked pathwise
quantities to the finite sleeping suffix-variance PAC-Bayes theorem.

The confidence conclusion is necessarily probabilistic: an explicit event has
outer failure mass at most `1 / 160`. Observed data alone cannot establish that
one realized random path belongs to its confidence event. On that event, the
posterior-averaged conditional Brier risk encountered along the monitored
prefix is below the checked endpoint. It is not future, population,
stationary, or deployment risk without an additional bridge.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle
open scoped BigOperators

namespace FormalSLT.Applications.GJPBrierMonitorReplayPath

open FormalSLT.StochasticDynamics
open GJPBrierMonitorReplayData
open GJPBrierMonitorReplayReceipt
open GJPBrierMonitorReplayPathData

noncomputable section

abbrev Model := GJPBrierMonitorReplayData.Model

private theorem replay_model_empirical_sum
    (model : Model) :
    (∑ k ∈ Finset.Ico 0 horizon,
        observedTrajectoryScore (monitorBrierScore model) k replayPath) =
      horizon * ratToReal (monitorEmpiricalBrierQ model) := by
  rw [← Finset.range_eq_Ico]
  rcases model with ⟨a, b⟩
  cases a <;> cases b
  · rw [observedConstantTrainBaseRateLossPrefix175]
    norm_num [horizon, ratToReal, monitorEmpiricalBrierQ]
  · rw [observedFirstWeekMeanLossPrefix175]
    norm_num [horizon, ratToReal, monitorEmpiricalBrierQ]
  · rw [observedFinalConsensusMedianLossPrefix175]
    norm_num [horizon, ratToReal, monitorEmpiricalBrierQ]
  · rw [observedExtremizedFinalConsensusLossPrefix175]
    norm_num [horizon, ratToReal, monitorEmpiricalBrierQ]

/-- The theorem's empirical score is reconstructed from every forecast and
outcome in the named replay. -/
theorem replay_empiricalPrequentialRisk_eq :
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        monitorBrierScore selectedPosterior 0 horizon replayPath =
      (posteriorEmpiricalBrierRisk : Real) := by
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    posteriorAverage
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [replay_model_empirical_sum (false, false),
    replay_model_empirical_sum (false, true),
    replay_model_empirical_sum (true, false),
    replay_model_empirical_sum (true, true)]
  norm_num [horizon, selectedPosterior, posteriorQ,
    monitorEmpiricalBrierQ, posteriorEmpiricalBrierRisk, ratToReal]

private theorem replay_model_quadratic_sum
    (model : Model) :
    (∑ k ∈ Finset.Ico 0 horizon,
      (observedTrajectoryScore (monitorBrierScore model) k replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore (monitorBrierScore model)) k replayPath) ^ 2) =
      ratToReal (monitorQuadraticVariationQ model) := by
  rw [← Finset.range_eq_Ico]
  rcases model with ⟨a, b⟩
  cases a <;> cases b
  · rw [observedConstantTrainBaseRateQuadraticPrefix175]
  · rw [observedFirstWeekMeanQuadraticPrefix175]
  · rw [observedFinalConsensusMedianQuadraticPrefix175]
  · rw [observedExtremizedFinalConsensusQuadraticPrefix175]

/-- The theorem's observable forward-predictor quadratic variation is
reconstructed from the same named path. -/
theorem replay_suffixPredictorQuadraticVariation_eq :
    finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
        monitorBrierScore selectedPosterior 0 horizon replayPath =
      (suffixPredictorQuadraticVariation : Real) := by
  unfold finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
    posteriorAverage
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [replay_model_quadratic_sum (false, false),
    replay_model_quadratic_sum (false, true),
    replay_model_quadratic_sum (true, false),
    replay_model_quadratic_sum (true, true)]
  norm_num [selectedPosterior, posteriorQ, monitorQuadraticVariationQ,
    suffixPredictorQuadraticVariation, ratToReal]

/-- At the admitted `lambda = 1/2` atom, the theorem-produced pathwise
boundary is exactly the real expression checked by the arithmetic receipt. -/
theorem replay_geometricAtomBoundary_eq_summary :
    finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        uniformPrior selectedPosterior monitorBrierScore
        ((1 : Real) / 160) 0 0 horizon replayPath =
      summaryInstantiatedEndpoint := by
  unfold finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
    finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
  rw [replay_empiricalPrequentialRisk_eq,
    replay_suffixPredictorQuadraticVariation_eq]
  norm_num [continuousTrajectorySleepingSuffixEffectiveConfidence,
    polynomialEpochWeight, geometricForwardBesselPACBayesComplexity,
    geometricForwardTilt, summaryInstantiatedEndpoint]

theorem replay_selectedBoundary_le_summary :
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        uniformPrior selectedPosterior monitorBrierScore
        ((1 : Real) / 160) 0 horizon replayPath ≤
      summaryInstantiatedEndpoint := by
  calc
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        uniformPrior selectedPosterior monitorBrierScore
        ((1 : Real) / 160) 0 horizon replayPath ≤
      finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        uniformPrior selectedPosterior monitorBrierScore
        ((1 : Real) / 160) 0 0 horizon replayPath := by
          apply finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le
          simp
    _ = summaryInstantiatedEndpoint := replay_geometricAtomBoundary_eq_summary

/-- Explicit success event for an arbitrary history-dependent binary outcome
kernel. It names the statistical claim whose failure mass is controlled. -/
def replayRiskEvent
    (P : (n : Nat) → ((i : Finset.Iic n) → Bool) → Bool → Real) :
    Set (Nat → Bool) :=
  {x | finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
      P monitorBrierScore selectedPosterior 0 horizon x <
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
      uniformPrior selectedPosterior monitorBrierScore
      ((1 : Real) / 160) 0 horizon x}

/-- Full theorem instance: for every supplied finite Boolean trajectory
kernel, the named GJP monitoring protocol fails with outer mass at most
`1 / 160`. -/
theorem replayRiskEvent_failureMass_le
    (P : (n : Nat) → ((i : Finset.Iic n) → Bool) → Bool → Real)
    (hP : ∀ n u, IsPMF (P n u)) :
    (trajectoryMeasure (finiteTrajectoryKernel P hP) false).real
        (replayRiskEvent P)ᶜ ≤ (1 : Real) / 160 := by
  rcases exists_finitePMFTrajectorySleepingSuffixVarianceOracle_event
      P hP false monitorBrierScore monitorBrierScore_mem_Icc
      (hprior := uniformPrior_isFullSupportPMF)
      (delta := (1 : Real) / 160) (by norm_num) (by norm_num)
      (fun _x _n => selectedPosterior)
      (fun _x _n => selectedPosterior_isPMF)
      (fun _x _n => 0) with
    ⟨goodEvent, hmass, hgood⟩
  calc
    (trajectoryMeasure (finiteTrajectoryKernel P hP) false).real
        (replayRiskEvent P)ᶜ ≤
      (trajectoryMeasure (finiteTrajectoryKernel P hP) false).real
        goodEventᶜ := by
          refine measureReal_mono ?_ (by finiteness)
          intro x hx
          simp only [Set.mem_compl_iff] at hx ⊢
          intro hxgood
          apply hx
          exact (hgood x hxgood horizon (by norm_num [horizon])).2.1
    _ ≤ (1 : Real) / 160 := hmass

/-- If the realized replay lies in the named confidence event, its encountered
posterior conditional risk is below the conservative checked endpoint. The
mass theorem above, rather than a deterministic membership assertion, is the
valid confidence guarantee. -/
theorem replayPath_conditionalRisk_lt_oneHundredFortyEight_thousandths
    (P : (n : Nat) → ((i : Finset.Iic n) → Bool) → Bool → Real)
    (hpath : replayPath ∈ replayRiskEvent P) :
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        P monitorBrierScore selectedPosterior 0 horizon replayPath <
      (148 : Real) / 1000 := by
  exact hpath.trans (replay_selectedBoundary_le_summary.trans_lt
    summaryInstantiatedEndpoint_lt_oneHundredFortyEight_thousandths)

end

end FormalSLT.Applications.GJPBrierMonitorReplayPath
