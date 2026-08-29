/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathDataFirstWeekMean
import Mathlib.Tactic

/-!
# Generated GJP path calculation: final-consensus-median

Generated from the hash-bound GJP stream and receipt. Small prefix
recurrences keep kernel checking bounded in memory.
-/

open Finset
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.Applications.GJPBrierMonitorReplayPathData

open FormalSLT.StochasticDynamics
open GJPBrierMonitorReplayData

noncomputable section

set_option maxRecDepth 100000

theorem observedFinalConsensusMedianLoss0 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 0 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss1 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 1 replayPath =
      ratToReal ((169 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss2 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 2 replayPath =
      ratToReal ((49 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss3 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 3 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss4 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 4 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss5 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 5 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss6 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 6 replayPath =
      ratToReal ((1 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss7 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 7 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss8 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 8 replayPath =
      ratToReal ((9 : Rat) / 16) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss9 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 9 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss10 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 10 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss11 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 11 replayPath =
      ratToReal ((49 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss12 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 12 replayPath =
      ratToReal ((121 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss13 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 13 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss14 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 14 replayPath =
      ratToReal ((9 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss15 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 15 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss16 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 16 replayPath =
      ratToReal ((1 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss17 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 17 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss18 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 18 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss19 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 19 replayPath =
      ratToReal ((1 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss20 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 20 replayPath =
      ratToReal (0 : Rat) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss21 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 21 replayPath =
      ratToReal ((529 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss22 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 22 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss23 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 23 replayPath =
      ratToReal ((49 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss24 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 24 replayPath =
      ratToReal ((81 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss25 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 25 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss26 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 26 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss27 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 27 replayPath =
      ratToReal ((49 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss28 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 28 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss29 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 29 replayPath =
      ratToReal ((1 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss30 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 30 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss31 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 31 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss32 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 32 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss33 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 33 replayPath =
      ratToReal ((121 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss34 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 34 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss35 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 35 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss36 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 36 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss37 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 37 replayPath =
      ratToReal ((121 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss38 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 38 replayPath =
      ratToReal ((16 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss39 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 39 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss40 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 40 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss41 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 41 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss42 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 42 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss43 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 43 replayPath =
      ratToReal ((49 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss44 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 44 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss45 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 45 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss46 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 46 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss47 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 47 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss48 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 48 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss49 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 49 replayPath =
      ratToReal ((9 : Rat) / 1600) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss50 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 50 replayPath =
      ratToReal ((1 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss51 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 51 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss52 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 52 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss53 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 53 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss54 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 54 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss55 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 55 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss56 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 56 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss57 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 57 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss58 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 58 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss59 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 59 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss60 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 60 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss61 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 61 replayPath =
      ratToReal ((9 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss62 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 62 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss63 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 63 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss64 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 64 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss65 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 65 replayPath =
      ratToReal ((529 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss66 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 66 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss67 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 67 replayPath =
      ratToReal ((1 : Rat) / 1600) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss68 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 68 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss69 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 69 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss70 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 70 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss71 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 71 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss72 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 72 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss73 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 73 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss74 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 74 replayPath =
      ratToReal ((49 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss75 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 75 replayPath =
      ratToReal ((4 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss76 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 76 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss77 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 77 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss78 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 78 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss79 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 79 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss80 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 80 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss81 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 81 replayPath =
      ratToReal ((1 : Rat) / 4) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss82 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 82 replayPath =
      ratToReal ((4 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss83 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 83 replayPath =
      ratToReal ((1 : Rat) / 16) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss84 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 84 replayPath =
      ratToReal ((9 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss85 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 85 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss86 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 86 replayPath =
      ratToReal ((3721 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss87 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 87 replayPath =
      ratToReal ((49 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss88 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 88 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss89 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 89 replayPath =
      ratToReal ((9 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss90 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 90 replayPath =
      ratToReal ((49 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss91 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 91 replayPath =
      ratToReal ((169 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss92 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 92 replayPath =
      ratToReal ((4 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss93 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 93 replayPath =
      ratToReal ((9 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss94 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 94 replayPath =
      ratToReal ((289 : Rat) / 1600) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss95 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 95 replayPath =
      ratToReal ((1 : Rat) / 16) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss96 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 96 replayPath =
      ratToReal ((289 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss97 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 97 replayPath =
      ratToReal ((9 : Rat) / 16) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss98 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 98 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss99 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 99 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss100 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 100 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss101 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 101 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss102 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 102 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss103 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 103 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss104 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 104 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss105 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 105 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss106 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 106 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss107 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 107 replayPath =
      ratToReal ((49 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss108 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 108 replayPath =
      ratToReal ((49 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss109 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 109 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss110 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 110 replayPath =
      ratToReal ((81 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss111 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 111 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss112 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 112 replayPath =
      ratToReal ((4 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss113 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 113 replayPath =
      ratToReal ((1 : Rat) / 4) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss114 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 114 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss115 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 115 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss116 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 116 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss117 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 117 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss118 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 118 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss119 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 119 replayPath =
      ratToReal ((289 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss120 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 120 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss121 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 121 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss122 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 122 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss123 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 123 replayPath =
      ratToReal ((49 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss124 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 124 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss125 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 125 replayPath =
      ratToReal ((1 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss126 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 126 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss127 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 127 replayPath =
      ratToReal ((289 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss128 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 128 replayPath =
      ratToReal ((121 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss129 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 129 replayPath =
      ratToReal ((4 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss130 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 130 replayPath =
      ratToReal ((361 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss131 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 131 replayPath =
      ratToReal ((4 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss132 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 132 replayPath =
      ratToReal ((361 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss133 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 133 replayPath =
      ratToReal ((9 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss134 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 134 replayPath =
      ratToReal ((9 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss135 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 135 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss136 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 136 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss137 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 137 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss138 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 138 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss139 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 139 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss140 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 140 replayPath =
      ratToReal ((1 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss141 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 141 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss142 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 142 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss143 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 143 replayPath =
      ratToReal ((1 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss144 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 144 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss145 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 145 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss146 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 146 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss147 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 147 replayPath =
      ratToReal ((9 : Rat) / 2500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss148 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 148 replayPath =
      ratToReal ((4 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss149 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 149 replayPath =
      ratToReal ((9 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss150 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 150 replayPath =
      ratToReal ((1 : Rat) / 25) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss151 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 151 replayPath =
      ratToReal ((729 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss152 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 152 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss153 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 153 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss154 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 154 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss155 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 155 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss156 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 156 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss157 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 157 replayPath =
      ratToReal ((169 : Rat) / 40000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss158 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 158 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss159 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 159 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss160 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 160 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss161 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 161 replayPath =
      ratToReal ((1 : Rat) / 625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss162 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 162 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss163 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 163 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss164 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 164 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss165 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 165 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss166 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 166 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss167 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 167 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss168 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 168 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss169 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 169 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss170 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 170 replayPath =
      ratToReal (0 : Rat) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss171 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 171 replayPath =
      ratToReal ((9 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss172 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 172 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss173 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 173 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLoss174 :
    observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) 174 replayPath =
      ratToReal ((1 : Rat) / 400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    finalConsensusMedianPredictionsQ]

theorem observedFinalConsensusMedianLossPrefix0 :
    (∑ i ∈ Finset.range 0, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) = ratToReal 0 := by
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix1 :
    (∑ i ∈ Finset.range 1, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((1 : Rat) / 100) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix0,
    observedFinalConsensusMedianLoss0]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix2 :
    (∑ i ∈ Finset.range 2, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((97 : Rat) / 1250) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix1,
    observedFinalConsensusMedianLoss1]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix3 :
    (∑ i ∈ Finset.range 3, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((2001 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix2,
    observedFinalConsensusMedianLoss2]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix4 :
    (∑ i ∈ Finset.range 4, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((1013 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix3,
    observedFinalConsensusMedianLoss3]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix5 :
    (∑ i ∈ Finset.range 5, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((2051 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix4,
    observedFinalConsensusMedianLoss4]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix6 :
    (∑ i ∈ Finset.range 6, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103 : Rat) / 500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix5,
    observedFinalConsensusMedianLoss5]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix7 :
    (∑ i ∈ Finset.range 7, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((129 : Rat) / 625) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix6,
    observedFinalConsensusMedianLoss6]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix8 :
    (∑ i ∈ Finset.range 8, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((541 : Rat) / 2500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix7,
    observedFinalConsensusMedianLoss7]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix9 :
    (∑ i ∈ Finset.range 9, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((7789 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix8,
    observedFinalConsensusMedianLoss8]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix10 :
    (∑ i ∈ Finset.range 10, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((7889 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix9,
    observedFinalConsensusMedianLoss9]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix11 :
    (∑ i ∈ Finset.range 11, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((8289 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix10,
    observedFinalConsensusMedianLoss10]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix12 :
    (∑ i ∈ Finset.range 12, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((13189 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix11,
    observedFinalConsensusMedianLoss11]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix13 :
    (∑ i ∈ Finset.range 13, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((52877 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix12,
    observedFinalConsensusMedianLoss12]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix14 :
    (∑ i ∈ Finset.range 14, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((52977 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix13,
    observedFinalConsensusMedianLoss13]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix15 :
    (∑ i ∈ Finset.range 15, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((56577 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix14,
    observedFinalConsensusMedianLoss14]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix16 :
    (∑ i ∈ Finset.range 16, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((56977 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix15,
    observedFinalConsensusMedianLoss15]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix17 :
    (∑ i ∈ Finset.range 17, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((57041 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix16,
    observedFinalConsensusMedianLoss16]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix18 :
    (∑ i ∈ Finset.range 18, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((57441 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix17,
    observedFinalConsensusMedianLoss17]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix19 :
    (∑ i ∈ Finset.range 19, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((57841 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix18,
    observedFinalConsensusMedianLoss18]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix20 :
    (∑ i ∈ Finset.range 20, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((57857 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix19,
    observedFinalConsensusMedianLoss19]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix21 :
    (∑ i ∈ Finset.range 21, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((57857 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix20,
    observedFinalConsensusMedianLoss20]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix22 :
    (∑ i ∈ Finset.range 22, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((66321 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix21,
    observedFinalConsensusMedianLoss21]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix23 :
    (∑ i ∈ Finset.range 23, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((66421 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix22,
    observedFinalConsensusMedianLoss22]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix24 :
    (∑ i ∈ Finset.range 24, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((71321 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix23,
    observedFinalConsensusMedianLoss23]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix25 :
    (∑ i ∈ Finset.range 25, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35701 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix24,
    observedFinalConsensusMedianLoss24]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix26 :
    (∑ i ∈ Finset.range 26, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35751 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix25,
    observedFinalConsensusMedianLoss25]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix27 :
    (∑ i ∈ Finset.range 27, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35801 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix26,
    observedFinalConsensusMedianLoss26]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix28 :
    (∑ i ∈ Finset.range 28, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((71651 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix27,
    observedFinalConsensusMedianLoss27]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix29 :
    (∑ i ∈ Finset.range 29, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((72051 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix28,
    observedFinalConsensusMedianLoss28]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix30 :
    (∑ i ∈ Finset.range 30, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((14423 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix29,
    observedFinalConsensusMedianLoss29]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix31 :
    (∑ i ∈ Finset.range 31, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((14503 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix30,
    observedFinalConsensusMedianLoss30]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix32 :
    (∑ i ∈ Finset.range 32, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((14523 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix31,
    observedFinalConsensusMedianLoss31]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix33 :
    (∑ i ∈ Finset.range 33, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((14603 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix32,
    observedFinalConsensusMedianLoss32]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix34 :
    (∑ i ∈ Finset.range 34, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((4571 : Rat) / 2500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix33,
    observedFinalConsensusMedianLoss33]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix35 :
    (∑ i ∈ Finset.range 35, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((18309 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix34,
    observedFinalConsensusMedianLoss34]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix36 :
    (∑ i ∈ Finset.range 36, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((18409 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix35,
    observedFinalConsensusMedianLoss35]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix37 :
    (∑ i ∈ Finset.range 37, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((18509 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix36,
    observedFinalConsensusMedianLoss36]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix38 :
    (∑ i ∈ Finset.range 38, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((18993 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix37,
    observedFinalConsensusMedianLoss37]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix39 :
    (∑ i ∈ Finset.range 39, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((25393 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix38,
    observedFinalConsensusMedianLoss38]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix40 :
    (∑ i ∈ Finset.range 40, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((12709 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix39,
    observedFinalConsensusMedianLoss39]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix41 :
    (∑ i ∈ Finset.range 41, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((25419 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix40,
    observedFinalConsensusMedianLoss40]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix42 :
    (∑ i ∈ Finset.range 42, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((1271 : Rat) / 500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix41,
    observedFinalConsensusMedianLoss41]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix43 :
    (∑ i ∈ Finset.range 43, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((5089 : Rat) / 2000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix42,
    observedFinalConsensusMedianLoss42]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix44 :
    (∑ i ∈ Finset.range 44, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((12747 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix43,
    observedFinalConsensusMedianLoss43]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix45 :
    (∑ i ∈ Finset.range 45, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((12797 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix44,
    observedFinalConsensusMedianLoss44]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix46 :
    (∑ i ∈ Finset.range 46, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((25619 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix45,
    observedFinalConsensusMedianLoss45]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix47 :
    (∑ i ∈ Finset.range 47, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((6407 : Rat) / 2500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix46,
    observedFinalConsensusMedianLoss46]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix48 :
    (∑ i ∈ Finset.range 48, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((25653 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix47,
    observedFinalConsensusMedianLoss47]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix49 :
    (∑ i ∈ Finset.range 49, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((12839 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix48,
    observedFinalConsensusMedianLoss48]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix50 :
    (∑ i ∈ Finset.range 50, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((102937 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix49,
    observedFinalConsensusMedianLoss49]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix51 :
    (∑ i ∈ Finset.range 51, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((102953 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix50,
    observedFinalConsensusMedianLoss50]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix52 :
    (∑ i ∈ Finset.range 52, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103053 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix51,
    observedFinalConsensusMedianLoss51]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix53 :
    (∑ i ∈ Finset.range 53, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103057 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix52,
    observedFinalConsensusMedianLoss52]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix54 :
    (∑ i ∈ Finset.range 54, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103157 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix53,
    observedFinalConsensusMedianLoss53]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix55 :
    (∑ i ∈ Finset.range 55, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103257 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix54,
    observedFinalConsensusMedianLoss54]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix56 :
    (∑ i ∈ Finset.range 56, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103261 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix55,
    observedFinalConsensusMedianLoss55]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix57 :
    (∑ i ∈ Finset.range 57, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103297 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix56,
    observedFinalConsensusMedianLoss56]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix58 :
    (∑ i ∈ Finset.range 58, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103397 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix57,
    observedFinalConsensusMedianLoss57]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix59 :
    (∑ i ∈ Finset.range 59, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103401 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix58,
    observedFinalConsensusMedianLoss58]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix60 :
    (∑ i ∈ Finset.range 60, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103501 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix59,
    observedFinalConsensusMedianLoss59]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix61 :
    (∑ i ∈ Finset.range 61, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((103601 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix60,
    observedFinalConsensusMedianLoss60]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix62 :
    (∑ i ∈ Finset.range 62, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((104501 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix61,
    observedFinalConsensusMedianLoss61]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix63 :
    (∑ i ∈ Finset.range 63, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((104601 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix62,
    observedFinalConsensusMedianLoss62]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix64 :
    (∑ i ∈ Finset.range 64, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((104701 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix63,
    observedFinalConsensusMedianLoss63]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix65 :
    (∑ i ∈ Finset.range 65, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((105101 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix64,
    observedFinalConsensusMedianLoss64]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix66 :
    (∑ i ∈ Finset.range 66, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((10563 : Rat) / 4000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix65,
    observedFinalConsensusMedianLoss65]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix67 :
    (∑ i ∈ Finset.range 67, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((10723 : Rat) / 4000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix66,
    observedFinalConsensusMedianLoss66]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix68 :
    (∑ i ∈ Finset.range 68, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21451 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix67,
    observedFinalConsensusMedianLoss67]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix69 :
    (∑ i ∈ Finset.range 69, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21471 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix68,
    observedFinalConsensusMedianLoss68]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix70 :
    (∑ i ∈ Finset.range 70, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21791 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix69,
    observedFinalConsensusMedianLoss69]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix71 :
    (∑ i ∈ Finset.range 71, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21811 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix70,
    observedFinalConsensusMedianLoss70]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix72 :
    (∑ i ∈ Finset.range 72, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21831 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix71,
    observedFinalConsensusMedianLoss71]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix73 :
    (∑ i ∈ Finset.range 73, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21851 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix72,
    observedFinalConsensusMedianLoss72]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix74 :
    (∑ i ∈ Finset.range 74, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((109259 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix73,
    observedFinalConsensusMedianLoss73]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix75 :
    (∑ i ∈ Finset.range 75, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21891 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix74,
    observedFinalConsensusMedianLoss74]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix76 :
    (∑ i ∈ Finset.range 76, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((109711 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix75,
    observedFinalConsensusMedianLoss75]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix77 :
    (∑ i ∈ Finset.range 77, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((109811 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix76,
    observedFinalConsensusMedianLoss76]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix78 :
    (∑ i ∈ Finset.range 78, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((110211 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix77,
    observedFinalConsensusMedianLoss77]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix79 :
    (∑ i ∈ Finset.range 79, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((110611 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix78,
    observedFinalConsensusMedianLoss78]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix80 :
    (∑ i ∈ Finset.range 80, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((111011 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix79,
    observedFinalConsensusMedianLoss79]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix81 :
    (∑ i ∈ Finset.range 81, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((112611 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix80,
    observedFinalConsensusMedianLoss80]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix82 :
    (∑ i ∈ Finset.range 82, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((122611 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix81,
    observedFinalConsensusMedianLoss81]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix83 :
    (∑ i ∈ Finset.range 83, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((129011 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix82,
    observedFinalConsensusMedianLoss82]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix84 :
    (∑ i ∈ Finset.range 84, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((131511 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix83,
    observedFinalConsensusMedianLoss83]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix85 :
    (∑ i ∈ Finset.range 85, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((135111 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix84,
    observedFinalConsensusMedianLoss84]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix86 :
    (∑ i ∈ Finset.range 86, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((136711 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix85,
    observedFinalConsensusMedianLoss85]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix87 :
    (∑ i ∈ Finset.range 87, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((8777 : Rat) / 2500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix86,
    observedFinalConsensusMedianLoss86]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix88 :
    (∑ i ∈ Finset.range 88, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((4413 : Rat) / 1250) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix87,
    observedFinalConsensusMedianLoss87]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix89 :
    (∑ i ∈ Finset.range 89, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((4463 : Rat) / 1250) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix88,
    observedFinalConsensusMedianLoss88]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix90 :
    (∑ i ∈ Finset.range 90, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((9151 : Rat) / 2500) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix89,
    observedFinalConsensusMedianLoss89]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix91 :
    (∑ i ∈ Finset.range 91, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((37829 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix90,
    observedFinalConsensusMedianLoss90]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix92 :
    (∑ i ∈ Finset.range 92, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21027 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix91,
    observedFinalConsensusMedianLoss91]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix93 :
    (∑ i ∈ Finset.range 93, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((21827 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix92,
    observedFinalConsensusMedianLoss92]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix94 :
    (∑ i ∈ Finset.range 94, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((23627 : Rat) / 5000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix93,
    observedFinalConsensusMedianLoss93]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix95 :
    (∑ i ∈ Finset.range 95, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((196241 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix94,
    observedFinalConsensusMedianLoss94]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix96 :
    (∑ i ∈ Finset.range 96, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((198741 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix95,
    observedFinalConsensusMedianLoss95]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix97 :
    (∑ i ∈ Finset.range 97, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((40673 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix96,
    observedFinalConsensusMedianLoss96]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix98 :
    (∑ i ∈ Finset.range 98, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((45173 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix97,
    observedFinalConsensusMedianLoss97]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix99 :
    (∑ i ∈ Finset.range 99, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((45493 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix98,
    observedFinalConsensusMedianLoss98]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix100 :
    (∑ i ∈ Finset.range 100, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((45573 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix99,
    observedFinalConsensusMedianLoss99]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix101 :
    (∑ i ∈ Finset.range 101, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((45593 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix100,
    observedFinalConsensusMedianLoss100]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix102 :
    (∑ i ∈ Finset.range 102, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((45673 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix101,
    observedFinalConsensusMedianLoss101]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix103 :
    (∑ i ∈ Finset.range 103, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((228401 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix102,
    observedFinalConsensusMedianLoss102]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix104 :
    (∑ i ∈ Finset.range 104, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((228801 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix103,
    observedFinalConsensusMedianLoss103]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix105 :
    (∑ i ∈ Finset.range 105, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((229201 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix104,
    observedFinalConsensusMedianLoss104]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix106 :
    (∑ i ∈ Finset.range 106, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((229601 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix105,
    observedFinalConsensusMedianLoss105]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix107 :
    (∑ i ∈ Finset.range 107, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((230001 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix106,
    observedFinalConsensusMedianLoss106]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix108 :
    (∑ i ∈ Finset.range 108, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((230197 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix107,
    observedFinalConsensusMedianLoss107]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix109 :
    (∑ i ∈ Finset.range 109, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((230981 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix108,
    observedFinalConsensusMedianLoss108]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix110 :
    (∑ i ∈ Finset.range 110, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((232581 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix109,
    observedFinalConsensusMedianLoss109]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix111 :
    (∑ i ∈ Finset.range 111, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((233877 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix110,
    observedFinalConsensusMedianLoss110]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix112 :
    (∑ i ∈ Finset.range 112, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((233913 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix111,
    observedFinalConsensusMedianLoss111]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix113 :
    (∑ i ∈ Finset.range 113, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((240313 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix112,
    observedFinalConsensusMedianLoss112]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix114 :
    (∑ i ∈ Finset.range 114, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((250313 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix113,
    observedFinalConsensusMedianLoss113]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix115 :
    (∑ i ∈ Finset.range 115, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((250413 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix114,
    observedFinalConsensusMedianLoss114]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix116 :
    (∑ i ∈ Finset.range 116, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((250813 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix115,
    observedFinalConsensusMedianLoss115]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix117 :
    (∑ i ∈ Finset.range 117, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((250913 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix116,
    observedFinalConsensusMedianLoss116]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix118 :
    (∑ i ∈ Finset.range 118, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((251313 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix117,
    observedFinalConsensusMedianLoss117]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix119 :
    (∑ i ∈ Finset.range 119, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((252913 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix118,
    observedFinalConsensusMedianLoss118]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix120 :
    (∑ i ∈ Finset.range 120, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((281813 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix119,
    observedFinalConsensusMedianLoss119]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix121 :
    (∑ i ∈ Finset.range 121, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((282213 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix120,
    observedFinalConsensusMedianLoss120]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix122 :
    (∑ i ∈ Finset.range 122, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((283813 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix121,
    observedFinalConsensusMedianLoss121]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix123 :
    (∑ i ∈ Finset.range 123, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((283913 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix122,
    observedFinalConsensusMedianLoss122]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix124 :
    (∑ i ∈ Finset.range 124, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((303513 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix123,
    observedFinalConsensusMedianLoss123]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix125 :
    (∑ i ∈ Finset.range 125, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((303613 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix124,
    observedFinalConsensusMedianLoss124]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix126 :
    (∑ i ∈ Finset.range 126, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((303629 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix125,
    observedFinalConsensusMedianLoss125]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix127 :
    (∑ i ∈ Finset.range 127, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((305229 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix126,
    observedFinalConsensusMedianLoss126]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix128 :
    (∑ i ∈ Finset.range 128, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((309853 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix127,
    observedFinalConsensusMedianLoss127]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix129 :
    (∑ i ∈ Finset.range 129, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((317597 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix128,
    observedFinalConsensusMedianLoss128]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix130 :
    (∑ i ∈ Finset.range 130, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((323997 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix129,
    observedFinalConsensusMedianLoss129]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix131 :
    (∑ i ∈ Finset.range 131, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((325441 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix130,
    observedFinalConsensusMedianLoss130]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix132 :
    (∑ i ∈ Finset.range 132, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((331841 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix131,
    observedFinalConsensusMedianLoss131]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix133 :
    (∑ i ∈ Finset.range 133, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((337617 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix132,
    observedFinalConsensusMedianLoss132]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix134 :
    (∑ i ∈ Finset.range 134, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((338517 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix133,
    observedFinalConsensusMedianLoss133]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix135 :
    (∑ i ∈ Finset.range 135, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((339093 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix134,
    observedFinalConsensusMedianLoss134]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix136 :
    (∑ i ∈ Finset.range 136, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((339493 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix135,
    observedFinalConsensusMedianLoss135]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix137 :
    (∑ i ∈ Finset.range 137, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((339893 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix136,
    observedFinalConsensusMedianLoss136]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix138 :
    (∑ i ∈ Finset.range 138, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((341493 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix137,
    observedFinalConsensusMedianLoss137]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix139 :
    (∑ i ∈ Finset.range 139, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((341893 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix138,
    observedFinalConsensusMedianLoss138]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix140 :
    (∑ i ∈ Finset.range 140, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((341993 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix139,
    observedFinalConsensusMedianLoss139]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix141 :
    (∑ i ∈ Finset.range 141, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((342009 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix140,
    observedFinalConsensusMedianLoss140]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix142 :
    (∑ i ∈ Finset.range 142, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68409 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix141,
    observedFinalConsensusMedianLoss141]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix143 :
    (∑ i ∈ Finset.range 143, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68429 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix142,
    observedFinalConsensusMedianLoss142]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix144 :
    (∑ i ∈ Finset.range 144, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((342161 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix143,
    observedFinalConsensusMedianLoss143]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix145 :
    (∑ i ∈ Finset.range 145, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68433 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix144,
    observedFinalConsensusMedianLoss144]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix146 :
    (∑ i ∈ Finset.range 146, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68513 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix145,
    observedFinalConsensusMedianLoss145]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix147 :
    (∑ i ∈ Finset.range 147, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68533 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix146,
    observedFinalConsensusMedianLoss146]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix148 :
    (∑ i ∈ Finset.range 148, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((342809 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix147,
    observedFinalConsensusMedianLoss147]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix149 :
    (∑ i ∈ Finset.range 149, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68613 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix148,
    observedFinalConsensusMedianLoss148]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix150 :
    (∑ i ∈ Finset.range 150, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((68793 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix149,
    observedFinalConsensusMedianLoss149]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix151 :
    (∑ i ∈ Finset.range 151, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((69113 : Rat) / 8000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix150,
    observedFinalConsensusMedianLoss150]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix152 :
    (∑ i ∈ Finset.range 152, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((348481 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix151,
    observedFinalConsensusMedianLoss151]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix153 :
    (∑ i ∈ Finset.range 153, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((348581 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix152,
    observedFinalConsensusMedianLoss152]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix154 :
    (∑ i ∈ Finset.range 154, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((348981 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix153,
    observedFinalConsensusMedianLoss153]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix155 :
    (∑ i ∈ Finset.range 155, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((349381 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix154,
    observedFinalConsensusMedianLoss154]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix156 :
    (∑ i ∈ Finset.range 156, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((349781 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix155,
    observedFinalConsensusMedianLoss155]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix157 :
    (∑ i ∈ Finset.range 157, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((350181 : Rat) / 40000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix156,
    observedFinalConsensusMedianLoss156]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix158 :
    (∑ i ∈ Finset.range 158, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((7007 : Rat) / 800) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix157,
    observedFinalConsensusMedianLoss157]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix159 :
    (∑ i ∈ Finset.range 159, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((7009 : Rat) / 800) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix158,
    observedFinalConsensusMedianLoss158]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix160 :
    (∑ i ∈ Finset.range 160, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((7011 : Rat) / 800) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix159,
    observedFinalConsensusMedianLoss159]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix161 :
    (∑ i ∈ Finset.range 161, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((7019 : Rat) / 800) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix160,
    observedFinalConsensusMedianLoss160]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix162 :
    (∑ i ∈ Finset.range 162, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((175507 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix161,
    observedFinalConsensusMedianLoss161]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix163 :
    (∑ i ∈ Finset.range 163, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((175707 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix162,
    observedFinalConsensusMedianLoss162]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix164 :
    (∑ i ∈ Finset.range 164, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((175709 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix163,
    observedFinalConsensusMedianLoss163]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix165 :
    (∑ i ∈ Finset.range 165, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((175711 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix164,
    observedFinalConsensusMedianLoss164]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix166 :
    (∑ i ∈ Finset.range 166, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((175911 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix165,
    observedFinalConsensusMedianLoss165]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix167 :
    (∑ i ∈ Finset.range 167, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((175913 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix166,
    observedFinalConsensusMedianLoss166]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix168 :
    (∑ i ∈ Finset.range 168, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35183 : Rat) / 4000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix167,
    observedFinalConsensusMedianLoss167]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix169 :
    (∑ i ∈ Finset.range 169, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35193 : Rat) / 4000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix168,
    observedFinalConsensusMedianLoss168]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix170 :
    (∑ i ∈ Finset.range 170, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35203 : Rat) / 4000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix169,
    observedFinalConsensusMedianLoss169]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix171 :
    (∑ i ∈ Finset.range 171, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((35203 : Rat) / 4000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix170,
    observedFinalConsensusMedianLoss170]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix172 :
    (∑ i ∈ Finset.range 172, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((176033 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix171,
    observedFinalConsensusMedianLoss171]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix173 :
    (∑ i ∈ Finset.range 173, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((176083 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix172,
    observedFinalConsensusMedianLoss172]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix174 :
    (∑ i ∈ Finset.range 174, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((176133 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix173,
    observedFinalConsensusMedianLoss173]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianLossPrefix175 :
    (∑ i ∈ Finset.range 175, observedTrajectoryScore
        (monitorBrierScore finalConsensusMedian) i replayPath) =
      ratToReal ((176183 : Rat) / 20000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianLossPrefix174,
    observedFinalConsensusMedianLoss174]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor0 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 0 replayPath =
      ratToReal ((1 : Rat) / 2) := by
  norm_num [forwardPredictorProcess, forwardPredictor, ratToReal]

theorem observedFinalConsensusMedianPredictor1 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 1 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix1]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor2 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 2 replayPath =
      ratToReal ((97 : Rat) / 2500) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix2]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor3 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 3 replayPath =
      ratToReal ((667 : Rat) / 10000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix3]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor4 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 4 replayPath =
      ratToReal ((1013 : Rat) / 20000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix4]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor5 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 5 replayPath =
      ratToReal ((2051 : Rat) / 50000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix5]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor6 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 6 replayPath =
      ratToReal ((103 : Rat) / 3000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix6]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor7 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 7 replayPath =
      ratToReal ((129 : Rat) / 4375) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix7]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor8 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 8 replayPath =
      ratToReal ((541 : Rat) / 20000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix8]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor9 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 9 replayPath =
      ratToReal ((7789 : Rat) / 90000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix9]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor10 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 10 replayPath =
      ratToReal ((7889 : Rat) / 100000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix10]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor11 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 11 replayPath =
      ratToReal ((8289 : Rat) / 110000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix11]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor12 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 12 replayPath =
      ratToReal ((13189 : Rat) / 120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix12]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor13 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 13 replayPath =
      ratToReal ((52877 : Rat) / 520000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix13]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor14 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 14 replayPath =
      ratToReal ((52977 : Rat) / 560000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix14]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor15 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 15 replayPath =
      ratToReal ((18859 : Rat) / 200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix15]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor16 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 16 replayPath =
      ratToReal ((56977 : Rat) / 640000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix16]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor17 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 17 replayPath =
      ratToReal ((57041 : Rat) / 680000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix17]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor18 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 18 replayPath =
      ratToReal ((19147 : Rat) / 240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix18]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor19 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 19 replayPath =
      ratToReal ((57841 : Rat) / 760000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix19]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor20 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 20 replayPath =
      ratToReal ((57857 : Rat) / 800000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix20]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor21 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 21 replayPath =
      ratToReal ((57857 : Rat) / 840000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix21]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor22 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 22 replayPath =
      ratToReal ((66321 : Rat) / 880000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix22]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor23 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 23 replayPath =
      ratToReal ((66421 : Rat) / 920000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix23]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor24 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 24 replayPath =
      ratToReal ((71321 : Rat) / 960000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix24]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor25 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 25 replayPath =
      ratToReal ((35701 : Rat) / 500000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix25]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor26 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 26 replayPath =
      ratToReal ((35751 : Rat) / 520000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix26]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor27 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 27 replayPath =
      ratToReal ((35801 : Rat) / 540000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix27]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor28 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 28 replayPath =
      ratToReal ((71651 : Rat) / 1120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix28]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor29 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 29 replayPath =
      ratToReal ((72051 : Rat) / 1160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix29]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor30 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 30 replayPath =
      ratToReal ((14423 : Rat) / 240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix30]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor31 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 31 replayPath =
      ratToReal ((14503 : Rat) / 248000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix31]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor32 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 32 replayPath =
      ratToReal ((14523 : Rat) / 256000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix32]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor33 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 33 replayPath =
      ratToReal ((14603 : Rat) / 264000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix33]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor34 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 34 replayPath =
      ratToReal ((4571 : Rat) / 85000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix34]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor35 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 35 replayPath =
      ratToReal ((18309 : Rat) / 350000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix35]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor36 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 36 replayPath =
      ratToReal ((18409 : Rat) / 360000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix36]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor37 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 37 replayPath =
      ratToReal ((18509 : Rat) / 370000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix37]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor38 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 38 replayPath =
      ratToReal ((18993 : Rat) / 380000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix38]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor39 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 39 replayPath =
      ratToReal ((25393 : Rat) / 390000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix39]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor40 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 40 replayPath =
      ratToReal ((12709 : Rat) / 200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix40]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor41 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 41 replayPath =
      ratToReal ((25419 : Rat) / 410000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix41]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor42 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 42 replayPath =
      ratToReal ((1271 : Rat) / 21000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix42]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor43 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 43 replayPath =
      ratToReal ((5089 : Rat) / 86000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix43]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor44 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 44 replayPath =
      ratToReal ((12747 : Rat) / 220000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix44]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor45 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 45 replayPath =
      ratToReal ((12797 : Rat) / 225000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix45]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor46 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 46 replayPath =
      ratToReal ((25619 : Rat) / 460000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix46]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor47 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 47 replayPath =
      ratToReal ((6407 : Rat) / 117500) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix47]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor48 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 48 replayPath =
      ratToReal ((8551 : Rat) / 160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix48]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor49 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 49 replayPath =
      ratToReal ((12839 : Rat) / 245000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix49]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor50 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 50 replayPath =
      ratToReal ((102937 : Rat) / 2000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix50]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor51 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 51 replayPath =
      ratToReal ((102953 : Rat) / 2040000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix51]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor52 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 52 replayPath =
      ratToReal ((103053 : Rat) / 2080000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix52]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor53 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 53 replayPath =
      ratToReal ((103057 : Rat) / 2120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix53]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor54 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 54 replayPath =
      ratToReal ((103157 : Rat) / 2160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix54]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor55 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 55 replayPath =
      ratToReal ((9387 : Rat) / 200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix55]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor56 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 56 replayPath =
      ratToReal ((103261 : Rat) / 2240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix56]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor57 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 57 replayPath =
      ratToReal ((103297 : Rat) / 2280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix57]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor58 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 58 replayPath =
      ratToReal ((103397 : Rat) / 2320000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix58]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor59 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 59 replayPath =
      ratToReal ((103401 : Rat) / 2360000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix59]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor60 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 60 replayPath =
      ratToReal ((103501 : Rat) / 2400000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix60]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor61 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 61 replayPath =
      ratToReal ((103601 : Rat) / 2440000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix61]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor62 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 62 replayPath =
      ratToReal ((3371 : Rat) / 80000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix62]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor63 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 63 replayPath =
      ratToReal ((4981 : Rat) / 120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix63]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor64 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 64 replayPath =
      ratToReal ((104701 : Rat) / 2560000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix64]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor65 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 65 replayPath =
      ratToReal ((105101 : Rat) / 2600000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix65]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor66 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 66 replayPath =
      ratToReal ((3521 : Rat) / 88000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix66]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor67 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 67 replayPath =
      ratToReal ((10723 : Rat) / 268000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix67]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor68 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 68 replayPath =
      ratToReal ((21451 : Rat) / 544000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix68]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor69 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 69 replayPath =
      ratToReal ((7157 : Rat) / 184000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix69]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor70 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 70 replayPath =
      ratToReal ((3113 : Rat) / 80000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix70]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor71 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 71 replayPath =
      ratToReal ((21811 : Rat) / 568000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix71]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor72 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 72 replayPath =
      ratToReal ((7277 : Rat) / 192000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix72]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor73 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 73 replayPath =
      ratToReal ((21851 : Rat) / 584000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix73]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor74 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 74 replayPath =
      ratToReal ((109259 : Rat) / 2960000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix74]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor75 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 75 replayPath =
      ratToReal ((7297 : Rat) / 200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix75]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor76 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 76 replayPath =
      ratToReal ((109711 : Rat) / 3040000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix76]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor77 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 77 replayPath =
      ratToReal ((109811 : Rat) / 3080000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix77]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor78 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 78 replayPath =
      ratToReal ((36737 : Rat) / 1040000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix78]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor79 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 79 replayPath =
      ratToReal ((110611 : Rat) / 3160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix79]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor80 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 80 replayPath =
      ratToReal ((111011 : Rat) / 3200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix80]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor81 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 81 replayPath =
      ratToReal ((37537 : Rat) / 1080000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix81]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor82 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 82 replayPath =
      ratToReal ((122611 : Rat) / 3280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix82]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor83 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 83 replayPath =
      ratToReal ((129011 : Rat) / 3320000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix83]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor84 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 84 replayPath =
      ratToReal ((43837 : Rat) / 1120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix84]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor85 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 85 replayPath =
      ratToReal ((135111 : Rat) / 3400000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix85]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor86 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 86 replayPath =
      ratToReal ((136711 : Rat) / 3440000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix86]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor87 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 87 replayPath =
      ratToReal ((8777 : Rat) / 217500) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix87]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor88 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 88 replayPath =
      ratToReal ((4413 : Rat) / 110000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix88]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor89 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 89 replayPath =
      ratToReal ((4463 : Rat) / 111250) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix89]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor90 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 90 replayPath =
      ratToReal ((9151 : Rat) / 225000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix90]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor91 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 91 replayPath =
      ratToReal ((37829 : Rat) / 910000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix91]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor92 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 92 replayPath =
      ratToReal ((21027 : Rat) / 460000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix92]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor93 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 93 replayPath =
      ratToReal ((21827 : Rat) / 465000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix93]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor94 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 94 replayPath =
      ratToReal ((23627 : Rat) / 470000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix94]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor95 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 95 replayPath =
      ratToReal ((196241 : Rat) / 3800000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix95]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor96 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 96 replayPath =
      ratToReal ((66247 : Rat) / 1280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix96]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor97 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 97 replayPath =
      ratToReal ((40673 : Rat) / 776000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix97]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor98 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 98 replayPath =
      ratToReal ((45173 : Rat) / 784000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix98]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor99 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 99 replayPath =
      ratToReal ((45493 : Rat) / 792000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix99]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor100 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 100 replayPath =
      ratToReal ((45573 : Rat) / 800000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix100]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor101 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 101 replayPath =
      ratToReal ((45593 : Rat) / 808000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix101]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor102 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 102 replayPath =
      ratToReal ((45673 : Rat) / 816000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix102]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor103 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 103 replayPath =
      ratToReal ((228401 : Rat) / 4120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix103]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor104 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 104 replayPath =
      ratToReal ((228801 : Rat) / 4160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix104]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor105 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 105 replayPath =
      ratToReal ((32743 : Rat) / 600000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix105]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor106 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 106 replayPath =
      ratToReal ((229601 : Rat) / 4240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix106]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor107 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 107 replayPath =
      ratToReal ((230001 : Rat) / 4280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix107]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor108 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 108 replayPath =
      ratToReal ((230197 : Rat) / 4320000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix108]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor109 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 109 replayPath =
      ratToReal ((230981 : Rat) / 4360000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix109]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor110 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 110 replayPath =
      ratToReal ((232581 : Rat) / 4400000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix110]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor111 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 111 replayPath =
      ratToReal ((2107 : Rat) / 40000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix111]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor112 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 112 replayPath =
      ratToReal ((233913 : Rat) / 4480000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix112]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor113 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 113 replayPath =
      ratToReal ((240313 : Rat) / 4520000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix113]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor114 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 114 replayPath =
      ratToReal ((250313 : Rat) / 4560000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix114]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor115 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 115 replayPath =
      ratToReal ((250413 : Rat) / 4600000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix115]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor116 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 116 replayPath =
      ratToReal ((250813 : Rat) / 4640000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix116]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor117 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 117 replayPath =
      ratToReal ((19301 : Rat) / 360000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix117]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor118 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 118 replayPath =
      ratToReal ((251313 : Rat) / 4720000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix118]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor119 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 119 replayPath =
      ratToReal ((252913 : Rat) / 4760000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix119]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor120 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 120 replayPath =
      ratToReal ((281813 : Rat) / 4800000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix120]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor121 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 121 replayPath =
      ratToReal ((282213 : Rat) / 4840000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix121]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor122 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 122 replayPath =
      ratToReal ((283813 : Rat) / 4880000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix122]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor123 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 123 replayPath =
      ratToReal ((283913 : Rat) / 4920000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix123]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor124 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 124 replayPath =
      ratToReal ((303513 : Rat) / 4960000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix124]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor125 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 125 replayPath =
      ratToReal ((303613 : Rat) / 5000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix125]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor126 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 126 replayPath =
      ratToReal ((303629 : Rat) / 5040000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix126]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor127 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 127 replayPath =
      ratToReal ((305229 : Rat) / 5080000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix127]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor128 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 128 replayPath =
      ratToReal ((309853 : Rat) / 5120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix128]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor129 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 129 replayPath =
      ratToReal ((317597 : Rat) / 5160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix129]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor130 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 130 replayPath =
      ratToReal ((323997 : Rat) / 5200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix130]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor131 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 131 replayPath =
      ratToReal ((325441 : Rat) / 5240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix131]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor132 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 132 replayPath =
      ratToReal ((331841 : Rat) / 5280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix132]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor133 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 133 replayPath =
      ratToReal ((48231 : Rat) / 760000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix133]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor134 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 134 replayPath =
      ratToReal ((338517 : Rat) / 5360000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix134]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor135 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 135 replayPath =
      ratToReal ((12559 : Rat) / 200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix135]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor136 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 136 replayPath =
      ratToReal ((339493 : Rat) / 5440000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix136]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor137 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 137 replayPath =
      ratToReal ((339893 : Rat) / 5480000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix137]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor138 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 138 replayPath =
      ratToReal ((113831 : Rat) / 1840000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix138]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor139 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 139 replayPath =
      ratToReal ((341893 : Rat) / 5560000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix139]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor140 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 140 replayPath =
      ratToReal ((341993 : Rat) / 5600000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix140]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor141 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 141 replayPath =
      ratToReal ((114003 : Rat) / 1880000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix141]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor142 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 142 replayPath =
      ratToReal ((68409 : Rat) / 1136000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix142]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor143 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 143 replayPath =
      ratToReal ((68429 : Rat) / 1144000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix143]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor144 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 144 replayPath =
      ratToReal ((342161 : Rat) / 5760000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix144]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor145 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 145 replayPath =
      ratToReal ((68433 : Rat) / 1160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix145]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor146 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 146 replayPath =
      ratToReal ((68513 : Rat) / 1168000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix146]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor147 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 147 replayPath =
      ratToReal ((68533 : Rat) / 1176000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix147]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor148 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 148 replayPath =
      ratToReal ((342809 : Rat) / 5920000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix148]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor149 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 149 replayPath =
      ratToReal ((68613 : Rat) / 1192000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix149]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor150 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 150 replayPath =
      ratToReal ((22931 : Rat) / 400000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix150]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor151 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 151 replayPath =
      ratToReal ((69113 : Rat) / 1208000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix151]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor152 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 152 replayPath =
      ratToReal ((348481 : Rat) / 6080000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix152]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor153 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 153 replayPath =
      ratToReal ((348581 : Rat) / 6120000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix153]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor154 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 154 replayPath =
      ratToReal ((348981 : Rat) / 6160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix154]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor155 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 155 replayPath =
      ratToReal ((349381 : Rat) / 6200000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix155]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor156 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 156 replayPath =
      ratToReal ((349781 : Rat) / 6240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix156]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor157 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 157 replayPath =
      ratToReal ((350181 : Rat) / 6280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix157]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor158 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 158 replayPath =
      ratToReal ((7007 : Rat) / 126400) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix158]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor159 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 159 replayPath =
      ratToReal ((7009 : Rat) / 127200) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix159]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor160 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 160 replayPath =
      ratToReal ((7011 : Rat) / 128000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix160]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor161 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 161 replayPath =
      ratToReal ((7019 : Rat) / 128800) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix161]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor162 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 162 replayPath =
      ratToReal ((175507 : Rat) / 3240000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix162]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor163 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 163 replayPath =
      ratToReal ((175707 : Rat) / 3260000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix163]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor164 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 164 replayPath =
      ratToReal ((175709 : Rat) / 3280000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix164]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor165 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 165 replayPath =
      ratToReal ((175711 : Rat) / 3300000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix165]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor166 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 166 replayPath =
      ratToReal ((175911 : Rat) / 3320000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix166]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor167 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 167 replayPath =
      ratToReal ((175913 : Rat) / 3340000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix167]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor168 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 168 replayPath =
      ratToReal ((35183 : Rat) / 672000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix168]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor169 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 169 replayPath =
      ratToReal ((35193 : Rat) / 676000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix169]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor170 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 170 replayPath =
      ratToReal ((35203 : Rat) / 680000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix170]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor171 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 171 replayPath =
      ratToReal ((35203 : Rat) / 684000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix171]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor172 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 172 replayPath =
      ratToReal ((176033 : Rat) / 3440000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix172]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor173 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 173 replayPath =
      ratToReal ((176083 : Rat) / 3460000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix173]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianPredictor174 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian)) 174 replayPath =
      ratToReal ((58711 : Rat) / 1160000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFinalConsensusMedianLossPrefix174]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix0 :
    (∑ i ∈ Finset.range 0,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal 0 := by
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix1 :
    (∑ i ∈ Finset.range 1,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2401 : Rat) / 10000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix0,
    observedFinalConsensusMedianLoss0,
    observedFinalConsensusMedianPredictor0]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix2 :
    (∑ i ∈ Finset.range 2,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1521361 : Rat) / 6250000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix1,
    observedFinalConsensusMedianLoss1,
    observedFinalConsensusMedianPredictor1]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix3 :
    (∑ i ∈ Finset.range 3,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((5008469 : Rat) / 20000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix2,
    observedFinalConsensusMedianLoss2,
    observedFinalConsensusMedianPredictor2]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix4 :
    (∑ i ∈ Finset.range 4,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((25454509 : Rat) / 100000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix3,
    observedFinalConsensusMedianLoss3,
    observedFinalConsensusMedianPredictor3]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix5 :
    (∑ i ∈ Finset.range 5,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((20549081 : Rat) / 80000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix4,
    observedFinalConsensusMedianLoss4,
    observedFinalConsensusMedianPredictor4]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix6 :
    (∑ i ∈ Finset.range 6,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2584731269 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix5,
    observedFinalConsensusMedianLoss5,
    observedFinalConsensusMedianPredictor5]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix7 :
    (∑ i ∈ Finset.range 7,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((23366213821 : Rat) / 90000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix6,
    observedFinalConsensusMedianLoss6,
    observedFinalConsensusMedianPredictor6]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix8 :
    (∑ i ∈ Finset.range 8,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1146618923629 : Rat) / 4410000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix7,
    observedFinalConsensusMedianLoss7,
    observedFinalConsensusMedianPredictor7]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix9 :
    (∑ i ∈ Finset.range 9,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1205497740827 : Rat) / 2205000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix8,
    observedFinalConsensusMedianLoss8,
    observedFinalConsensusMedianPredictor8]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix10 :
    (∑ i ∈ Finset.range 10,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((10965752553893 : Rat) / 19845000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix9,
    observedFinalConsensusMedianLoss9,
    observedFinalConsensusMedianPredictor9]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix11 :
    (∑ i ∈ Finset.range 11,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((4398306707567 : Rat) / 7938000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix10,
    observedFinalConsensusMedianLoss10,
    observedFinalConsensusMedianPredictor10]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix12 :
    (∑ i ∈ Finset.range 12,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((697334352036587 : Rat) / 960498000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix11,
    observedFinalConsensusMedianLoss11,
    observedFinalConsensusMedianPredictor11]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix13 :
    (∑ i ∈ Finset.range 13,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((88538390784829 : Rat) / 120062250000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix12,
    observedFinalConsensusMedianLoss12,
    observedFinalConsensusMedianPredictor12]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix14 :
    (∑ i ∈ Finset.range 14,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((485203377926681837 : Rat) / 649296648000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix13,
    observedFinalConsensusMedianLoss13,
    observedFinalConsensusMedianPredictor13]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix15 :
    (∑ i ∈ Finset.range 15,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1940868510851361353 : Rat) / 2597186592000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix14,
    observedFinalConsensusMedianLoss14,
    observedFinalConsensusMedianPredictor14]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix16 :
    (∑ i ∈ Finset.range 16,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9796616010160880209 : Rat) / 12985932960000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix15,
    observedFinalConsensusMedianLoss15,
    observedFinalConsensusMedianPredictor15]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix17 :
    (∑ i ∈ Finset.range 17,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((633335855353012656601 : Rat) / 831099709440000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix16,
    observedFinalConsensusMedianLoss16,
    observedFinalConsensusMedianPredictor16]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix18 :
    (∑ i ∈ Finset.range 18,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((184345204101832987748089 : Rat) / 240187816028160000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix17,
    observedFinalConsensusMedianLoss17,
    observedFinalConsensusMedianPredictor17]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix19 :
    (∑ i ∈ Finset.range 19,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((185514710307051393202489 : Rat) / 240187816028160000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix18,
    observedFinalConsensusMedianLoss18,
    observedFinalConsensusMedianPredictor18]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix20 :
    (∑ i ∈ Finset.range 20,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((67467774980043942923192929 : Rat) / 86707801586165760000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix19,
    observedFinalConsensusMedianLoss19,
    observedFinalConsensusMedianPredictor19]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix21 :
    (∑ i ∈ Finset.range 21,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((13584257654949721376675069 : Rat) / 17341560317233152000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix20,
    observedFinalConsensusMedianLoss20,
    observedFinalConsensusMedianPredictor20]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix22 :
    (∑ i ∈ Finset.range 22,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((13937500833644077550807549 : Rat) / 17341560317233152000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix21,
    observedFinalConsensusMedianLoss21,
    observedFinalConsensusMedianPredictor21]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix23 :
    (∑ i ∈ Finset.range 23,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((14029571948111232641536829 : Rat) / 17341560317233152000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix22,
    observedFinalConsensusMedianLoss22,
    observedFinalConsensusMedianPredictor22]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix24 :
    (∑ i ∈ Finset.range 24,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7444856819729520032325058061 : Rat) / 9173685407816337408000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix23,
    observedFinalConsensusMedianLoss23,
    observedFinalConsensusMedianPredictor23]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix25 :
    (∑ i ∈ Finset.range 25,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7492767507913519557821690081 : Rat) / 9173685407816337408000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix24,
    observedFinalConsensusMedianLoss24,
    observedFinalConsensusMedianPredictor24]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix26 :
    (∑ i ∈ Finset.range 26,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((942039930915344061092772094429 : Rat) / 1146710675977042176000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix25,
    observedFinalConsensusMedianLoss25,
    observedFinalConsensusMedianPredictor25]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix27 :
    (∑ i ∈ Finset.range 27,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((947073207936566431992421534429 : Rat) / 1146710675977042176000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix26,
    observedFinalConsensusMedianLoss26,
    observedFinalConsensusMedianPredictor26]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix28 :
    (∑ i ∈ Finset.range 28,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((8567360739425987538076350769861 : Rat) / 10320396083793379584000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix27,
    observedFinalConsensusMedianLoss27,
    observedFinalConsensusMedianPredictor27]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix29 :
    (∑ i ∈ Finset.range 29,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((8597426161075058730568926379861 : Rat) / 10320396083793379584000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix28,
    observedFinalConsensusMedianLoss28,
    observedFinalConsensusMedianPredictor28]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix30 :
    (∑ i ∈ Finset.range 30,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7262217951499584520825655761463101 : Rat) / 8679453106470232230144000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix29,
    observedFinalConsensusMedianLoss29,
    observedFinalConsensusMedianPredictor29]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix31 :
    (∑ i ∈ Finset.range 31,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7283999842070368866868791616223101 : Rat) / 8679453106470232230144000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix30,
    observedFinalConsensusMedianLoss30,
    observedFinalConsensusMedianPredictor30]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix32 :
    (∑ i ∈ Finset.range 32,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7026062250315951723362959847834400061 : Rat) / 8340954435317893173168384000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix31,
    observedFinalConsensusMedianLoss31,
    observedFinalConsensusMedianPredictor31]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix33 :
    (∑ i ∈ Finset.range 33,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((28177106794837649439716135524060115869 : Rat) / 33363817741271572692673536000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix32,
    observedFinalConsensusMedianLoss32,
    observedFinalConsensusMedianPredictor32]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix34 :
    (∑ i ∈ Finset.range 34,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((28268329502003021481072858919953875869 : Rat) / 33363817741271572692673536000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix33,
    observedFinalConsensusMedianLoss33,
    observedFinalConsensusMedianPredictor33]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix35 :
    (∑ i ∈ Finset.range 35,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((28356052201804683788885850648481235869 : Rat) / 33363817741271572692673536000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix34,
    observedFinalConsensusMedianLoss34,
    observedFinalConsensusMedianPredictor34]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix36 :
    (∑ i ∈ Finset.range 36,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((28415782009654182867029245976334189469 : Rat) / 33363817741271572692673536000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix35,
    observedFinalConsensusMedianLoss35,
    observedFinalConsensusMedianPredictor35]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix37 :
    (∑ i ∈ Finset.range 37,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((28472239582660075128391637393479149469 : Rat) / 33363817741271572692673536000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix36,
    observedFinalConsensusMedianLoss36,
    observedFinalConsensusMedianPredictor36]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix38 :
    (∑ i ∈ Finset.range 38,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((38978616499104962501101433255411722983061 : Rat) / 45675066487800783016270070784000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix37,
    observedFinalConsensusMedianLoss37,
    observedFinalConsensusMedianPredictor37]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix39 :
    (∑ i ∈ Finset.range 39,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((54879099990715964702028824925068731623061 : Rat) / 45675066487800783016270070784000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix38,
    observedFinalConsensusMedianLoss38,
    observedFinalConsensusMedianPredictor38]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix40 :
    (∑ i ∈ Finset.range 40,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((55058148270540432160489191382949348583061 : Rat) / 45675066487800783016270070784000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix39,
    observedFinalConsensusMedianLoss39,
    observedFinalConsensusMedianPredictor39]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix41 :
    (∑ i ∈ Finset.range 41,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((55242002655213525704934546353640670464661 : Rat) / 45675066487800783016270070784000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix40,
    observedFinalConsensusMedianLoss40,
    observedFinalConsensusMedianPredictor40]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix42 :
    (∑ i ∈ Finset.range 42,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((93155973478890886381107540373576082061655141 : Rat) / 76779786765993116250349988987904000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix41,
    observedFinalConsensusMedianLoss41,
    observedFinalConsensusMedianPredictor41]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix43 :
    (∑ i ∈ Finset.range 43,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((93414472783556330469329890046903464845655141 : Rat) / 76779786765993116250349988987904000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix42,
    observedFinalConsensusMedianLoss42,
    observedFinalConsensusMedianPredictor42]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix44 :
    (∑ i ∈ Finset.range 44,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((173141550686333728173645651604599777314582115709 : Rat) / 141965825730321271946897129638634496000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix43,
    observedFinalConsensusMedianLoss43,
    observedFinalConsensusMedianPredictor43]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix45 :
    (∑ i ∈ Finset.range 45,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((15769803191919281046603486597235164123217370519 : Rat) / 12905984157301933813354284512603136000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix44,
    observedFinalConsensusMedianLoss44,
    observedFinalConsensusMedianPredictor44]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix46 :
    (∑ i ∈ Finset.range 46,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((15807962328724892499942557307131375505103936919 : Rat) / 12905984157301933813354284512603136000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix45,
    observedFinalConsensusMedianLoss45,
    observedFinalConsensusMedianPredictor45]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix47 :
    (∑ i ∈ Finset.range 47,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((15846710290964544031458161349902820610447936919 : Rat) / 12905984157301933813354284512603136000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix46,
    observedFinalConsensusMedianLoss46,
    observedFinalConsensusMedianPredictor46]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix48 :
    (∑ i ∈ Finset.range 48,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((35082554262922929994469733902546050685500686894071 : Rat) / 28509319003479971793699614488340327424000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix47,
    observedFinalConsensusMedianLoss47,
    observedFinalConsensusMedianPredictor47]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix49 :
    (∑ i ∈ Finset.range 49,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((35156543519638466094215328501794783491516232934071 : Rat) / 28509319003479971793699614488340327424000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix48,
    observedFinalConsensusMedianLoss48,
    observedFinalConsensusMedianPredictor48]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix50 :
    (∑ i ∈ Finset.range 50,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1725727568181352179364710375233215205413291209609479 : Rat) / 1396956631170518617891281109928676043776000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix49,
    observedFinalConsensusMedianLoss49,
    observedFinalConsensusMedianPredictor49]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix51 :
    (∑ i ∈ Finset.range 51,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((345874163893975687862658957716323710305100122985883 : Rat) / 279391326234103723578256221985735208755200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix50,
    observedFinalConsensusMedianLoss50,
    observedFinalConsensusMedianPredictor50]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix52 :
    (∑ i ∈ Finset.range 52,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((346517000906573737592933178890925269520738918633883 : Rat) / 279391326234103723578256221985735208755200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix51,
    observedFinalConsensusMedianLoss51,
    observedFinalConsensusMedianPredictor51]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix53 :
    (∑ i ∈ Finset.range 53,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((347200051093183289240004606753694406334661984833883 : Rat) / 279391326234103723578256221985735208755200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix52,
    observedFinalConsensusMedianLoss52,
    observedFinalConsensusMedianPredictor52]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix54 :
    (∑ i ∈ Finset.range 54,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((976953683486279907641854041084291285134090946598505347 : Rat) / 784810235391597359531321727557930201393356800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix53,
    observedFinalConsensusMedianLoss53,
    observedFinalConsensusMedianPredictor53]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix55 :
    (∑ i ∈ Finset.range 55,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((978561190538120884082254319514770306722476212799177347 : Rat) / 784810235391597359531321727557930201393356800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix54,
    observedFinalConsensusMedianLoss54,
    observedFinalConsensusMedianPredictor54]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix56 :
    (∑ i ∈ Finset.range 56,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((980282685307808657510650791651185383804580259940548227 : Rat) / 784810235391597359531321727557930201393356800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix55,
    observedFinalConsensusMedianLoss55,
    observedFinalConsensusMedianPredictor55]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix57 :
    (∑ i ∈ Finset.range 57,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((981885988994434453548304993644708579080178340413498227 : Rat) / 784810235391597359531321727557930201393356800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix56,
    observedFinalConsensusMedianLoss56,
    observedFinalConsensusMedianPredictor56]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix58 :
    (∑ i ∈ Finset.range 58,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((983324018844017654006645967396878567311041724980666227 : Rat) / 784810235391597359531321727557930201393356800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix57,
    observedFinalConsensusMedianLoss57,
    observedFinalConsensusMedianPredictor57]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix59 :
    (∑ i ∈ Finset.range 59,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((33961237314207158556643925219812050316060315331443663 : Rat) / 27062421910055081363149025088204489703219200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix58,
    observedFinalConsensusMedianLoss58,
    observedFinalConsensusMedianPredictor58]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix60 :
    (∑ i ∈ Finset.range 60,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((118379859231681241435589601387145612872209035254659902903 : Rat) / 94204290668901738225121756332039828656906035200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix59,
    observedFinalConsensusMedianLoss59,
    observedFinalConsensusMedianPredictor59]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix61 :
    (∑ i ∈ Finset.range 61,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((118535336299060083775087938076919755255068122220363682423 : Rat) / 94204290668901738225121756332039828656906035200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix60,
    observedFinalConsensusMedianLoss60,
    observedFinalConsensusMedianPredictor60]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix62 :
    (∑ i ∈ Finset.range 62,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((441209631712382973605370557511317986828007638085678401367983 : Rat) / 350534165578983367935678055311520202432347356979200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix61,
    observedFinalConsensusMedianLoss61,
    observedFinalConsensusMedianPredictor61]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix63 :
    (∑ i ∈ Finset.range 63,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((441760366948887752089680700533906840845480456659137602615983 : Rat) / 350534165578983367935678055311520202432347356979200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix62,
    observedFinalConsensusMedianLoss62,
    observedFinalConsensusMedianPredictor62]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix64 :
    (∑ i ∈ Finset.range 64,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((442293757286283662518929425597860369402589429850464679863983 : Rat) / 350534165578983367935678055311520202432347356979200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix63,
    observedFinalConsensusMedianLoss63,
    observedFinalConsensusMedianPredictor63]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix65 :
    (∑ i ∈ Finset.range 65,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1770513701708239977033164858522702281477293925619147079940807 : Rat) / 1402136662315933471742712221246080809729389427916800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix64,
    observedFinalConsensusMedianLoss64,
    observedFinalConsensusMedianPredictor64]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix66 :
    (∑ i ∈ Finset.range 66,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1771550941151753494698835963417530683583631924853305845938887 : Rat) / 1402136662315933471742712221246080809729389427916800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix65,
    observedFinalConsensusMedianLoss65,
    observedFinalConsensusMedianPredictor65]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix67 :
    (∑ i ∈ Finset.range 67,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((19487060354660959837022328369954644651871770505388337924527757 : Rat) / 15423503285475268189169834433706888907023283707084800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix66,
    observedFinalConsensusMedianLoss66,
    observedFinalConsensusMedianPredictor66]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix68 :
    (∑ i ∈ Finset.range 68,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((87584817984482352760151062763897098861418940831459270523352301173 : Rat) / 69236106248498478901183386772910224303627520561103667200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix67,
    observedFinalConsensusMedianLoss67,
    observedFinalConsensusMedianPredictor67]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix69 :
    (∑ i ∈ Finset.range 69,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((87679254062790972765285880572263243397424981565735538536463501173 : Rat) / 69236106248498478901183386772910224303627520561103667200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix68,
    observedFinalConsensusMedianLoss68,
    observedFinalConsensusMedianPredictor68]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix70 :
    (∑ i ∈ Finset.range 70,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((87679338335909545377934068156921369722372799624174066493724301173 : Rat) / 69236106248498478901183386772910224303627520561103667200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix69,
    observedFinalConsensusMedianLoss69,
    observedFinalConsensusMedianPredictor69]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix71 :
    (∑ i ∈ Finset.range 71,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((87771136422919383657482667502251872384737472792302217100627213173 : Rat) / 69236106248498478901183386772910224303627520561103667200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix70,
    observedFinalConsensusMedianLoss70,
    observedFinalConsensusMedianPredictor70]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix72 :
    (∑ i ∈ Finset.range 72,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((442904109334284820587158263670971151737048498869823414378086050405093 : Rat) / 349019211598680832140865452722240440714586331148523586355200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix71,
    observedFinalConsensusMedianLoss71,
    observedFinalConsensusMedianPredictor71]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix73 :
    (∑ i ∈ Finset.range 73,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((443341511990037388943505099621795652742604740277735573970302126605093 : Rat) / 349019211598680832140865452722240440714586331148523586355200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix72,
    observedFinalConsensusMedianLoss72,
    observedFinalConsensusMedianPredictor72]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix74 :
    (∑ i ∈ Finset.range 74,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2365156843983565791108480946774484087128767135743363656238094645101708597 : Rat) / 1859923378609370154478671997556819308568030558690482191686860800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix73,
    observedFinalConsensusMedianLoss73,
    observedFinalConsensusMedianPredictor73]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix75 :
    (∑ i ∈ Finset.range 75,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2367062813292890126902276892170159611880991801416951681853295573168908597 : Rat) / 1859923378609370154478671997556819308568030558690482191686860800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix74,
    observedFinalConsensusMedianLoss74,
    observedFinalConsensusMedianPredictor74]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix76 :
    (∑ i ∈ Finset.range 76,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2368746243380815878281794904303553471385196230279643223823725185816557877 : Rat) / 1859923378609370154478671997556819308568030558690482191686860800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix75,
    observedFinalConsensusMedianLoss75,
    observedFinalConsensusMedianPredictor75]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix77 :
    (∑ i ∈ Finset.range 77,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2370844665932338673632277915020638338356319813347866397043350547313805877 : Rat) / 1859923378609370154478671997556819308568030558690482191686860800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix76,
    observedFinalConsensusMedianLoss76,
    observedFinalConsensusMedianPredictor76]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix78 :
    (∑ i ∈ Finset.range 78,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2372068630194628249343945530191894365380386530573645407101741000511117877 : Rat) / 1859923378609370154478671997556819308568030558690482191686860800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix77,
    observedFinalConsensusMedianLoss77,
    observedFinalConsensusMedianPredictor77]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix79 :
    (∑ i ∈ Finset.range 79,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2373261411935442663281236340571640746745556084556492834885468317573389877 : Rat) / 1859923378609370154478671997556819308568030558690482191686860800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix78,
    observedFinalConsensusMedianLoss78,
    observedFinalConsensusMedianPredictor78]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix80 :
    (∑ i ∈ Finset.range 80,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((14818781356000212555932673291857986884664707090148715533156404766982389070357 : Rat) / 11607781805901079134101391936752109304773078716787299358317698252800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix79,
    observedFinalConsensusMedianLoss79,
    observedFinalConsensusMedianPredictor79]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix81 :
    (∑ i ∈ Finset.range 81,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((14819108534617014470325269944550897572032598170275205179230218929710158029477 : Rat) / 11607781805901079134101391936752109304773078716787299358317698252800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix80,
    observedFinalConsensusMedianLoss80,
    observedFinalConsensusMedianPredictor80]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix82 :
    (∑ i ∈ Finset.range 82,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((5118964807392435028389985811425970758458508018863841795207059156758784239159 : Rat) / 3869260601967026378033797312250703101591026238929099786105899417600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix81,
    observedFinalConsensusMedianLoss81,
    observedFinalConsensusMedianPredictor81]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix83 :
    (∑ i ∈ Finset.range 83,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((5177140380516521304706187433813929635501319873993982822953501818959721583159 : Rat) / 3869260601967026378033797312250703101591026238929099786105899417600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix82,
    observedFinalConsensusMedianLoss82,
    observedFinalConsensusMedianPredictor82]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix84 :
    (∑ i ∈ Finset.range 84,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((35680217999753060420671859040832628829597253817588947910771687498261412757838351 : Rat) / 26655336286950844718274829684095093666860579759982568426483541087846400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix83,
    observedFinalConsensusMedianLoss83,
    observedFinalConsensusMedianPredictor83]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix85 :
    (∑ i ∈ Finset.range 85,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((35749167929503538986250908512875246243296812519475817688960589198894442227502351 : Rat) / 26655336286950844718274829684095093666860579759982568426483541087846400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix84,
    observedFinalConsensusMedianLoss84,
    observedFinalConsensusMedianPredictor84]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix86 :
    (∑ i ∈ Finset.range 86,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((35749169751845410062313066695546671049846857665403175516744625651048306940984591 : Rat) / 26655336286950844718274829684095093666860579759982568426483541087846400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix85,
    observedFinalConsensusMedianLoss85,
    observedFinalConsensusMedianPredictor85]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix87 :
    (∑ i ∈ Finset.range 87,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((35824847555155750051274312598105377242167726314919864872851856928947873094584591 : Rat) / 26655336286950844718274829684095093666860579759982568426483541087846400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix86,
    observedFinalConsensusMedianLoss86,
    observedFinalConsensusMedianPredictor86]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix88 :
    (∑ i ∈ Finset.range 88,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1039253535026952045068162809536019765133174751180408211746936151459935836349417139 : Rat) / 773004752321574496829970060838757716338956813039494484368022691547545600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix87,
    observedFinalConsensusMedianLoss87,
    observedFinalConsensusMedianPredictor87]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix89 :
    (∑ i ∈ Finset.range 89,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1039253545823464701460401649557915656186898227319557088083677296765376734823401139 : Rat) / 773004752321574496829970060838757716338956813039494484368022691547545600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix88,
    observedFinalConsensusMedianLoss88,
    observedFinalConsensusMedianPredictor88]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix90 :
    (∑ i ∈ Finset.range 90,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((8247163297363831005407387943378739957240033316267380246979755962092924065241956518019 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix89,
    observedFinalConsensusMedianLoss89,
    observedFinalConsensusMedianPredictor89]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix91 :
    (∑ i ∈ Finset.range 91,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((8288162507079984067442798537322611183644965176011713684019368487072214527700181813379 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix90,
    observedFinalConsensusMedianLoss90,
    observedFinalConsensusMedianPredictor90]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix92 :
    (∑ i ∈ Finset.range 92,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9176650941496373599727428318879437351887014234598303125562704719924919730080228149379 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix91,
    observedFinalConsensusMedianLoss91,
    observedFinalConsensusMedianPredictor91]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix93 :
    (∑ i ∈ Finset.range 93,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9256629216706404866317888501944689709241166274885053922850474952332627853750352693379 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix92,
    observedFinalConsensusMedianLoss92,
    observedFinalConsensusMedianPredictor92]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix94 :
    (∑ i ∈ Finset.range 94,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9856721352919147305355803294175500759941170800375851299668949559903829205796141877379 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix93,
    observedFinalConsensusMedianLoss93,
    observedFinalConsensusMedianPredictor93]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix95 :
    (∑ i ∈ Finset.range 95,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9960765138983729540491853840446276365761099828425541167492341080762812568944410933379 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix94,
    observedFinalConsensusMedianLoss94,
    observedFinalConsensusMedianPredictor94]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix96 :
    (∑ i ∈ Finset.range 96,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9961486964748039075369475127910498368464965217202509902182967867408651878577102399619 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix95,
    observedFinalConsensusMedianLoss95,
    observedFinalConsensusMedianPredictor95]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix97 :
    (∑ i ∈ Finset.range 97,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((9986444953381997986498935594703754731447264739577857046668562487929130356454070261119 : Rat) / 6122970643139191589390192851903799871120876916085835810679107739748108697600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix96,
    observedFinalConsensusMedianLoss96,
    observedFinalConsensusMedianPredictor96]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix98 :
    (∑ i ∈ Finset.range 98,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((108952163733297211044341386173996248489677568296845982469932612706820275486105666600468671 : Rat) / 57611030781296653664572324543562852987376330903451629142679724723289954735718400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix97,
    observedFinalConsensusMedianLoss97,
    observedFinalConsensusMedianPredictor97]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix99 :
    (∑ i ∈ Finset.range 99,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((108970047110789822628711099430433743914657866177207325089839997724414519312980588082068671 : Rat) / 57611030781296653664572324543562852987376330903451629142679724723289954735718400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix98,
    observedFinalConsensusMedianLoss98,
    observedFinalConsensusMedianPredictor98]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix100 :
    (∑ i ∈ Finset.range 100,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((109099707412415468372647441613903827900475715472676445963419832109498374853488971864468671 : Rat) / 57611030781296653664572324543562852987376330903451629142679724723289954735718400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix99,
    observedFinalConsensusMedianLoss99,
    observedFinalConsensusMedianPredictor99]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix101 :
    (∑ i ∈ Finset.range 101,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((109270614705636692812450688580242344258118104939798464011913039249154024981244219484158911 : Rat) / 57611030781296653664572324543562852987376330903451629142679724723289954735718400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix100,
    observedFinalConsensusMedianLoss100,
    observedFinalConsensusMedianPredictor100]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix102 :
    (∑ i ∈ Finset.range 102,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1115936285807941690653126071999529311334207832430293657034019175892129664845999996641911451111 : Rat) / 587690125000007164032302282668884663324225951546110068884475871902280828259063398400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix101,
    observedFinalConsensusMedianLoss101,
    observedFinalConsensusMedianPredictor101]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix103 :
    (∑ i ∈ Finset.range 103,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((1117718693930812894205551788273331419833598771649992056351624669149910092911663255816506395111 : Rat) / 587690125000007164032302282668884663324225951546110068884475871902280828259063398400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix102,
    observedFinalConsensusMedianLoss102,
    observedFinalConsensusMedianPredictor102]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix104 :
    (∑ i ∈ Finset.range 104,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((11870749585625650707866001407343954345910321165699359550016593897108555513866349529272929645956599 : Rat) / 6234804536125076003218694916834197393206713119952681720795404525011297307000403593625600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix103,
    observedFinalConsensusMedianLoss103,
    observedFinalConsensusMedianPredictor103]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix105 :
    (∑ i ∈ Finset.range 105,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((11883375199699262400798301709602006449137963741252251181003006837222161599166696010280727491932599 : Rat) / 6234804536125076003218694916834197393206713119952681720795404525011297307000403593625600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix104,
    observedFinalConsensusMedianLoss104,
    observedFinalConsensusMedianPredictor104]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix106 :
    (∑ i ∈ Finset.range 106,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((11895761471066172520594742532207275523832764838502144684925822470806629936455453156637221052211639 : Rat) / 6234804536125076003218694916834197393206713119952681720795404525011297307000403593625600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix105,
    observedFinalConsensusMedianLoss105,
    observedFinalConsensusMedianPredictor105]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix107 :
    (∑ i ∈ Finset.range 107,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((11907915141573486873634593018966183636017722305321304161674580245839449749432361979935578252467639 : Rat) / 6234804536125076003218694916834197393206713119952681720795404525011297307000403593625600000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix106,
    observedFinalConsensusMedianLoss106,
    observedFinalConsensusMedianPredictor106]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix108 :
    (∑ i ∈ Finset.range 108,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((136503981756178936821210640316886923239723791983158573153596074780953113850093325510440473653353454911 : Rat) / 71382277134095995160850838102834725954823658510338253021386586406854342867847620743419494400000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix107,
    observedFinalConsensusMedianLoss107,
    observedFinalConsensusMedianPredictor107]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix109 :
    (∑ i ∈ Finset.range 109,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((409754952599294618060521194777294885716156993654667806922333065537988976729312637760888204636240364733 : Rat) / 214146831402287985482552514308504177864470975531014759064159759220563028603542862230258483200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix108,
    observedFinalConsensusMedianLoss108,
    observedFinalConsensusMedianPredictor108]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix110 :
    (∑ i ∈ Finset.range 110,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((4868727074153162569548301860660285433805301092825653206357801721947847137763197510860623543840432922064773 : Rat) / 2544278503890583555518206422499338137207779660283986352441282099299509342838692746157701038899200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix109,
    observedFinalConsensusMedianLoss109,
    observedFinalConsensusMedianPredictor109]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix111 :
    (∑ i ∈ Finset.range 111,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((4869792067664334328506012846136837640351362548360986212200179025381590256751492601857231051876618702908293 : Rat) / 2544278503890583555518206422499338137207779660283986352441282099299509342838692746157701038899200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix110,
    observedFinalConsensusMedianLoss110,
    observedFinalConsensusMedianPredictor110]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix112 :
    (∑ i ∈ Finset.range 112,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((4876612389425962686245727448382189505190954918662188767893342218516878798533566482841401659515106992700293 : Rat) / 2544278503890583555518206422499338137207779660283986352441282099299509342838692746157701038899200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix111,
    observedFinalConsensusMedianLoss111,
    observedFinalConsensusMedianPredictor111]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix113 :
    (∑ i ∈ Finset.range 113,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((4906172063973011817052407685055786380232445524547570827790436257923907010487293613578350923656401430062293 : Rat) / 2544278503890583555518206422499338137207779660283986352441282099299509342838692746157701038899200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix112,
    observedFinalConsensusMedianLoss112,
    observedFinalConsensusMedianPredictor112]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix114 :
    (∑ i ∈ Finset.range 114,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((63905602167912946880854962633163998453606957084610419717539955188221808371975308516481219406468000547732747317 : Rat) / 32487892216178861420411977808894048674006138482166221734322731125955434798707267675687684565703884800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix113,
    observedFinalConsensusMedianLoss113,
    observedFinalConsensusMedianPredictor113]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix115 :
    (∑ i ∈ Finset.range 115,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((63994782978147610763651694580638747237940540582923235178004008429922997598505688286597250498693844399673739317 : Rat) / 32487892216178861420411977808894048674006138482166221734322731125955434798707267675687684565703884800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix114,
    observedFinalConsensusMedianLoss114,
    observedFinalConsensusMedianPredictor114]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix116 :
    (∑ i ∈ Finset.range 116,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((64058936853558091950851546356945660635749812438593635139503676203917200566003839572122949125010435180618307637 : Rat) / 32487892216178861420411977808894048674006138482166221734322731125955434798707267675687684565703884800000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix115,
    observedFinalConsensusMedianLoss115,
    observedFinalConsensusMedianPredictor115]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix117 :
    (∑ i ∈ Finset.range 117,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2211906393779351617914749327691753307280134064130719253429189978261742467430699962158244946101619150963688953 : Rat) / 1120272145385477980014206131341174092207108223522973163252507969860532234438181643989230502265651200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix116,
    observedFinalConsensusMedianLoss116,
    observedFinalConsensusMedianPredictor116]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix118 :
    (∑ i ∈ Finset.range 118,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2214037343306988220666969637069847568439052270160206170866615981205366573765880216685781275826391234358760953 : Rat) / 1120272145385477980014206131341174092207108223522973163252507969860532234438181643989230502265651200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix117,
    observedFinalConsensusMedianLoss117,
    observedFinalConsensusMedianPredictor117]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix119 :
    (∑ i ∈ Finset.range 119,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2214233851301255056136810101125072168361050361344133253984152602290022230110684379314697944527160649422952953 : Rat) / 1120272145385477980014206131341174092207108223522973163252507969860532234438181643989230502265651200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix118,
    observedFinalConsensusMedianLoss118,
    observedFinalConsensusMedianPredictor118]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix120 :
    (∑ i ∈ Finset.range 120,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2716174254212185251554190486982296940503582112560194032503828152481480687760374401483494263267420567077480953 : Rat) / 1120272145385477980014206131341174092207108223522973163252507969860532234438181643989230502265651200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix119,
    observedFinalConsensusMedianLoss119,
    observedFinalConsensusMedianPredictor119]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix121 :
    (∑ i ∈ Finset.range 121,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2718832397399270682490281564707153758267061090467932815072515117138040765309975950453211834992456294078537273 : Rat) / 1120272145385477980014206131341174092207108223522973163252507969860532234438181643989230502265651200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix120,
    observedFinalConsensusMedianLoss120,
    observedFinalConsensusMedianPredictor120]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix122 :
    (∑ i ∈ Finset.range 122,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((329024157442639388373065871276416988824189181931887594775163621480160161947793947173192648001541396735005858033 : Rat) / 135552929591642835581718941892282065157060095046279752753553464353124400367019978922696890774143795200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix121,
    observedFinalConsensusMedianLoss121,
    observedFinalConsensusMedianPredictor121]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix123 :
    (∑ i ∈ Finset.range 123,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((329444081125678799241092963636922569742253847219778426920008903727452011575165682623454228915165254146987810033 : Rat) / 135552929591642835581718941892282065157060095046279752753553464353124400367019978922696890774143795200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix122,
    observedFinalConsensusMedianLoss122,
    observedFinalConsensusMedianPredictor122]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix124 :
    (∑ i ∈ Finset.range 124,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((354775967774128147601808480977309898399394508021480538279873200169018665477752848466872984879879713127207202033 : Rat) / 135552929591642835581718941892282065157060095046279752753553464353124400367019978922696890774143795200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix123,
    observedFinalConsensusMedianLoss123,
    observedFinalConsensusMedianPredictor123]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix125 :
    (∑ i ∈ Finset.range 125,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((355242916026908161458562016381075588208366762472952197969612461600069806917815268169557559718722736400376770033 : Rat) / 135552929591642835581718941892282065157060095046279752753553464353124400367019978922696890774143795200000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix124,
    observedFinalConsensusMedianLoss124,
    observedFinalConsensusMedianPredictor124]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix126 :
    (∑ i ∈ Finset.range 126,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((44467021025693103771608348952512340848983899273785211724985361413481853596686033613893933204573996902478708522669 : Rat) / 16944116198955354447714867736535258144632511880784969094194183044140550045877497365337111346767974400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix125,
    observedFinalConsensusMedianLoss125,
    observedFinalConsensusMedianPredictor125]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix127 :
    (∑ i ∈ Finset.range 127,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((44473964952082597592898046894989060659340337151682033816273836019073447644237903711936826405201162597853252522669 : Rat) / 16944116198955354447714867736535258144632511880784969094194183044140550045877497365337111346767974400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix126,
    observedFinalConsensusMedianLoss126,
    observedFinalConsensusMedianPredictor126]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix128 :
    (∑ i ∈ Finset.range 128,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((718162859134560053801165862000546035520381086636365270399517504551805533423236519151269455554559717514514178162128301 : Rat) / 273291650172950911887193101722577178614777784125180766520257978318942931689958155005522268912020659097600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix127,
    observedFinalConsensusMedianLoss127,
    observedFinalConsensusMedianPredictor127]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix129 :
    (∑ i ∈ Finset.range 129,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2892012264302366769656472047816178195786163486012560614228778036418196230122114904092335649471244804035642532650216329 : Rat) / 1093166600691803647548772406890308714459111136500723066081031913275771726759832620022089075648082636390400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix128,
    observedFinalConsensusMedianLoss128,
    observedFinalConsensusMedianPredictor128]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix130 :
    (∑ i ∈ Finset.range 130,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2902607716709920666076637992016420660985488590653612784011150915987017203420979701684278918960974544380053950506216329 : Rat) / 1093166600691803647548772406890308714459111136500723066081031913275771726759832620022089075648082636390400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix129,
    observedFinalConsensusMedianLoss129,
    observedFinalConsensusMedianPredictor129]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix131 :
    (∑ i ∈ Finset.range 131,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((223335270586892902363202026587505236045563628726265970518133894177164500961092145007586909917507188583919050028404333 : Rat) / 84089738514754126734520954376177593419931625884671005083156301021213209750756355386314544280621741260800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix130,
    observedFinalConsensusMedianLoss130,
    observedFinalConsensusMedianPredictor130]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix132 :
    (∑ i ∈ Finset.range 132,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3846485500552671483439162239345981866466942256163683808985671565521369152779974068953221939219692102868272783441574758613 : Rat) / 1443064002651695568891114098049583680679446631806839118232045281825039892532729814784543894399749701776588800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix131,
    observedFinalConsensusMedianLoss131,
    observedFinalConsensusMedianPredictor131]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix133 :
    (∑ i ∈ Finset.range 133,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3856082769041362519211110830091435909195929909298869676938492094933078517450716978579804777406767305049204681411766758613 : Rat) / 1443064002651695568891114098049583680679446631806839118232045281825039892532729814784543894399749701776588800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix132,
    observedFinalConsensusMedianLoss132,
    observedFinalConsensusMedianPredictor132]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix134 :
    (∑ i ∈ Finset.range 134,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3858504046459643623814404722088214034654193362932341899890544352841218974012768051879216097118654850105627402116534758613 : Rat) / 1443064002651695568891114098049583680679446631806839118232045281825039892532729814784543894399749701776588800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix133,
    observedFinalConsensusMedianLoss133,
    observedFinalConsensusMedianPredictor133]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix135 :
    (∑ i ∈ Finset.range 135,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3861934444550389240792234541822536631399874720708248689320896113456738553756322787241615820205668981399492569166326758613 : Rat) / 1443064002651695568891114098049583680679446631806839118232045281825039892532729814784543894399749701776588800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix134,
    observedFinalConsensusMedianLoss134,
    observedFinalConsensusMedianPredictor134]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix136 :
    (∑ i ∈ Finset.range 136,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3865956714197824943738043960063677265039276302475429639472384690011114001394883972760440802186669733900244618992047078613 : Rat) / 1443064002651695568891114098049583680679446631806839118232045281825039892532729814784543894399749701776588800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix135,
    observedFinalConsensusMedianLoss135,
    observedFinalConsensusMedianPredictor135]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix137 :
    (∑ i ∈ Finset.range 137,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3869920050288034485595060431054420563486405077762349666316614756387816668631733973089192169866370140167881194904339078613 : Rat) / 1443064002651695568891114098049583680679446631806839118232045281825039892532729814784543894399749701776588800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix136,
    observedFinalConsensusMedianLoss136,
    observedFinalConsensusMedianPredictor136]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix138 :
    (∑ i ∈ Finset.range 138,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((72647667439526837794929436278896267109810129216824907184213645798674848719974627879602706097398334725599322703080921798487397 : Rat) / 27084868265769674132517320506292636102672533832382563410097257894574173742946805893691104353988902152644795187200000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix137,
    observedFinalConsensusMedianLoss137,
    observedFinalConsensusMedianPredictor137]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix139 :
    (∑ i ∈ Finset.range 139,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3161761923010694028209169996934930650545489541596477015736531980151457453787102069761569819525090099519273689588679001325539 : Rat) / 1177602968076942353587709587230114613159675384016633191743359038894529293171600256247439319738647919680208486400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix138,
    observedFinalConsensusMedianLoss138,
    observedFinalConsensusMedianPredictor138]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix140 :
    (∑ i ∈ Finset.range 140,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((61167580758378658632957412666277256261458242497766473767756606938338276357560531048204013130600222678178650785510253401506739019 : Rat) / 22752466946214603213668136934873044440858088094585369897673439990481200473368488550956775096670416456141308165734400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix139,
    observedFinalConsensusMedianLoss139,
    observedFinalConsensusMedianPredictor139]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix141 :
    (∑ i ∈ Finset.range 141,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((61251329644307847977611462296126462540810553618671091075282176725298663026296419121701835276855061812488197957148150396834099019 : Rat) / 22752466946214603213668136934873044440858088094585369897673439990481200473368488550956775096670416456141308165734400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix140,
    observedFinalConsensusMedianLoss140,
    observedFinalConsensusMedianPredictor140]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix142 :
    (∑ i ∈ Finset.range 142,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((61332529897214143977400158401829934401123416667319415733384408794854141291467283213893776420099519790356347360771536864930099019 : Rat) / 22752466946214603213668136934873044440858088094585369897673439990481200473368488550956775096670416456141308165734400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix141,
    observedFinalConsensusMedianLoss141,
    observedFinalConsensusMedianPredictor141]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix143 :
    (∑ i ∈ Finset.range 143,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((61408329852571788763717678154737803424577698518353002244836551714294793354381808628525924364574973641699675861077868895330099019 : Rat) / 22752466946214603213668136934873044440858088094585369897673439990481200473368488550956775096670416456141308165734400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix142,
    observedFinalConsensusMedianLoss142,
    observedFinalConsensusMedianPredictor142]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix144 :
    (∑ i ∈ Finset.range 144,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((799352460522388178756137333754890677300716633390510037894325597005762036567920853002280170960262878044117037844833366565883287247 : Rat) / 295782070300789841777685780153349577731155145229609808669754719876255606153790351162438076256715413929837006154547200000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix143,
    observedFinalConsensusMedianLoss143,
    observedFinalConsensusMedianPredictor143]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix145 :
    (∑ i ∈ Finset.range 145,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((800392678751351487084730382253463073649736547111071684661738233622917253265027662703428706913130533141239900743942157252958287247 : Rat) / 295782070300789841777685780153349577731155145229609808669754719876255606153790351162438076256715413929837006154547200000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix144,
    observedFinalConsensusMedianLoss144,
    observedFinalConsensusMedianPredictor144]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix146 :
    (∑ i ∈ Finset.range 146,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((23231977621212017228423901664137377325617231648104310886772704729489392002855119222995993586319100154099056761343659160063662330163 : Rat) / 8577680038722905411552887624447137754203499211658684451422886876411412578459920183710704211444747003965273178481868800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix145,
    observedFinalConsensusMedianLoss145,
    observedFinalConsensusMedianPredictor145]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix147 :
    (∑ i ∈ Finset.range 147,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((23259029606700028992630478171720910554817513610472498948525283884971840616232752544851944416363462063852974123501752701092462330163 : Rat) / 8577680038722905411552887624447137754203499211658684451422886876411412578459920183710704211444747003965273178481868800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix146,
    observedFinalConsensusMedianLoss146,
    observedFinalConsensusMedianPredictor146]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix148 :
    (∑ i ∈ Finset.range 148,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((23284672618937837632946412785829724000442765733940386173184040266987302255886969472666421504616168611529770875769796794712430330163 : Rat) / 8577680038722905411552887624447137754203499211658684451422886876411412578459920183710704211444747003965273178481868800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix147,
    observedFinalConsensusMedianLoss147,
    observedFinalConsensusMedianPredictor147]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix149 :
    (∑ i ∈ Finset.range 149,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((23307428890073658525841762302787561169058971454685500589188301750166454305307814523618998576925227546293752754155624574763102330163 : Rat) / 8577680038722905411552887624447137754203499211658684451422886876411412578459920183710704211444747003965273178481868800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix148,
    observedFinalConsensusMedianLoss148,
    observedFinalConsensusMedianPredictor148]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix150 :
    (∑ i ∈ Finset.range 150,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((517682326389037884658845108505892781203380577015954225432601341691574552930562331059819001036381425015424701248521599287410975631948763 : Rat) / 190433074539687223041885658150350905281071885998034453506039511543209770654388687998561344198284828235033029835475969228800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix149,
    observedFinalConsensusMedianLoss149,
    observedFinalConsensusMedianPredictor149]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix151 :
    (∑ i ∈ Finset.range 151,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((517739502445002304780860501244150358760911396079424718079987230717521934151470649758468166391117550899634131270692676158704886116428763 : Rat) / 190433074539687223041885658150350905281071885998034453506039511543209770654388687998561344198284828235033029835475969228800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix150,
    observedFinalConsensusMedianLoss150,
    observedFinalConsensusMedianPredictor150]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix152 :
    (∑ i ∈ Finset.range 152,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((11806046933321000838258761802789292651856752807376927808002433089896681441910466778344776942379494653910967207779255294771837154357460225163 : Rat) / 4342064532579408372578034891486150991313720072641183574391206902696725980690716475055197209065092368586988113278687574385868800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix151,
    observedFinalConsensusMedianLoss151,
    observedFinalConsensusMedianPredictor151]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix153 :
    (∑ i ∈ Finset.range 153,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((11819093920228461929357401776038892908606860362554453165303722254558218339541541899680571069751549642993631806478830488793957787804272225163 : Rat) / 4342064532579408372578034891486150991313720072641183574391206902696725980690716475055197209065092368586988113278687574385868800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix152,
    observedFinalConsensusMedianLoss152,
    observedFinalConsensusMedianPredictor152]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix154 :
    (∑ i ∈ Finset.range 154,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((695804016198282610179560903845759761332453783777090790149933269263735169666674365143816751869256301762169706340506271716206062530220248539 : Rat) / 255415560739965198386943228910950058312571768978893151434776876629219175334748027944423365239123080505116947839922798493286400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix153,
    observedFinalConsensusMedianLoss153,
    observedFinalConsensusMedianPredictor153]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix155 :
    (∑ i ∈ Finset.range 155,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((696359923055720860515545005402507725486601359472842025518315895156301788539101292863139571124591809838927998556881787466559741226604248539 : Rat) / 255415560739965198386943228910950058312571768978893151434776876629219175334748027944423365239123080505116947839922798493286400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix154,
    observedFinalConsensusMedianLoss154,
    observedFinalConsensusMedianPredictor154]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix156 :
    (∑ i ∈ Finset.range 156,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((696908680060133162075095430065143926022699753029571944269473537431769423634979628671316885649442461641150669033616927176669537021128408539 : Rat) / 255415560739965198386943228910950058312571768978893151434776876629219175334748027944423365239123080505116947839922798493286400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix155,
    observedFinalConsensusMedianLoss155,
    observedFinalConsensusMedianPredictor155]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix157 :
    (∑ i ∈ Finset.range 157,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((697450424267521621352223920882033912786332392132153974923507164801432060599907185286679310923092071665328827243822455264086854738232408539 : Rat) / 255415560739965198386943228910950058312571768978893151434776876629219175334748027944423365239123080505116947839922798493286400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix156,
    observedFinalConsensusMedianLoss156,
    observedFinalConsensusMedianPredictor156]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix158 :
    (∑ i ∈ Finset.range 158,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((17208176930447331495641357691528271451419854442922340666272980921383730996501922244488815478957832254521965530524929415943089715557605454077811 : Rat) / 6295738156679402175039763649426007987346581533560737289715815232033623452826204140802091529779144811370627647306257060061016473600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix157,
    observedFinalConsensusMedianLoss157,
    observedFinalConsensusMedianPredictor157]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix159 :
    (∑ i ∈ Finset.range 159,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((17225818392263999592623937692538943589642354907490174490131707718310683301354188078701566876063583809124900375352365434849785203050565454077811 : Rat) / 6295738156679402175039763649426007987346581533560737289715815232033623452826204140802091529779144811370627647306257060061016473600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix158,
    observedFinalConsensusMedianLoss158,
    observedFinalConsensusMedianPredictor158]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix160 :
    (∑ i ∈ Finset.range 160,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((17243238646715615524472880659400634949105449784966200105368812886558950274113650294804059889684405050733526041515575465148695299556805454077811 : Rat) / 6295738156679402175039763649426007987346581533560737289715815232033623452826204140802091529779144811370627647306257060061016473600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix159,
    observedFinalConsensusMedianLoss159,
    observedFinalConsensusMedianPredictor159]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix161 :
    (∑ i ∈ Finset.range 161,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((17255859465610845800736381098039332779252257314019190978841077768327151634759566451973261471945092824320924344692132312343485503846714229077811 : Rat) / 6295738156679402175039763649426007987346581533560737289715815232033623452826204140802091529779144811370627647306257060061016473600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix160,
    observedFinalConsensusMedianLoss160,
    observedFinalConsensusMedianPredictor160]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix162 :
    (∑ i ∈ Finset.range 162,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((397289911647648538161858818396066795395733315560031068118269598675508163271941563185342811407185725999887459765588940739358445417272028036789653 : Rat) / 144801977603626250025914563936798183708971375271896957663463750336773339415002695238448105184920330661524435888043912381403378892800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix161,
    observedFinalConsensusMedianLoss161,
    observedFinalConsensusMedianPredictor161]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix163 :
    (∑ i ∈ Finset.range 163,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((3578151633265027705031832380398384614039210456363131436594867793975767709469034537623655064390351970415147359858797485143859724681260177579106877 : Rat) / 1303217798432636250233231075431183653380742377447072618971173753030960054735024257146032946664282975953719922992395211432630410035200000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix162,
    observedFinalConsensusMedianLoss162,
    observedFinalConsensusMedianPredictor162]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix164 :
    (∑ i ∈ Finset.range 164,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((95168123290085569383708934572692293031385317279380272685599643529844904757699657476999501090938061299478568138116667584663834360917824520698458615013 : Rat) / 34625193686556712532446716443131118486672944226391272413445115444279577694254859488112949359923334388114384633984948372553557364225228800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix163,
    observedFinalConsensusMedianLoss163,
    observedFinalConsensusMedianPredictor163]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix165 :
    (∑ i ∈ Finset.range 165,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((95267117457662220409250030867978431085339515617235072548127675985854344800423469719811244202358778128013276012491938888079214289104251648762010615013 : Rat) / 34625193686556712532446716443131118486672944226391272413445115444279577694254859488112949359923334388114384633984948372553557364225228800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix164,
    observedFinalConsensusMedianLoss164,
    observedFinalConsensusMedianPredictor164]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix166 :
    (∑ i ∈ Finset.range 166,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((95331873340753885372607380131167310950281730924522892724232170156331629338690658450975285572462205185109588893551106916766490292488670716633938935013 : Rat) / 34625193686556712532446716443131118486672944226391272413445115444279577694254859488112949359923334388114384633984948372553557364225228800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix165,
    observedFinalConsensusMedianLoss165,
    observedFinalConsensusMedianPredictor165]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix167 :
    (∑ i ∈ Finset.range 167,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((95428714769112131917285467218201691678302395732532510076955070474672443678492897674628217313082097127826991456996117547431792589257648635675730935013 : Rat) / 34625193686556712532446716443131118486672944226391272413445115444279577694254859488112949359923334388114384633984948372553557364225228800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix166,
    observedFinalConsensusMedianLoss166,
    observedFinalConsensusMedianPredictor166]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix168 :
    (∑ i ∈ Finset.range 168,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2664079988595608088826323763018746374557512954034112189307832201640339261697078927294686539689068349171487709782455435218938333611572518337476080398577557 : Rat) / 965662026724380155817406474882483763474821741529826196338570824625513142315073776263982044698901872750122073057206225162146161330877406003200000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix167,
    observedFinalConsensusMedianLoss167,
    observedFinalConsensusMedianPredictor167]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix169 :
    (∑ i ∈ Finset.range 169,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((2666480224910999611711981415011498502747923666127267151878859653737222387037512412883363168835429082741012679944764624300381281429456500336890573598577557 : Rat) / 965662026724380155817406474882483763474821741529826196338570824625513142315073776263982044698901872750122073057206225162146161330877406003200000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix168,
    observedFinalConsensusMedianLoss168,
    observedFinalConsensusMedianPredictor168]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix170 :
    (∑ i ∈ Finset.range 170,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((451036011677211066580063329964419200017926625836556702890040173836516200744300513145660027491926481517351100057771816492768257622003932627653291885359607133 : Rat) / 163196882516420246333141694255139756027244874318540627181218469361711721051247468188612965554114416494770630346667852052402701264918281614540800000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix169,
    observedFinalConsensusMedianLoss169,
    observedFinalConsensusMedianPredictor169]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix171 :
    (∑ i ∈ Finset.range 171,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7675047563731834630119180420475052514169485295377283968371489692362305953411278913767063395950838849234875835020165006287993217033530671206025894344489321261 : Rat) / 2774347002779144187663408802337375852463162863415190662080713979149099257871206959206420414419945080411100715893353484890845921503610787447193600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix170,
    observedFinalConsensusMedianLoss170,
    observedFinalConsensusMedianPredictor170]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix172 :
    (∑ i ∈ Finset.range 172,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7682141453068860867306520008373564150933496680738707134635832002053919585201058609314720161803687899812961661112315229819229705051814253675622821493545321261 : Rat) / 2774347002779144187663408802337375852463162863415190662080713979149099257871206959206420414419945080411100715893353484890845921503610787447193600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix171,
    observedFinalConsensusMedianLoss171,
    observedFinalConsensusMedianPredictor171]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix173 :
    (∑ i ∈ Finset.range 173,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((7688713883718222742112108980995678440122935336693223189169480470147531416505235926411198307467179074842207840066322952408869731292644167923265119528809321261 : Rat) / 2774347002779144187663408802337375852463162863415190662080713979149099257871206959206420414419945080411100715893353484890845921503610787447193600000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix172,
    observedFinalConsensusMedianLoss172,
    observedFinalConsensusMedianPredictor172]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix174 :
    (∑ i ∈ Finset.range 174,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((230309956614133410152921853858272289165819684889649879785976837271126880181887987790542963605493925453017657403520344107736972724166259484877651507452984352020469 : Rat) / 83033431446177006392578162045155321888370001339153241325413688681953391688827353082088956583174536311623833325972176449298127584681567257507057254400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix173,
    observedFinalConsensusMedianLoss173,
    observedFinalConsensusMedianPredictor173]
  norm_num [ratToReal]

theorem observedFinalConsensusMedianQuadraticPrefix175 :
    (∑ i ∈ Finset.range 175,
      (observedTrajectoryScore
          (monitorBrierScore finalConsensusMedian) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore finalConsensusMedian)) i replayPath) ^ 2) =
      ratToReal ((230502166896071254316168474229054068042589489053202239480445516191940613575911470250751992108846705487846893042284727879560720591823263280889913121284308256020469 : Rat) / 83033431446177006392578162045155321888370001339153241325413688681953391688827353082088956583174536311623833325972176449298127584681567257507057254400000000000000) := by
  rw [Finset.sum_range_succ,
    observedFinalConsensusMedianQuadraticPrefix174,
    observedFinalConsensusMedianLoss174,
    observedFinalConsensusMedianPredictor174]
  norm_num [ratToReal]

end

end FormalSLT.Applications.GJPBrierMonitorReplayPathData
