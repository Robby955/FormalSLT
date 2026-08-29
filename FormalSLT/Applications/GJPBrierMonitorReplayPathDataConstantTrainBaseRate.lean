/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathDataBase
import Mathlib.Tactic

/-!
# Generated GJP path calculation: constant-train-baserate

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

theorem observedConstantTrainBaseRateLoss0 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 0 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss1 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 1 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss2 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 2 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss3 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 3 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss4 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 4 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss5 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 5 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss6 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 6 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss7 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 7 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss8 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 8 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss9 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 9 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss10 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 10 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss11 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 11 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss12 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 12 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss13 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 13 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss14 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 14 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss15 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 15 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss16 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 16 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss17 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 17 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss18 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 18 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss19 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 19 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss20 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 20 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss21 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 21 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss22 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 22 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss23 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 23 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss24 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 24 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss25 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 25 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss26 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 26 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss27 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 27 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss28 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 28 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss29 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 29 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss30 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 30 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss31 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 31 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss32 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 32 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss33 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 33 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss34 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 34 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss35 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 35 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss36 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 36 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss37 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 37 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss38 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 38 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss39 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 39 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss40 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 40 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss41 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 41 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss42 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 42 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss43 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 43 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss44 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 44 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss45 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 45 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss46 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 46 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss47 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 47 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss48 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 48 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss49 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 49 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss50 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 50 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss51 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 51 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss52 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 52 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss53 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 53 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss54 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 54 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss55 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 55 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss56 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 56 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss57 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 57 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss58 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 58 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss59 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 59 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss60 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 60 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss61 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 61 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss62 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 62 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss63 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 63 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss64 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 64 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss65 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 65 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss66 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 66 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss67 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 67 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss68 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 68 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss69 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 69 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss70 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 70 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss71 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 71 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss72 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 72 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss73 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 73 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss74 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 74 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss75 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 75 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss76 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 76 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss77 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 77 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss78 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 78 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss79 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 79 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss80 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 80 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss81 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 81 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss82 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 82 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss83 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 83 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss84 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 84 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss85 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 85 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss86 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 86 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss87 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 87 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss88 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 88 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss89 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 89 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss90 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 90 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss91 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 91 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss92 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 92 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss93 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 93 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss94 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 94 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss95 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 95 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss96 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 96 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss97 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 97 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss98 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 98 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss99 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 99 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss100 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 100 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss101 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 101 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss102 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 102 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss103 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 103 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss104 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 104 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss105 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 105 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss106 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 106 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss107 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 107 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss108 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 108 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss109 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 109 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss110 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 110 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss111 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 111 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss112 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 112 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss113 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 113 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss114 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 114 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss115 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 115 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss116 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 116 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss117 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 117 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss118 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 118 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss119 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 119 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss120 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 120 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss121 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 121 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss122 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 122 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss123 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 123 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss124 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 124 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss125 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 125 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss126 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 126 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss127 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 127 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss128 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 128 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss129 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 129 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss130 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 130 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss131 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 131 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss132 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 132 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss133 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 133 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss134 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 134 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss135 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 135 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss136 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 136 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss137 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 137 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss138 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 138 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss139 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 139 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss140 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 140 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss141 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 141 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss142 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 142 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss143 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 143 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss144 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 144 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss145 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 145 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss146 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 146 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss147 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 147 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss148 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 148 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss149 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 149 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss150 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 150 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss151 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 151 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss152 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 152 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss153 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 153 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss154 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 154 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss155 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 155 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss156 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 156 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss157 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 157 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss158 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 158 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss159 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 159 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss160 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 160 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss161 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 161 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss162 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 162 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss163 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 163 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss164 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 164 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss165 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 165 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss166 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 166 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss167 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 167 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss168 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 168 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss169 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 169 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss170 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 170 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss171 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 171 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss172 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 172 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss173 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 173 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLoss174 :
    observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) 174 replayPath =
      ratToReal ((3292120129 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    constantTrainBaseRatePredictionsQ]

theorem observedConstantTrainBaseRateLossPrefix0 :
    (∑ i ∈ Finset.range 0, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) = ratToReal 0 := by
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix1 :
    (∑ i ∈ Finset.range 1, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix0,
    observedConstantTrainBaseRateLoss0]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix2 :
    (∑ i ∈ Finset.range 2, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((20341320129 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix1,
    observedConstantTrainBaseRateLoss1]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix3 :
    (∑ i ∈ Finset.range 3, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((61023960387 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix2,
    observedConstantTrainBaseRateLoss2]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix4 :
    (∑ i ∈ Finset.range 4, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((16079020129 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix3,
    observedConstantTrainBaseRateLoss3]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix5 :
    (∑ i ∈ Finset.range 5, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((13521640129 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix4,
    observedConstantTrainBaseRateLoss4]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix6 :
    (∑ i ∈ Finset.range 6, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((43974760387 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix5,
    observedConstantTrainBaseRateLoss5]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix7 :
    (∑ i ∈ Finset.range 7, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((91241640903 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix6,
    observedConstantTrainBaseRateLoss6]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix8 :
    (∑ i ∈ Finset.range 8, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((13947870129 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix7,
    observedConstantTrainBaseRateLoss7]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix9 :
    (∑ i ∈ Finset.range 9, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((131924281161 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix8,
    observedConstantTrainBaseRateLoss8]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix10 :
    (∑ i ∈ Finset.range 10, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((15226560129 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix9,
    observedConstantTrainBaseRateLoss9]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix11 :
    (∑ i ∈ Finset.range 11, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((172606921419 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix10,
    observedConstantTrainBaseRateLoss10]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix12 :
    (∑ i ∈ Finset.range 12, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((48237060387 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix11,
    observedConstantTrainBaseRateLoss11]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix13 :
    (∑ i ∈ Finset.range 13, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((196240361677 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix12,
    observedConstantTrainBaseRateLoss12]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix14 :
    (∑ i ∈ Finset.range 14, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((99766240903 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix13,
    observedConstantTrainBaseRateLoss13]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix15 :
    (∑ i ∈ Finset.range 15, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((43974760387 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix14,
    observedConstantTrainBaseRateLoss14]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix16 :
    (∑ i ∈ Finset.range 16, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((13947870129 : Rat) / 2500000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix15,
    observedConstantTrainBaseRateLoss15]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix17 :
    (∑ i ∈ Finset.range 17, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((226458042193 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix16,
    observedConstantTrainBaseRateLoss16]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix18 :
    (∑ i ∈ Finset.range 18, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((114875081161 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix17,
    observedConstantTrainBaseRateLoss17]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix19 :
    (∑ i ∈ Finset.range 19, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((233042282451 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix18,
    observedConstantTrainBaseRateLoss18]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix20 :
    (∑ i ∈ Finset.range 20, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((11816720129 : Rat) / 2000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix19,
    observedConstantTrainBaseRateLoss19]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix21 :
    (∑ i ∈ Finset.range 21, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((239626522709 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix20,
    observedConstantTrainBaseRateLoss20]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix22 :
    (∑ i ∈ Finset.range 22, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((129983921419 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix21,
    observedConstantTrainBaseRateLoss21]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix23 :
    (∑ i ∈ Finset.range 23, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((280309162967 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix22,
    observedConstantTrainBaseRateLoss22]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix24 :
    (∑ i ∈ Finset.range 24, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((37581310387 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix23,
    observedConstantTrainBaseRateLoss23]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix25 :
    (∑ i ∈ Finset.range 25, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((12157704129 : Rat) / 1600000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix24,
    observedConstantTrainBaseRateLoss24]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix26 :
    (∑ i ∈ Finset.range 26, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((153617361677 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix25,
    observedConstantTrainBaseRateLoss25]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix27 :
    (∑ i ∈ Finset.range 27, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((310526843483 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix26,
    observedConstantTrainBaseRateLoss26]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix28 :
    (∑ i ∈ Finset.range 28, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((78454740903 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix27,
    observedConstantTrainBaseRateLoss27]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix29 :
    (∑ i ∈ Finset.range 29, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((317111083741 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix28,
    observedConstantTrainBaseRateLoss28]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix30 :
    (∑ i ∈ Finset.range 30, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((32040320387 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix29,
    observedConstantTrainBaseRateLoss29]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix31 :
    (∑ i ∈ Finset.range 31, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((323695323999 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix30,
    observedConstantTrainBaseRateLoss30]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix32 :
    (∑ i ∈ Finset.range 32, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((10218357629 : Rat) / 1250000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix31,
    observedConstantTrainBaseRateLoss31]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix33 :
    (∑ i ∈ Finset.range 33, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((330279564257 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix32,
    observedConstantTrainBaseRateLoss32]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix34 :
    (∑ i ∈ Finset.range 34, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((166785842193 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix33,
    observedConstantTrainBaseRateLoss33]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix35 :
    (∑ i ∈ Finset.range 35, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((67372760903 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix34,
    observedConstantTrainBaseRateLoss34]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix36 :
    (∑ i ∈ Finset.range 36, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((85038981161 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix35,
    observedConstantTrainBaseRateLoss35]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix37 :
    (∑ i ∈ Finset.range 37, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((343448044773 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix36,
    observedConstantTrainBaseRateLoss36]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix38 :
    (∑ i ∈ Finset.range 38, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((181894682451 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix37,
    observedConstantTrainBaseRateLoss37]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix39 :
    (∑ i ∈ Finset.range 39, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((384130685031 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix38,
    observedConstantTrainBaseRateLoss38]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix40 :
    (∑ i ∈ Finset.range 40, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((9685570129 : Rat) / 1000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix39,
    observedConstantTrainBaseRateLoss39]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix41 :
    (∑ i ∈ Finset.range 41, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((390714925289 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix40,
    observedConstantTrainBaseRateLoss40]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix42 :
    (∑ i ∈ Finset.range 42, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((197003522709 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix41,
    observedConstantTrainBaseRateLoss41]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix43 :
    (∑ i ∈ Finset.range 43, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((397299165547 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix42,
    observedConstantTrainBaseRateLoss42]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix44 :
    (∑ i ∈ Finset.range 44, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((100147821419 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix43,
    observedConstantTrainBaseRateLoss43]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix45 :
    (∑ i ∈ Finset.range 45, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((80776681161 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix44,
    observedConstantTrainBaseRateLoss44]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix46 :
    (∑ i ∈ Finset.range 46, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((203587762967 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix45,
    observedConstantTrainBaseRateLoss45]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix47 :
    (∑ i ∈ Finset.range 47, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((410467646063 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix46,
    observedConstantTrainBaseRateLoss46]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix48 :
    (∑ i ∈ Finset.range 48, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((25859985387 : Rat) / 2500000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix47,
    observedConstantTrainBaseRateLoss47]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix49 :
    (∑ i ∈ Finset.range 49, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((417051886321 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix48,
    observedConstantTrainBaseRateLoss48]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix50 :
    (∑ i ∈ Finset.range 50, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((8406880129 : Rat) / 800000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix49,
    observedConstantTrainBaseRateLoss49]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix51 :
    (∑ i ∈ Finset.range 51, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((423636126579 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix50,
    observedConstantTrainBaseRateLoss50]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix52 :
    (∑ i ∈ Finset.range 52, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((106732061677 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix51,
    observedConstantTrainBaseRateLoss51]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix53 :
    (∑ i ∈ Finset.range 53, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((430220366837 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix52,
    observedConstantTrainBaseRateLoss52]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix54 :
    (∑ i ∈ Finset.range 54, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((216756243483 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix53,
    observedConstantTrainBaseRateLoss53]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix55 :
    (∑ i ∈ Finset.range 55, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((87360921419 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix54,
    observedConstantTrainBaseRateLoss54]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix56 :
    (∑ i ∈ Finset.range 56, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((55012090903 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix55,
    observedConstantTrainBaseRateLoss55]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix57 :
    (∑ i ∈ Finset.range 57, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((443388847353 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix56,
    observedConstantTrainBaseRateLoss56]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix58 :
    (∑ i ∈ Finset.range 58, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((223340483741 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix57,
    observedConstantTrainBaseRateLoss57]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix59 :
    (∑ i ∈ Finset.range 59, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((449973087611 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix58,
    observedConstantTrainBaseRateLoss58]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix60 :
    (∑ i ∈ Finset.range 60, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((22663260387 : Rat) / 2000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix59,
    observedConstantTrainBaseRateLoss59]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix61 :
    (∑ i ∈ Finset.range 61, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((456557327869 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix60,
    observedConstantTrainBaseRateLoss60]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix62 :
    (∑ i ∈ Finset.range 62, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((229924723999 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix61,
    observedConstantTrainBaseRateLoss61]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix63 :
    (∑ i ∈ Finset.range 63, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((463141568127 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix62,
    observedConstantTrainBaseRateLoss62]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix64 :
    (∑ i ∈ Finset.range 64, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((7288026379 : Rat) / 625000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix63,
    observedConstantTrainBaseRateLoss63]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix65 :
    (∑ i ∈ Finset.range 65, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((93945161677 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix64,
    observedConstantTrainBaseRateLoss64]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix66 :
    (∑ i ∈ Finset.range 66, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((236508964257 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix65,
    observedConstantTrainBaseRateLoss65]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix67 :
    (∑ i ∈ Finset.range 67, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((476310048643 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix66,
    observedConstantTrainBaseRateLoss66]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix68 :
    (∑ i ∈ Finset.range 68, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((119900542193 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix67,
    observedConstantTrainBaseRateLoss67]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix69 :
    (∑ i ∈ Finset.range 69, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((482894288901 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix68,
    observedConstantTrainBaseRateLoss68]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix70 :
    (∑ i ∈ Finset.range 70, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((48618640903 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix69,
    observedConstantTrainBaseRateLoss69]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix71 :
    (∑ i ∈ Finset.range 71, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((489478529159 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix70,
    observedConstantTrainBaseRateLoss70]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix72 :
    (∑ i ∈ Finset.range 72, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((61596331161 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix71,
    observedConstantTrainBaseRateLoss71]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix73 :
    (∑ i ∈ Finset.range 73, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((496062769417 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix72,
    observedConstantTrainBaseRateLoss72]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix74 :
    (∑ i ∈ Finset.range 74, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((249677444773 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix73,
    observedConstantTrainBaseRateLoss73]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix75 :
    (∑ i ∈ Finset.range 75, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((20105880387 : Rat) / 1600000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix74,
    observedConstantTrainBaseRateLoss74]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix76 :
    (∑ i ∈ Finset.range 76, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((126484782451 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix75,
    observedConstantTrainBaseRateLoss75]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix77 :
    (∑ i ∈ Finset.range 77, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((509231249933 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix76,
    observedConstantTrainBaseRateLoss76]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix78 :
    (∑ i ∈ Finset.range 78, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((256261685031 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix77,
    observedConstantTrainBaseRateLoss77]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix79 :
    (∑ i ∈ Finset.range 79, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((515815490191 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix78,
    observedConstantTrainBaseRateLoss78]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix80 :
    (∑ i ∈ Finset.range 80, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((6488845129 : Rat) / 500000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix79,
    observedConstantTrainBaseRateLoss79]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix81 :
    (∑ i ∈ Finset.range 81, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((539448930449 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix80,
    observedConstantTrainBaseRateLoss80]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix82 :
    (∑ i ∈ Finset.range 82, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((279895125289 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix81,
    observedConstantTrainBaseRateLoss81]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix83 :
    (∑ i ∈ Finset.range 83, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((563082370707 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix82,
    observedConstantTrainBaseRateLoss82]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix84 :
    (∑ i ∈ Finset.range 84, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((145855922709 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix83,
    observedConstantTrainBaseRateLoss83]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix85 :
    (∑ i ∈ Finset.range 85, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((117343162193 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix84,
    observedConstantTrainBaseRateLoss84]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix86 :
    (∑ i ∈ Finset.range 86, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((303528565547 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix85,
    observedConstantTrainBaseRateLoss85]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix87 :
    (∑ i ∈ Finset.range 87, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((627398451223 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix86,
    observedConstantTrainBaseRateLoss86]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix88 :
    (∑ i ∈ Finset.range 88, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((80967471419 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix87,
    observedConstantTrainBaseRateLoss87]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix89 :
    (∑ i ∈ Finset.range 89, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((668081091481 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix88,
    observedConstantTrainBaseRateLoss88]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix90 :
    (∑ i ∈ Finset.range 90, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((68842241161 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix89,
    observedConstantTrainBaseRateLoss89]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix91 :
    (∑ i ∈ Finset.range 91, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((708763731739 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix90,
    observedConstantTrainBaseRateLoss90]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix92 :
    (∑ i ∈ Finset.range 92, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((182276262967 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix91,
    observedConstantTrainBaseRateLoss91]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix93 :
    (∑ i ∈ Finset.range 93, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((749446371997 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix92,
    observedConstantTrainBaseRateLoss92]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix94 :
    (∑ i ∈ Finset.range 94, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((384893846063 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix93,
    observedConstantTrainBaseRateLoss93]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix95 :
    (∑ i ∈ Finset.range 95, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((154615962451 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix94,
    observedConstantTrainBaseRateLoss94]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix96 :
    (∑ i ∈ Finset.range 96, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((24794410387 : Rat) / 1250000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix95,
    observedConstantTrainBaseRateLoss95]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix97 :
    (∑ i ∈ Finset.range 97, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((813762452513 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix96,
    observedConstantTrainBaseRateLoss96]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix98 :
    (∑ i ∈ Finset.range 98, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((417051886321 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix97,
    observedConstantTrainBaseRateLoss97]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix99 :
    (∑ i ∈ Finset.range 99, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((837395892771 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix98,
    observedConstantTrainBaseRateLoss98]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix100 :
    (∑ i ∈ Finset.range 100, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((8406880129 : Rat) / 400000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix99,
    observedConstantTrainBaseRateLoss99]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix101 :
    (∑ i ∈ Finset.range 101, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((843980133029 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix100,
    observedConstantTrainBaseRateLoss100]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix102 :
    (∑ i ∈ Finset.range 102, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((423636126579 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix101,
    observedConstantTrainBaseRateLoss101]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix103 :
    (∑ i ∈ Finset.range 103, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((850564373287 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix102,
    observedConstantTrainBaseRateLoss102]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix104 :
    (∑ i ∈ Finset.range 104, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((106732061677 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix103,
    observedConstantTrainBaseRateLoss103]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix105 :
    (∑ i ∈ Finset.range 105, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((171429722709 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix104,
    observedConstantTrainBaseRateLoss104]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix106 :
    (∑ i ∈ Finset.range 106, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((430220366837 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix105,
    observedConstantTrainBaseRateLoss105]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix107 :
    (∑ i ∈ Finset.range 107, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((863732853803 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix106,
    observedConstantTrainBaseRateLoss106]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix108 :
    (∑ i ∈ Finset.range 108, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((216756243483 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix107,
    observedConstantTrainBaseRateLoss107]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix109 :
    (∑ i ∈ Finset.range 109, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((887366294061 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix108,
    observedConstantTrainBaseRateLoss108]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix110 :
    (∑ i ∈ Finset.range 110, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((90770761419 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix109,
    observedConstantTrainBaseRateLoss109]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix111 :
    (∑ i ∈ Finset.range 111, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((928048934319 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix110,
    observedConstantTrainBaseRateLoss110]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix112 :
    (∑ i ∈ Finset.range 112, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((58208815903 : Rat) / 2500000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix111,
    observedConstantTrainBaseRateLoss111]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix113 :
    (∑ i ∈ Finset.range 113, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((951682374577 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix112,
    observedConstantTrainBaseRateLoss112]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix114 :
    (∑ i ∈ Finset.range 114, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((486011847353 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix113,
    observedConstantTrainBaseRateLoss113]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix115 :
    (∑ i ∈ Finset.range 115, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((195063162967 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix114,
    observedConstantTrainBaseRateLoss114]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix116 :
    (∑ i ∈ Finset.range 116, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((244651983741 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix115,
    observedConstantTrainBaseRateLoss115]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix117 :
    (∑ i ∈ Finset.range 117, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((981900055093 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix116,
    observedConstantTrainBaseRateLoss116]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix118 :
    (∑ i ∈ Finset.range 118, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((501120687611 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix117,
    observedConstantTrainBaseRateLoss117]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix119 :
    (∑ i ∈ Finset.range 119, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1022582695351 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix118,
    observedConstantTrainBaseRateLoss118]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix120 :
    (∑ i ∈ Finset.range 120, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((26073100387 : Rat) / 1000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix119,
    observedConstantTrainBaseRateLoss119]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix121 :
    (∑ i ∈ Finset.range 121, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1063265335609 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix120,
    observedConstantTrainBaseRateLoss120]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix122 :
    (∑ i ∈ Finset.range 122, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((533278727869 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix121,
    observedConstantTrainBaseRateLoss121]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix123 :
    (∑ i ∈ Finset.range 123, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1069849575867 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix122,
    observedConstantTrainBaseRateLoss122]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix124 :
    (∑ i ∈ Finset.range 124, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((268285423999 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix123,
    observedConstantTrainBaseRateLoss123]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix125 :
    (∑ i ∈ Finset.range 125, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((8611470529 : Rat) / 320000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix124,
    observedConstantTrainBaseRateLoss124]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix126 :
    (∑ i ∈ Finset.range 126, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((539862968127 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix125,
    observedConstantTrainBaseRateLoss125]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix127 :
    (∑ i ∈ Finset.range 127, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1083018056383 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix126,
    observedConstantTrainBaseRateLoss126]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix128 :
    (∑ i ∈ Finset.range 128, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((8619995129 : Rat) / 312500000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix127,
    observedConstantTrainBaseRateLoss127]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix129 :
    (∑ i ∈ Finset.range 129, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1123700696641 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix128,
    observedConstantTrainBaseRateLoss128]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix130 :
    (∑ i ∈ Finset.range 130, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((112699281677 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix129,
    observedConstantTrainBaseRateLoss129]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix131 :
    (∑ i ∈ Finset.range 131, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1130284936899 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix130,
    observedConstantTrainBaseRateLoss130]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix132 :
    (∑ i ∈ Finset.range 132, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((283394264257 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix131,
    observedConstantTrainBaseRateLoss131]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix133 :
    (∑ i ∈ Finset.range 133, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1136869177157 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix132,
    observedConstantTrainBaseRateLoss132]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix134 :
    (∑ i ∈ Finset.range 134, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((570080648643 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix133,
    observedConstantTrainBaseRateLoss133]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix135 :
    (∑ i ∈ Finset.range 135, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((228690683483 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix134,
    observedConstantTrainBaseRateLoss134]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix136 :
    (∑ i ∈ Finset.range 136, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((143343192193 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix135,
    observedConstantTrainBaseRateLoss135]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix137 :
    (∑ i ∈ Finset.range 137, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1150037657673 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix136,
    observedConstantTrainBaseRateLoss136]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix138 :
    (∑ i ∈ Finset.range 138, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((576664888901 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix137,
    observedConstantTrainBaseRateLoss137]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix139 :
    (∑ i ∈ Finset.range 139, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1156621897931 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix138,
    observedConstantTrainBaseRateLoss138]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix140 :
    (∑ i ∈ Finset.range 140, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((57995700903 : Rat) / 2000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix139,
    observedConstantTrainBaseRateLoss139]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix141 :
    (∑ i ∈ Finset.range 141, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1163206138189 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix140,
    observedConstantTrainBaseRateLoss140]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix142 :
    (∑ i ∈ Finset.range 142, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((583249129159 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix141,
    observedConstantTrainBaseRateLoss141]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix143 :
    (∑ i ∈ Finset.range 143, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1169790378447 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix142,
    observedConstantTrainBaseRateLoss142]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix144 :
    (∑ i ∈ Finset.range 144, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((73317656161 : Rat) / 2500000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix143,
    observedConstantTrainBaseRateLoss143]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix145 :
    (∑ i ∈ Finset.range 145, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((235274923741 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix144,
    observedConstantTrainBaseRateLoss144]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix146 :
    (∑ i ∈ Finset.range 146, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((589833369417 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix145,
    observedConstantTrainBaseRateLoss145]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix147 :
    (∑ i ∈ Finset.range 147, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1182958858963 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix146,
    observedConstantTrainBaseRateLoss146]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix148 :
    (∑ i ∈ Finset.range 148, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((296562744773 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix147,
    observedConstantTrainBaseRateLoss147]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix149 :
    (∑ i ∈ Finset.range 149, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1189543099221 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix148,
    observedConstantTrainBaseRateLoss148]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix150 :
    (∑ i ∈ Finset.range 150, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((23856704387 : Rat) / 800000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix149,
    observedConstantTrainBaseRateLoss149]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix151 :
    (∑ i ∈ Finset.range 151, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1196127339479 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix150,
    observedConstantTrainBaseRateLoss150]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix152 :
    (∑ i ∈ Finset.range 152, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((149927432451 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix151,
    observedConstantTrainBaseRateLoss151]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix153 :
    (∑ i ∈ Finset.range 153, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1202711579737 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix152,
    observedConstantTrainBaseRateLoss152]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix154 :
    (∑ i ∈ Finset.range 154, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((603001849933 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix153,
    observedConstantTrainBaseRateLoss153]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix155 :
    (∑ i ∈ Finset.range 155, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((241859163999 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix154,
    observedConstantTrainBaseRateLoss154]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix156 :
    (∑ i ∈ Finset.range 156, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((303146985031 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix155,
    observedConstantTrainBaseRateLoss155]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix157 :
    (∑ i ∈ Finset.range 157, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1215880060253 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix156,
    observedConstantTrainBaseRateLoss156]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix158 :
    (∑ i ∈ Finset.range 158, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((609586090191 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix157,
    observedConstantTrainBaseRateLoss157]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix159 :
    (∑ i ∈ Finset.range 159, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1222464300511 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix158,
    observedConstantTrainBaseRateLoss158]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix160 :
    (∑ i ∈ Finset.range 160, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((7660977629 : Rat) / 250000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix159,
    observedConstantTrainBaseRateLoss159]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix161 :
    (∑ i ∈ Finset.range 161, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1229048540769 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix160,
    observedConstantTrainBaseRateLoss160]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix162 :
    (∑ i ∈ Finset.range 162, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((616170330449 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix161,
    observedConstantTrainBaseRateLoss161]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix163 :
    (∑ i ∈ Finset.range 163, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1235632781027 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix162,
    observedConstantTrainBaseRateLoss162]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix164 :
    (∑ i ∈ Finset.range 164, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((309731225289 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix163,
    observedConstantTrainBaseRateLoss163]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix165 :
    (∑ i ∈ Finset.range 165, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((248443404257 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix164,
    observedConstantTrainBaseRateLoss164]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix166 :
    (∑ i ∈ Finset.range 166, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((622754570707 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix165,
    observedConstantTrainBaseRateLoss165]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix167 :
    (∑ i ∈ Finset.range 167, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1248801261543 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix166,
    observedConstantTrainBaseRateLoss166]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix168 :
    (∑ i ∈ Finset.range 168, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((156511672709 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix167,
    observedConstantTrainBaseRateLoss167]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix169 :
    (∑ i ∈ Finset.range 169, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1255385501801 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix168,
    observedConstantTrainBaseRateLoss168]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix170 :
    (∑ i ∈ Finset.range 170, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((125867762193 : Rat) / 4000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix169,
    observedConstantTrainBaseRateLoss169]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix171 :
    (∑ i ∈ Finset.range 171, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1261969742059 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix170,
    observedConstantTrainBaseRateLoss170]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix172 :
    (∑ i ∈ Finset.range 172, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((316315465547 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix171,
    observedConstantTrainBaseRateLoss171]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix173 :
    (∑ i ∈ Finset.range 173, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((1268553982317 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix172,
    observedConstantTrainBaseRateLoss172]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix174 :
    (∑ i ∈ Finset.range 174, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((635923051223 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix173,
    observedConstantTrainBaseRateLoss173]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateLossPrefix175 :
    (∑ i ∈ Finset.range 175, observedTrajectoryScore
        (monitorBrierScore constantTrainBaseRate) i replayPath) =
      ratToReal ((51005528903 : Rat) / 1600000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateLossPrefix174,
    observedConstantTrainBaseRateLoss174]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor0 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 0 replayPath =
      ratToReal ((1 : Rat) / 2) := by
  norm_num [forwardPredictorProcess, forwardPredictor, ratToReal]

theorem observedConstantTrainBaseRatePredictor1 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 1 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix1]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor2 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 2 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix2]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor3 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 3 replayPath =
      ratToReal ((20341320129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix3]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor4 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 4 replayPath =
      ratToReal ((16079020129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix4]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor5 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 5 replayPath =
      ratToReal ((13521640129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix5]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor6 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 6 replayPath =
      ratToReal ((43974760387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix6]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor7 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 7 replayPath =
      ratToReal ((13034520129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix7]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor8 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 8 replayPath =
      ratToReal ((13947870129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix8]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor9 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 9 replayPath =
      ratToReal ((43974760387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix9]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor10 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 10 replayPath =
      ratToReal ((15226560129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix10]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor11 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 11 replayPath =
      ratToReal ((172606921419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix11]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor12 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 12 replayPath =
      ratToReal ((16079020129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix12]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor13 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 13 replayPath =
      ratToReal ((196240361677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix13]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor14 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 14 replayPath =
      ratToReal ((14252320129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix14]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor15 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 15 replayPath =
      ratToReal ((43974760387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix15]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor16 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 16 replayPath =
      ratToReal ((13947870129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix16]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor17 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 17 replayPath =
      ratToReal ((226458042193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix17]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor18 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 18 replayPath =
      ratToReal ((114875081161 : Rat) / 360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix18]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor19 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 19 replayPath =
      ratToReal ((233042282451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix19]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor20 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 20 replayPath =
      ratToReal ((11816720129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix20]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor21 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 21 replayPath =
      ratToReal ((34232360387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix21]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor22 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 22 replayPath =
      ratToReal ((11816720129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix22]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor23 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 23 replayPath =
      ratToReal ((280309162967 : Rat) / 920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix23]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor24 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 24 replayPath =
      ratToReal ((37581310387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix24]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor25 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 25 replayPath =
      ratToReal ((12157704129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix25]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor26 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 26 replayPath =
      ratToReal ((11816720129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix26]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor27 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 27 replayPath =
      ratToReal ((310526843483 : Rat) / 1080000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix27]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor28 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 28 replayPath =
      ratToReal ((11207820129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix28]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor29 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 29 replayPath =
      ratToReal ((317111083741 : Rat) / 1160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix29]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor30 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 30 replayPath =
      ratToReal ((32040320387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix30]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor31 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 31 replayPath =
      ratToReal ((323695323999 : Rat) / 1240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix31]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor32 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 32 replayPath =
      ratToReal ((10218357629 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix32]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor33 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 33 replayPath =
      ratToReal ((330279564257 : Rat) / 1320000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix33]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor34 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 34 replayPath =
      ratToReal ((166785842193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix34]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor35 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 35 replayPath =
      ratToReal ((9624680129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix35]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor36 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 36 replayPath =
      ratToReal ((85038981161 : Rat) / 360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix36]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor37 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 37 replayPath =
      ratToReal ((343448044773 : Rat) / 1480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix37]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor38 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 38 replayPath =
      ratToReal ((181894682451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix38]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor39 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 39 replayPath =
      ratToReal ((128043561677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix39]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor40 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 40 replayPath =
      ratToReal ((9685570129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix40]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor41 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 41 replayPath =
      ratToReal ((390714925289 : Rat) / 1640000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix41]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor42 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 42 replayPath =
      ratToReal ((9381120129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix42]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor43 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 43 replayPath =
      ratToReal ((397299165547 : Rat) / 1720000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix43]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor44 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 44 replayPath =
      ratToReal ((100147821419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix44]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor45 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 45 replayPath =
      ratToReal ((26925560387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix45]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor46 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 46 replayPath =
      ratToReal ((203587762967 : Rat) / 920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix46]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor47 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 47 replayPath =
      ratToReal ((410467646063 : Rat) / 1880000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix47]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor48 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 48 replayPath =
      ratToReal ((8619995129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix48]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor49 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 49 replayPath =
      ratToReal ((59578840903 : Rat) / 280000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix49]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor50 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 50 replayPath =
      ratToReal ((8406880129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix50]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor51 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 51 replayPath =
      ratToReal ((141212042193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix51]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor52 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 52 replayPath =
      ratToReal ((106732061677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix52]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor53 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 53 replayPath =
      ratToReal ((430220366837 : Rat) / 2120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix53]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor54 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 54 replayPath =
      ratToReal ((72252081161 : Rat) / 360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix54]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor55 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 55 replayPath =
      ratToReal ((87360921419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix55]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor56 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 56 replayPath =
      ratToReal ((7858870129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix56]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor57 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 57 replayPath =
      ratToReal ((147796282451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix57]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor58 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 58 replayPath =
      ratToReal ((223340483741 : Rat) / 1160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix58]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor59 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 59 replayPath =
      ratToReal ((449973087611 : Rat) / 2360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix59]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor60 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 60 replayPath =
      ratToReal ((7554420129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix60]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor61 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 61 replayPath =
      ratToReal ((456557327869 : Rat) / 2440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix61]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor62 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 62 replayPath =
      ratToReal ((229924723999 : Rat) / 1240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix62]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor63 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 63 replayPath =
      ratToReal ((22054360387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix63]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor64 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 64 replayPath =
      ratToReal ((7288026379 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix64]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor65 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 65 replayPath =
      ratToReal ((93945161677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix65]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor66 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 66 replayPath =
      ratToReal ((78836321419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix66]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor67 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 67 replayPath =
      ratToReal ((476310048643 : Rat) / 2680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix67]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor68 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 68 replayPath =
      ratToReal ((119900542193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix68]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor69 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 69 replayPath =
      ratToReal ((160964762967 : Rat) / 920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix69]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor70 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 70 replayPath =
      ratToReal ((6945520129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix70]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor71 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 71 replayPath =
      ratToReal ((489478529159 : Rat) / 2840000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix71]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor72 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 72 replayPath =
      ratToReal ((20532110387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix72]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor73 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 73 replayPath =
      ratToReal ((496062769417 : Rat) / 2920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix73]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor74 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 74 replayPath =
      ratToReal ((249677444773 : Rat) / 1480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix74]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor75 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 75 replayPath =
      ratToReal ((6701960129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix75]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor76 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 76 replayPath =
      ratToReal ((126484782451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix76]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor77 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 77 replayPath =
      ratToReal ((72747321419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix77]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor78 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 78 replayPath =
      ratToReal ((85420561677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix78]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor79 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 79 replayPath =
      ratToReal ((515815490191 : Rat) / 3160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix79]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor80 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 80 replayPath =
      ratToReal ((6488845129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix80]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor81 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 81 replayPath =
      ratToReal ((539448930449 : Rat) / 3240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix81]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor82 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 82 replayPath =
      ratToReal ((279895125289 : Rat) / 1640000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix82]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor83 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 83 replayPath =
      ratToReal ((563082370707 : Rat) / 3320000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix83]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor84 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 84 replayPath =
      ratToReal ((6945520129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix84]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor85 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 85 replayPath =
      ratToReal ((117343162193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix85]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor86 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 86 replayPath =
      ratToReal ((303528565547 : Rat) / 1720000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix86]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor87 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 87 replayPath =
      ratToReal ((627398451223 : Rat) / 3480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix87]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor88 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 88 replayPath =
      ratToReal ((80967471419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix88]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor89 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 89 replayPath =
      ratToReal ((668081091481 : Rat) / 3560000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix89]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor90 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 90 replayPath =
      ratToReal ((68842241161 : Rat) / 360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix90]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor91 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 91 replayPath =
      ratToReal ((101251961677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix91]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor92 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 92 replayPath =
      ratToReal ((182276262967 : Rat) / 920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix92]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor93 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 93 replayPath =
      ratToReal ((749446371997 : Rat) / 3720000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix93]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor94 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 94 replayPath =
      ratToReal ((384893846063 : Rat) / 1880000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix94]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor95 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 95 replayPath =
      ratToReal ((154615962451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix95]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor96 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 96 replayPath =
      ratToReal ((24794410387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix96]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor97 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 97 replayPath =
      ratToReal ((813762452513 : Rat) / 3880000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix97]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor98 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 98 replayPath =
      ratToReal ((59578840903 : Rat) / 280000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix98]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor99 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 99 replayPath =
      ratToReal ((279131964257 : Rat) / 1320000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix99]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor100 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 100 replayPath =
      ratToReal ((8406880129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix100]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor101 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 101 replayPath =
      ratToReal ((843980133029 : Rat) / 4040000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix101]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor102 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 102 replayPath =
      ratToReal ((141212042193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix102]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor103 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 103 replayPath =
      ratToReal ((850564373287 : Rat) / 4120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix103]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor104 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 104 replayPath =
      ratToReal ((106732061677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix104]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor105 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 105 replayPath =
      ratToReal ((8163320129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix105]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor106 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 106 replayPath =
      ratToReal ((430220366837 : Rat) / 2120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix106]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor107 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 107 replayPath =
      ratToReal ((863732853803 : Rat) / 4280000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix107]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor108 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 108 replayPath =
      ratToReal ((72252081161 : Rat) / 360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix108]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor109 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 109 replayPath =
      ratToReal ((887366294061 : Rat) / 4360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix109]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor110 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 110 replayPath =
      ratToReal ((90770761419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix110]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor111 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 111 replayPath =
      ratToReal ((309349644773 : Rat) / 1480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix111]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor112 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 112 replayPath =
      ratToReal ((8315545129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix112]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor113 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 113 replayPath =
      ratToReal ((951682374577 : Rat) / 4520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix113]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor114 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 114 replayPath =
      ratToReal ((486011847353 : Rat) / 2280000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix114]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor115 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 115 replayPath =
      ratToReal ((195063162967 : Rat) / 920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix115]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor116 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 116 replayPath =
      ratToReal ((244651983741 : Rat) / 1160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix116]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor117 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 117 replayPath =
      ratToReal ((981900055093 : Rat) / 4680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix117]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor118 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 118 replayPath =
      ratToReal ((501120687611 : Rat) / 2360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix118]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor119 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 119 replayPath =
      ratToReal ((146083242193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix119]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor120 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 120 replayPath =
      ratToReal ((26073100387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix120]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor121 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 121 replayPath =
      ratToReal ((1063265335609 : Rat) / 4840000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix121]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor122 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 122 replayPath =
      ratToReal ((533278727869 : Rat) / 2440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix122]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor123 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 123 replayPath =
      ratToReal ((356616525289 : Rat) / 1640000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix123]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor124 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 124 replayPath =
      ratToReal ((268285423999 : Rat) / 1240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix124]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor125 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 125 replayPath =
      ratToReal ((8611470529 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix125]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor126 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 126 replayPath =
      ratToReal ((25707760387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix126]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor127 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 127 replayPath =
      ratToReal ((1083018056383 : Rat) / 5080000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix127]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor128 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 128 replayPath =
      ratToReal ((8619995129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix128]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor129 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 129 replayPath =
      ratToReal ((1123700696641 : Rat) / 5160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix129]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor130 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 130 replayPath =
      ratToReal ((112699281677 : Rat) / 520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix130]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor131 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 131 replayPath =
      ratToReal ((1130284936899 : Rat) / 5240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix131]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor132 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 132 replayPath =
      ratToReal ((283394264257 : Rat) / 1320000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix132]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor133 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 133 replayPath =
      ratToReal ((162409882451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix133]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor134 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 134 replayPath =
      ratToReal ((570080648643 : Rat) / 2680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix134]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor135 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 135 replayPath =
      ratToReal ((228690683483 : Rat) / 1080000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix135]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor136 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 136 replayPath =
      ratToReal ((143343192193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix136]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor137 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 137 replayPath =
      ratToReal ((1150037657673 : Rat) / 5480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix137]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor138 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 138 replayPath =
      ratToReal ((576664888901 : Rat) / 2760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix138]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor139 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 139 replayPath =
      ratToReal ((1156621897931 : Rat) / 5560000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix139]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor140 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 140 replayPath =
      ratToReal ((8285100129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix140]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor141 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 141 replayPath =
      ratToReal ((1163206138189 : Rat) / 5640000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix141]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor142 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 142 replayPath =
      ratToReal ((583249129159 : Rat) / 2840000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix142]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor143 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 143 replayPath =
      ratToReal ((1169790378447 : Rat) / 5720000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix143]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor144 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 144 replayPath =
      ratToReal ((73317656161 : Rat) / 360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix144]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor145 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 145 replayPath =
      ratToReal ((235274923741 : Rat) / 1160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix145]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor146 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 146 replayPath =
      ratToReal ((589833369417 : Rat) / 2920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix146]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor147 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 147 replayPath =
      ratToReal ((168994122709 : Rat) / 840000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix147]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor148 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 148 replayPath =
      ratToReal ((296562744773 : Rat) / 1480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix148]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor149 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 149 replayPath =
      ratToReal ((1189543099221 : Rat) / 5960000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix149]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor150 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 150 replayPath =
      ratToReal ((23856704387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix150]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor151 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 151 replayPath =
      ratToReal ((1196127339479 : Rat) / 6040000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix151]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor152 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 152 replayPath =
      ratToReal ((149927432451 : Rat) / 760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix152]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor153 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 153 replayPath =
      ratToReal ((1202711579737 : Rat) / 6120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix153]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor154 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 154 replayPath =
      ratToReal ((86143121419 : Rat) / 440000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix154]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor155 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 155 replayPath =
      ratToReal ((241859163999 : Rat) / 1240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix155]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor156 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 156 replayPath =
      ratToReal ((303146985031 : Rat) / 1560000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix156]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor157 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 157 replayPath =
      ratToReal ((1215880060253 : Rat) / 6280000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix157]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor158 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 158 replayPath =
      ratToReal ((609586090191 : Rat) / 3160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix158]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor159 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 159 replayPath =
      ratToReal ((1222464300511 : Rat) / 6360000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix159]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor160 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 160 replayPath =
      ratToReal ((7660977629 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix160]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor161 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 161 replayPath =
      ratToReal ((175578362967 : Rat) / 920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix161]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor162 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 162 replayPath =
      ratToReal ((616170330449 : Rat) / 3240000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix162]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor163 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 163 replayPath =
      ratToReal ((1235632781027 : Rat) / 6520000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix163]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor164 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 164 replayPath =
      ratToReal ((7554420129 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix164]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor165 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 165 replayPath =
      ratToReal ((248443404257 : Rat) / 1320000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix165]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor166 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 166 replayPath =
      ratToReal ((622754570707 : Rat) / 3320000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix166]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor167 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 167 replayPath =
      ratToReal ((1248801261543 : Rat) / 6680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix167]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor168 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 168 replayPath =
      ratToReal ((22358810387 : Rat) / 120000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix168]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor169 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 169 replayPath =
      ratToReal ((1255385501801 : Rat) / 6760000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix169]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor170 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 170 replayPath =
      ratToReal ((125867762193 : Rat) / 680000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix170]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor171 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 171 replayPath =
      ratToReal ((1261969742059 : Rat) / 6840000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix171]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor172 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 172 replayPath =
      ratToReal ((316315465547 : Rat) / 1720000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix172]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor173 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 173 replayPath =
      ratToReal ((1268553982317 : Rat) / 6920000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix173]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRatePredictor174 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate)) 174 replayPath =
      ratToReal ((635923051223 : Rat) / 3480000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedConstantTrainBaseRateLossPrefix174]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix0 :
    (∑ i ∈ Finset.range 0,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal 0 := by
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix1 :
    (∑ i ∈ Finset.range 1,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((116499430460576641 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix0,
    observedConstantTrainBaseRateLoss0,
    observedConstantTrainBaseRatePredictor0]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix2 :
    (∑ i ∈ Finset.range 2,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((116499430460576641 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix1,
    observedConstantTrainBaseRateLoss1,
    observedConstantTrainBaseRatePredictor1]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix3 :
    (∑ i ∈ Finset.range 3,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((116499430460576641 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix2,
    observedConstantTrainBaseRateLoss2,
    observedConstantTrainBaseRatePredictor2]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix4 :
    (∑ i ∈ Finset.range 4,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((290791720070460576641 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix3,
    observedConstantTrainBaseRateLoss3,
    observedConstantTrainBaseRatePredictor3]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix5 :
    (∑ i ∈ Finset.range 5,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((454296531680460576641 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix4,
    observedConstantTrainBaseRateLoss4,
    observedConstantTrainBaseRatePredictor4]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix6 :
    (∑ i ∈ Finset.range 6,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((500804566982860576641 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix5,
    observedConstantTrainBaseRateLoss5,
    observedConstantTrainBaseRatePredictor5]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix7 :
    (∑ i ∈ Finset.range 7,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5669941985405745189769 : Rat) / 14400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix6,
    observedConstantTrainBaseRateLoss6,
    observedConstantTrainBaseRatePredictor6]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix8 :
    (∑ i ∈ Finset.range 8,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((6150445921565745189769 : Rat) / 14400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix7,
    observedConstantTrainBaseRateLoss7,
    observedConstantTrainBaseRatePredictor7]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix9 :
    (∑ i ∈ Finset.range 9,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((6518331747688245189769 : Rat) / 14400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix8,
    observedConstantTrainBaseRateLoss8,
    observedConstantTrainBaseRatePredictor8]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix10 :
    (∑ i ∈ Finset.range 10,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((6809006968328245189769 : Rat) / 14400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix9,
    observedConstantTrainBaseRateLoss9,
    observedConstantTrainBaseRatePredictor9]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix11 :
    (∑ i ∈ Finset.range 11,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7044453897046645189769 : Rat) / 14400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix10,
    observedConstantTrainBaseRateLoss10,
    observedConstantTrainBaseRatePredictor10]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix12 :
    (∑ i ∈ Finset.range 12,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((875923614414484067962049 : Rat) / 1742400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix11,
    observedConstantTrainBaseRateLoss11,
    observedConstantTrainBaseRatePredictor11]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix13 :
    (∑ i ∈ Finset.range 13,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1053980354257774067962049 : Rat) / 1742400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix12,
    observedConstantTrainBaseRateLoss12,
    observedConstantTrainBaseRatePredictor12]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix14 :
    (∑ i ∈ Finset.range 14,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((203762850406997577485586281 : Rat) / 294465600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix13,
    observedConstantTrainBaseRateLoss13,
    observedConstantTrainBaseRatePredictor13]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix15 :
    (∑ i ∈ Finset.range 15,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((210586339983758577485586281 : Rat) / 294465600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix14,
    observedConstantTrainBaseRateLoss14,
    observedConstantTrainBaseRatePredictor14]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix16 :
    (∑ i ∈ Finset.range 16,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((26040267814580890831731809 : Rat) / 32718400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix15,
    observedConstantTrainBaseRateLoss15,
    observedConstantTrainBaseRatePredictor15]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix17 :
    (∑ i ∈ Finset.range 17,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((28362149684450953331731809 : Rat) / 32718400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix16,
    observedConstantTrainBaseRateLoss16,
    observedConstantTrainBaseRatePredictor16]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix18 :
    (∑ i ∈ Finset.range 18,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((8791063017493061512870492801 : Rat) / 9455617600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix17,
    observedConstantTrainBaseRateLoss17,
    observedConstantTrainBaseRatePredictor17]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix19 :
    (∑ i ∈ Finset.range 19,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((755021631482054658542509916881 : Rat) / 765905025600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix18,
    observedConstantTrainBaseRateLoss18,
    observedConstantTrainBaseRatePredictor18]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix20 :
    (∑ i ∈ Finset.range 20,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((286477159734119534757846079994041 : Rat) / 276491714241600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix19,
    observedConstantTrainBaseRateLoss19,
    observedConstantTrainBaseRatePredictor19]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix21 :
    (∑ i ∈ Finset.range 21,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((299034861303230301987006079994041 : Rat) / 276491714241600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix20,
    observedConstantTrainBaseRateLoss20,
    observedConstantTrainBaseRatePredictor20]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix22 :
    (∑ i ∈ Finset.range 22,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((312817009964113774410846079994041 : Rat) / 276491714241600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix21,
    observedConstantTrainBaseRateLoss21,
    observedConstantTrainBaseRatePredictor21]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix23 :
    (∑ i ∈ Finset.range 23,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((325374711533224541640006079994041 : Rat) / 276491714241600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix22,
    observedConstantTrainBaseRateLoss22,
    observedConstantTrainBaseRatePredictor22]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix24 :
    (∑ i ∈ Finset.range 24,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((178201149960525393866476656316847689 : Rat) / 146264116833806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix23,
    observedConstantTrainBaseRateLoss23,
    observedConstantTrainBaseRatePredictor23]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix25 :
    (∑ i ∈ Finset.range 25,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((185997476890942558457130358816847689 : Rat) / 146264116833806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix24,
    observedConstantTrainBaseRateLoss24,
    observedConstantTrainBaseRatePredictor24]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix26 :
    (∑ i ∈ Finset.range 26,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((193182571790015017343876811040847689 : Rat) / 146264116833806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix25,
    observedConstantTrainBaseRateLoss25,
    observedConstantTrainBaseRatePredictor25]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix27 :
    (∑ i ∈ Finset.range 27,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((199825595920074613208102451040847689 : Rat) / 146264116833806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix26,
    observedConstantTrainBaseRateLoss26,
    observedConstantTrainBaseRatePredictor26]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix28 :
    (∑ i ∈ Finset.range 28,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1853870910341415800406459499367629201 : Rat) / 1316377051504257600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix27,
    observedConstantTrainBaseRateLoss27,
    observedConstantTrainBaseRatePredictor27]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix29 :
    (∑ i ∈ Finset.range 29,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1905422133309888480556904389367629201 : Rat) / 1316377051504257600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix28,
    observedConstantTrainBaseRateLoss28,
    observedConstantTrainBaseRatePredictor28]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix30 :
    (∑ i ∈ Finset.range 30,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1642876172920898793386305385218176158041 : Rat) / 1107073100315080641600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix29,
    observedConstantTrainBaseRateLoss29,
    observedConstantTrainBaseRatePredictor29]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix31 :
    (∑ i ∈ Finset.range 31,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1680642827984148405409766424720576158041 : Rat) / 1107073100315080641600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix30,
    observedConstantTrainBaseRateLoss30,
    observedConstantTrainBaseRatePredictor30]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix32 :
    (∑ i ∈ Finset.range 32,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1649087747249691268419900469708633687877401 : Rat) / 1063897249402792496577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix31,
    observedConstantTrainBaseRateLoss31,
    observedConstantTrainBaseRatePredictor31]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix33 :
    (∑ i ∈ Finset.range 33,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1680986555808484812794013216843033844127401 : Rat) / 1063897249402792496577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix32,
    observedConstantTrainBaseRateLoss32,
    observedConstantTrainBaseRatePredictor32]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix34 :
    (∑ i ∈ Finset.range 34,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1710981395077726860029175249042873844127401 : Rat) / 1063897249402792496577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix33,
    observedConstantTrainBaseRateLoss33,
    observedConstantTrainBaseRatePredictor33]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix35 :
    (∑ i ∈ Finset.range 35,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1739237779129806954699669585604833844127401 : Rat) / 1063897249402792496577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix34,
    observedConstantTrainBaseRateLoss34,
    observedConstantTrainBaseRatePredictor34]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix36 :
    (∑ i ∈ Finset.range 36,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1765902579100586211384642200352283444127401 : Rat) / 1063897249402792496577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix35,
    observedConstantTrainBaseRateLoss35,
    observedConstantTrainBaseRatePredictor35]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix37 :
    (∑ i ∈ Finset.range 37,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1791106575986546542741965852409093444127401 : Rat) / 1063897249402792496577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix36,
    observedConstantTrainBaseRateLoss36,
    observedConstantTrainBaseRatePredictor36]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix38 :
    (∑ i ∈ Finset.range 38,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2563354386900622711196690168905447965010411969 : Rat) / 1456475334432422927814734400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix37,
    observedConstantTrainBaseRateLoss37,
    observedConstantTrainBaseRatePredictor37]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix39 :
    (∑ i ∈ Finset.range 39,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2668901522710477584144365637959935005010411969 : Rat) / 1456475334432422927814734400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix38,
    observedConstantTrainBaseRateLoss38,
    observedConstantTrainBaseRatePredictor38]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix40 :
    (∑ i ∈ Finset.range 40,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2708043653737924174724278980671011005010411969 : Rat) / 1456475334432422927814734400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix39,
    observedConstantTrainBaseRateLoss39,
    observedConstantTrainBaseRatePredictor39]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix41 :
    (∑ i ∈ Finset.range 41,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2745253142045890589894309102085727627510411969 : Rat) / 1456475334432422927814734400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix40,
    observedConstantTrainBaseRateLoss40,
    observedConstantTrainBaseRatePredictor40]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix42 :
    (∑ i ∈ Finset.range 42,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((4674305713071888345884381794869654737845002519889 : Rat) / 2448335037180902941656568526400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix41,
    observedConstantTrainBaseRateLoss41,
    observedConstantTrainBaseRatePredictor41]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix43 :
    (∑ i ∈ Finset.range 43,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((4731039635834420358492835884754587746845002519889 : Rat) / 2448335037180902941656568526400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix42,
    observedConstantTrainBaseRateLoss42,
    observedConstantTrainBaseRatePredictor42]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix44 :
    (∑ i ∈ Finset.range 44,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((8847770926410949713094566565468254571792409659274761 : Rat) / 4526971483747489539122995205313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix43,
    observedConstantTrainBaseRateLoss43,
    observedConstantTrainBaseRatePredictor43]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix45 :
    (∑ i ∈ Finset.range 45,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((8943352230596638692162845369143839984882659659274761 : Rat) / 4526971483747489539122995205313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix44,
    observedConstantTrainBaseRateLoss44,
    observedConstantTrainBaseRatePredictor44]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix46 :
    (∑ i ∈ Finset.range 46,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((9034732677462561587706641795768992261298819659274761 : Rat) / 4526971483747489539122995205313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix45,
    observedConstantTrainBaseRateLoss45,
    observedConstantTrainBaseRatePredictor45]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix47 :
    (∑ i ∈ Finset.range 47,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((9122183246887653205606541495162155474787819659274761 : Rat) / 4526971483747489539122995205313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix46,
    observedConstantTrainBaseRateLoss46,
    observedConstantTrainBaseRatePredictor46]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix48 :
    (∑ i ∈ Finset.range 48,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((20335948197278319794661037926729134803549017627337947049 : Rat) / 10000080007598204391922696408537742400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix47,
    observedConstantTrainBaseRateLoss47,
    observedConstantTrainBaseRatePredictor47]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix49 :
    (∑ i ∈ Finset.range 49,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((20513363691823379666370629406976659452712072017962947049 : Rat) / 10000080007598204391922696408537742400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix48,
    observedConstantTrainBaseRateLoss48,
    observedConstantTrainBaseRatePredictor48]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix50 :
    (∑ i ∈ Finset.range 50,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1013496969867341888232138366870229717094558412880184405401 : Rat) / 490003920372312015204212124018349377600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix49,
    observedConstantTrainBaseRateLoss49,
    observedConstantTrainBaseRatePredictor49]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix51 :
    (∑ i ∈ Finset.range 51,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1021508769736205519942748782771839534211323288273784405401 : Rat) / 490003920372312015204212124018349377600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix50,
    observedConstantTrainBaseRateLoss50,
    observedConstantTrainBaseRatePredictor50]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix52 :
    (∑ i ∈ Finset.range 52,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1029209461651683828007541570066735552201293372273784405401 : Rat) / 490003920372312015204212124018349377600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix51,
    observedConstantTrainBaseRateLoss51,
    observedConstantTrainBaseRatePredictor51]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix53 :
    (∑ i ∈ Finset.range 53,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1036616820997896505254777531514229835778183974523784405401 : Rat) / 490003920372312015204212124018349377600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix52,
    observedConstantTrainBaseRateLoss52,
    observedConstantTrainBaseRatePredictor52]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix54 :
    (∑ i ∈ Finset.range 54,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2931886149855250362537196125777496151492830972921310394771409 : Rat) / 1376421012325824450708631856367543401678400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix53,
    observedConstantTrainBaseRateLoss53,
    observedConstantTrainBaseRatePredictor53]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix55 :
    (∑ i ∈ Finset.range 55,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2951180685033266430331353068736705664765286849962310394771409 : Rat) / 1376421012325824450708631856367543401678400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix54,
    observedConstantTrainBaseRateLoss54,
    observedConstantTrainBaseRatePredictor54]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix56 :
    (∑ i ∈ Finset.range 56,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2969779979109000266261191629288459364171065804491750394771409 : Rat) / 1376421012325824450708631856367543401678400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix55,
    observedConstantTrainBaseRateLoss55,
    observedConstantTrainBaseRatePredictor55]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix57 :
    (∑ i ∈ Finset.range 57,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2987720943579374900727952358137010046793030516689312894771409 : Rat) / 1376421012325824450708631856367543401678400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix56,
    observedConstantTrainBaseRateLoss56,
    observedConstantTrainBaseRatePredictor56]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix58 :
    (∑ i ∈ Finset.range 58,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((3005037922520308989274508727995137144577727758133312894771409 : Rat) / 1376421012325824450708631856367543401678400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix57,
    observedConstantTrainBaseRateLoss57,
    observedConstantTrainBaseRatePredictor57]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix59 :
    (∑ i ∈ Finset.range 59,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((3021762911990907935079431928253476901029119356662312894771409 : Rat) / 1376421012325824450708631856367543401678400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix58,
    observedConstantTrainBaseRateLoss58,
    observedConstantTrainBaseRatePredictor58]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix60 :
    (∑ i ∈ Finset.range 60,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((10575019561219445375699264187919408033184845817993067186699274729 : Rat) / 4791321543906194912916747492015418581242510400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix59,
    observedConstantTrainBaseRateLoss59,
    observedConstantTrainBaseRatePredictor59]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix61 :
    (∑ i ∈ Finset.range 61,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((10629422625552731260612347045856624768902995133456641196699274729 : Rat) / 4791321543906194912916747492015418581242510400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix60,
    observedConstantTrainBaseRateLoss60,
    observedConstantTrainBaseRatePredictor60]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix62 :
    (∑ i ∈ Finset.range 62,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((39747932621281542206425641646206481013673382427261028328918001266609 : Rat) / 17828507464874951270963217417789372540803381198400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix61,
    observedConstantTrainBaseRateLoss61,
    observedConstantTrainBaseRatePredictor61]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix63 :
    (∑ i ∈ Finset.range 63,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((39937516827468577690281441004110690302171311920035183377918001266609 : Rat) / 17828507464874951270963217417789372540803381198400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix62,
    observedConstantTrainBaseRateLoss62,
    observedConstantTrainBaseRatePredictor62]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix64 :
    (∑ i ∈ Finset.range 64,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((40121130253667359348115074849357296627438643986103173301918001266609 : Rat) / 17828507464874951270963217417789372540803381198400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix63,
    observedConstantTrainBaseRateLoss63,
    observedConstantTrainBaseRatePredictor63]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix65 :
    (∑ i ∈ Finset.range 65,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((40299050587794059641069589676452946164788751644849230921145540329109 : Rat) / 17828507464874951270963217417789372540803381198400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix64,
    observedConstantTrainBaseRateLoss64,
    observedConstantTrainBaseRatePredictor64]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix66 :
    (∑ i ∈ Finset.range 66,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((40471538561423163641055789139597036225140477318274994710105540329109 : Rat) / 17828507464874951270963217417789372540803381198400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix65,
    observedConstantTrainBaseRateLoss65,
    observedConstantTrainBaseRatePredictor65]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix67 :
    (∑ i ∈ Finset.range 67,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((40638839224550565936726517498592394467791083601613803711105540329109 : Rat) / 17828507464874951270963217417789372540803381198400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix66,
    observedConstantTrainBaseRateLoss66,
    observedConstantTrainBaseRatePredictor66]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix68 :
    (∑ i ∈ Finset.range 68,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((183156510967590454889907029782965039270900215257868216867508770537370301 : Rat) / 80032170009823656255353882988456493335666378199617600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix67,
    observedConstantTrainBaseRateLoss67,
    observedConstantTrainBaseRatePredictor67]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix69 :
    (∑ i ∈ Finset.range 69,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((183863996093033561981459421364491291582077191450630948629081020537370301 : Rat) / 80032170009823656255353882988456493335666378199617600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix68,
    observedConstantTrainBaseRateLoss68,
    observedConstantTrainBaseRatePredictor68]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix70 :
    (∑ i ∈ Finset.range 70,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((184551123003356798106504214196454616658086924262085448033725020537370301 : Rat) / 80032170009823656255353882988456493335666378199617600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix69,
    observedConstantTrainBaseRateLoss69,
    observedConstantTrainBaseRatePredictor69]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix71 :
    (∑ i ∈ Finset.range 71,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((185218757946223926104736511884817349451328217714194605516482180537370301 : Rat) / 80032170009823656255353882988456493335666378199617600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix70,
    observedConstantTrainBaseRateLoss70,
    observedConstantTrainBaseRatePredictor70]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix72 :
    (∑ i ∈ Finset.range 72,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((936959170026963738685315015084341649271027883412589878074096756088883687341 : Rat) / 403442169019521051183238924144809182905094212504272321600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix71,
    observedConstantTrainBaseRateLoss71,
    observedConstantTrainBaseRatePredictor71]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix73 :
    (∑ i ∈ Finset.range 73,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((940140339772385544621182330279264300978700311157806523148525061151383687341 : Rat) / 403442169019521051183238924144809182905094212504272321600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix72,
    observedConstantTrainBaseRateLoss72,
    observedConstantTrainBaseRatePredictor72]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix74 :
    (∑ i ∈ Finset.range 74,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5026499054607309209257816800028678486368067823591154049924326384319723669840189 : Rat) / 2149943318705027681755480226767688135701247058435267201806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix73,
    observedConstantTrainBaseRateLoss73,
    observedConstantTrainBaseRatePredictor73]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix75 :
    (∑ i ∈ Finset.range 75,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5042547542431315954156705807906816311781830812795478603668453816920723669840189 : Rat) / 2149943318705027681755480226767688135701247058435267201806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix74,
    observedConstantTrainBaseRateLoss74,
    observedConstantTrainBaseRatePredictor74]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix76 :
    (∑ i ∈ Finset.range 76,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5058170923644517898168495355842937686353522569041324160344514585084826069840189 : Rat) / 2149943318705027681755480226767688135701247058435267201806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix75,
    observedConstantTrainBaseRateLoss75,
    observedConstantTrainBaseRatePredictor75]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix77 :
    (∑ i ∈ Finset.range 77,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5073385868125865012965295253201089128868371275565368699178109083167076069840189 : Rat) / 2149943318705027681755480226767688135701247058435267201806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix76,
    observedConstantTrainBaseRateLoss76,
    observedConstantTrainBaseRatePredictor76]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix78 :
    (∑ i ∈ Finset.range 78,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5088208185434730072008357524602789707712319011926117772597377395011076069840189 : Rat) / 2149943318705027681755480226767688135701247058435267201806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix77,
    observedConstantTrainBaseRateLoss77,
    observedConstantTrainBaseRatePredictor77]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix79 :
    (∑ i ∈ Finset.range 79,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5102652879603740745096180701318878256687625739224421726624800442500076069840189 : Rat) / 2149943318705027681755480226767688135701247058435267201806400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix78,
    observedConstantTrainBaseRateLoss78,
    observedConstantTrainBaseRatePredictor78]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix80 :
    (∑ i ∈ Finset.range 80,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((31933538140931206925211579964071801931953238367382497252168221382566050751872619549 : Rat) / 13417796252038077761835952095257141654911482891694502606473742400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix79,
    observedConstantTrainBaseRateLoss79,
    observedConstantTrainBaseRatePredictor79]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix81 :
    (∑ i ∈ Finset.range 81,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((33542760137378401574197007513399669244514358911662227539998777822503117182497619549 : Rat) / 13417796252038077761835952095257141654911482891694502606473742400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix80,
    observedConstantTrainBaseRateLoss80,
    observedConstantTrainBaseRatePredictor80]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix82 :
    (∑ i ∈ Finset.range 82,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((316012441753911849769291224432254568880178162280941219111176327172894618642478575941 : Rat) / 120760166268342699856523568857314274894203346025250523458263681600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix81,
    observedConstantTrainBaseRateLoss81,
    observedConstantTrainBaseRatePredictor81]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix83 :
    (∑ i ∈ Finset.range 83,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7730618951158611433015957543819021531548478865950827589216364380265763772743379901 : Rat) / 2945369908983968289183501679446689631565935268908549352640577600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix82,
    observedConstantTrainBaseRateLoss82,
    observedConstantTrainBaseRatePredictor82]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix84 :
    (∑ i ∈ Finset.range 84,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((55587091570648177217151437742608599381514541115847170994865458082854042560669144137989 : Rat) / 20290653302990557544185143069708244871857728067510996490340939086400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix83,
    observedConstantTrainBaseRateLoss83,
    observedConstantTrainBaseRatePredictor83]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix85 :
    (∑ i ∈ Finset.range 85,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((55756357868900692286583624276719494466996012871888038078679568614996507739909144137989 : Rat) / 20290653302990557544185143069708244871857728067510996490340939086400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix84,
    observedConstantTrainBaseRateLoss84,
    observedConstantTrainBaseRatePredictor84]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix86 :
    (∑ i ∈ Finset.range 86,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((58046676006842804839440106074770496013945033029089432288465685755209581683211544137989 : Rat) / 20290653302990557544185143069708244871857728067510996490340939086400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix85,
    observedConstantTrainBaseRateLoss85,
    observedConstantTrainBaseRatePredictor85]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix87 :
    (∑ i ∈ Finset.range 87,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((60284040602114811761342226273650767265527871135603774252460371577010482067251544137989 : Rat) / 20290653302990557544185143069708244871857728067510996490340939086400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix86,
    observedConstantTrainBaseRateLoss86,
    observedConstantTrainBaseRatePredictor86]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix88 :
    (∑ i ∈ Finset.range 88,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((62470267124328018683576085566941622884064886677390017239077453931091530982611544137989 : Rat) / 20290653302990557544185143069708244871857728067510996490340939086400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix87,
    observedConstantTrainBaseRateLoss87,
    observedConstantTrainBaseRatePredictor87]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix89 :
    (∑ i ∈ Finset.range 89,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((64607088992436459178719174537876344756056967079737650654070312445817700822534044137989 : Rat) / 20290653302990557544185143069708244871857728067510996490340939086400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix88,
    observedConstantTrainBaseRateLoss88,
    observedConstantTrainBaseRatePredictor88]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix90 :
    (∑ i ∈ Finset.range 90,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((528300300455720956349022662505437012989433906874382003996595641221361467455652003617010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix89,
    observedConstantTrainBaseRateLoss89,
    observedConstantTrainBaseRatePredictor89]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix91 :
    (∑ i ∈ Finset.range 91,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((544482168608544437369115006891741374595075084418334344681231060936622030004156978017010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix90,
    observedConstantTrainBaseRateLoss90,
    observedConstantTrainBaseRatePredictor90]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix92 :
    (∑ i ∈ Finset.range 92,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((560310345403360304566645255597098859078313043373293161194399385981134837230686418017010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix91,
    observedConstantTrainBaseRateLoss91,
    observedConstantTrainBaseRatePredictor91]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix93 :
    (∑ i ∈ Finset.range 93,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((575796301456983909985211889520665178667832601278067967378892167135861982391708428017010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix92,
    observedConstantTrainBaseRateLoss92,
    observedConstantTrainBaseRatePredictor92]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix94 :
    (∑ i ∈ Finset.range 94,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((590951016688556368796952898831460106290181258707367766147021072176168440553679788017010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix93,
    observedConstantTrainBaseRateLoss93,
    observedConstantTrainBaseRatePredictor93]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix95 :
    (∑ i ∈ Finset.range 95,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((593360011656881621912423815676698737113748434011682497577654227198859138730145428017010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix94,
    observedConstantTrainBaseRateLoss94,
    observedConstantTrainBaseRatePredictor94]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix96 :
    (∑ i ∈ Finset.range 96,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((608320118203400981640486607606553693891993733421991317695988644273363950774032941617010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix95,
    observedConstantTrainBaseRateLoss95,
    observedConstantTrainBaseRatePredictor95]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix97 :
    (∑ i ∈ Finset.range 97,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((622970179138984447520018584295674894513051006336274857362651851098169281578729644117010869 : Rat) / 160722264812988206307490518255159007629985064022754603199990578503374400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix96,
    observedConstantTrainBaseRateLoss96,
    observedConstantTrainBaseRatePredictor96]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix98 :
    (∑ i ∈ Finset.range 98,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((5996541377101041888261621556804946067396960745796047234493159381080080699070352031736955266421 : Rat) / 1512235789625406033147178286262791102790529467390098061508711353138249729600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix97,
    observedConstantTrainBaseRateLoss97,
    observedConstantTrainBaseRatePredictor97]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix99 :
    (∑ i ∈ Finset.range 99,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((6022286673632966253725957958418698702779566916751666936901156886512060884859958595736955266421 : Rat) / 1512235789625406033147178286262791102790529467390098061508711353138249729600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix98,
    observedConstantTrainBaseRateLoss98,
    observedConstantTrainBaseRatePredictor98]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix100 :
    (∑ i ∈ Finset.range 100,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((6047514489967279242800489822626277552918792471884589253187903957440408778373210451736955266421 : Rat) / 1512235789625406033147178286262791102790529467390098061508711353138249729600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix99,
    observedConstantTrainBaseRateLoss99,
    observedConstantTrainBaseRatePredictor99]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix101 :
    (∑ i ∈ Finset.range 101,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((6072240272756539403392438502736125583940247438470366415380544761657282548805548595802555266421 : Rat) / 1512235789625406033147178286262791102790529467390098061508711353138249729600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix100,
    observedConstantTrainBaseRateLoss100,
    observedConstantTrainBaseRatePredictor100]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix102 :
    (∑ i ∈ Finset.range 102,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((62190180850282060059925751967509697391989013785693979425223345155834676984688782666437866272760621 : Rat) / 15426317289968766944134365698166732039566191096846390325450364513363285491649600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix101,
    observedConstantTrainBaseRateLoss101,
    observedConstantTrainBaseRatePredictor101]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix103 :
    (∑ i ∈ Finset.range 103,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((62432614251121393872111900069970827500072310704322884492050650849621998526576788633001866272760621 : Rat) / 15426317289968766944134365698166732039566191096846390325450364513363285491649600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix102,
    observedConstantTrainBaseRateLoss102,
    observedConstantTrainBaseRatePredictor102]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix104 :
    (∑ i ∈ Finset.range 104,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((664869881692479296571219832700326106592765765403576609891436643301803075690255964683648655287717428189 : Rat) / 163657800129278648510321485691850860207757721346443354962702917122271095780910606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix103,
    observedConstantTrainBaseRateLoss103,
    observedConstantTrainBaseRatePredictor103]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix105 :
    (∑ i ∈ Finset.range 105,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((667343886664617308689366608001600273143291456203250527818277721245633916930178861737428505537717428189 : Rat) / 163657800129278648510321485691850860207757721346443354962702917122271095780910606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix104,
    observedConstantTrainBaseRateLoss104,
    observedConstantTrainBaseRatePredictor104]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix106 :
    (∑ i ∈ Finset.range 106,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((669770992132068078673028786836845750278029403748762826802106573766311865125281451717807903297717428189 : Rat) / 163657800129278648510321485691850860207757721346443354962702917122271095780910606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix105,
    observedConstantTrainBaseRateLoss105,
    observedConstantTrainBaseRatePredictor105]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix107 :
    (∑ i ∈ Finset.range 107,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((672152519168259315685299659180970117082095430065002867412351598600814746831494165720449667297717428189 : Rat) / 163657800129278648510321485691850860207757721346443354962702917122271095780910606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix106,
    observedConstantTrainBaseRateLoss106,
    observedConstantTrainBaseRatePredictor106]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix108 :
    (∑ i ∈ Finset.range 108,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7722233029736045644350871319621508255883396450503490925300726551421202415324782757867111101195566835335861 : Rat) / 1873718153680111246794670689686000498518618151695429970967985698132881775595645532673600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix107,
    observedConstantTrainBaseRateLoss107,
    observedConstantTrainBaseRatePredictor107]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix109 :
    (∑ i ∈ Finset.range 109,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7899788471436943831512256159204078933470592314358128846547916324344837897579972901221661260413206835335861 : Rat) / 1873718153680111246794670689686000498518618151695429970967985698132881775595645532673600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix108,
    observedConstantTrainBaseRateLoss108,
    observedConstantTrainBaseRatePredictor108]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix110 :
    (∑ i ∈ Finset.range 110,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((95928393501141606117247508196394766191941159842889425539263015360922303326172195871502030492083863370625364541 : Rat) / 22261645383873401723167482464159371922899702260293403485070638079516768375851864573695041600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix109,
    observedConstantTrainBaseRateLoss109,
    observedConstantTrainBaseRatePredictor109]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix111 :
    (∑ i ∈ Finset.range 111,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((97961916663953457651334592203600981991850478968330904998124901210238091619788438349438498871553119876225364541 : Rat) / 22261645383873401723167482464159371922899702260293403485070638079516768375851864573695041600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix110,
    observedConstantTrainBaseRateLoss110,
    observedConstantTrainBaseRatePredictor110]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix112 :
    (∑ i ∈ Finset.range 112,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((98319376466152045792216986635649048835999189585019743613934019989018060494870565968655362867451417636225364541 : Rat) / 22261645383873401723167482464159371922899702260293403485070638079516768375851864573695041600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix111,
    observedConstantTrainBaseRateLoss111,
    observedConstantTrainBaseRatePredictor111]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix113 :
    (∑ i ∈ Finset.range 113,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((100331540702808457191655376974327319639241626752000666452109848279032423616623527805816932050447171611850364541 : Rat) / 22261645383873401723167482464159371922899702260293403485070638079516768375851864573695041600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix112,
    observedConstantTrainBaseRateLoss112,
    observedConstantTrainBaseRatePredictor112]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix114 :
    (∑ i ∈ Finset.range 114,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1306374031418779214474802676993565773429349463818905206009068242744905188159934979837831129183658672181957304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix113,
    observedConstantTrainBaseRateLoss113,
    observedConstantTrainBaseRatePredictor113]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix115 :
    (∑ i ∈ Finset.range 115,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1311241784737309819212397935842184592788179597799680437569764148583554220461430272824809025233815761982957304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix114,
    observedConstantTrainBaseRateLoss114,
    observedConstantTrainBaseRatePredictor114]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix116 :
    (∑ i ∈ Finset.range 116,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1316025249548472294763988709679360409528244355547442623532925130986509443432336346749857398547074101419917304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix115,
    observedConstantTrainBaseRateLoss115,
    observedConstantTrainBaseRatePredictor115]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix117 :
    (∑ i ∈ Finset.range 117,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1320726596317766567888972953436543092077839808967043909900553251696905015949446396367779867116325107592167304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix116,
    observedConstantTrainBaseRateLoss116,
    observedConstantTrainBaseRatePredictor116]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix118 :
    (∑ i ∈ Finset.range 118,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1346092956615168594672143376546621095183481584576775400583851418649637980875285885138148692497894191578727304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix117,
    observedConstantTrainBaseRateLoss117,
    observedConstantTrainBaseRatePredictor117]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix119 :
    (∑ i ∈ Finset.range 119,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1371031200374945694976281549625754805648371721485825556858174070719155472750452271361761077634945268186887304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix118,
    observedConstantTrainBaseRateLoss118,
    observedConstantTrainBaseRatePredictor118]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix120 :
    (∑ i ∈ Finset.range 120,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1395552075038538403445656588249711996843423643406707865732100248772680051302095288223393649532996196136327304824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix119,
    observedConstantTrainBaseRateLoss119,
    observedConstantTrainBaseRatePredictor119]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix121 :
    (∑ i ∈ Finset.range 121,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1419665971296256205156407971718729898545724356345708864062910568732121826084721452235725514161350306601050904824029 : Rat) / 284258949906679466603125583584851020083506298161686469100866977637349615391252458741511986190400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix120,
    observedConstantTrainBaseRateLoss120,
    observedConstantTrainBaseRatePredictor120]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix122 :
    (∑ i ∈ Finset.range 122,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((172428733958495614129894313970166721962758699515649828831867364326834573474280940725542056331959460506727319483707509 : Rat) / 34395332938708215458978195613766973430104262077564062761204904294119303462341547507722950329038400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix121,
    observedConstantTrainBaseRateLoss121,
    observedConstantTrainBaseRatePredictor121]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix123 :
    (∑ i ∈ Finset.range 123,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((173067287177439940078072988254714297779688834772064018767315911159375457369502120013266264821815853328988159483707509 : Rat) / 34395332938708215458978195613766973430104262077564062761204904294119303462341547507722950329038400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix122,
    observedConstantTrainBaseRateLoss122,
    observedConstantTrainBaseRatePredictor122]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix124 :
    (∑ i ∈ Finset.range 124,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7121515484602320327517229342430294660076153155617954858888722468796015746448969122491036421821882373389680778832007869 : Rat) / 1410208650487036833818106020164445910634274745180126573209401076058891441956003447816640963490574400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix123,
    observedConstantTrainBaseRateLoss123,
    observedConstantTrainBaseRatePredictor123]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix125 :
    (∑ i ∈ Finset.range 125,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7146858439242113592600498522327501401545112147515406791964155807328604140813911456860051242691024190600121988832007869 : Rat) / 1410208650487036833818106020164445910634274745180126573209401076058891441956003447816640963490574400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix124,
    observedConstantTrainBaseRateLoss124,
    observedConstantTrainBaseRatePredictor124]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix126 :
    (∑ i ∈ Finset.range 126,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7171797528556767112211400724573866256382021808917980931034099040178337206526254070188561443374795363811497607709447869 : Rat) / 1410208650487036833818106020164445910634274745180126573209401076058891441956003447816640963490574400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix125,
    observedConstantTrainBaseRateLoss125,
    observedConstantTrainBaseRatePredictor125]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix127 :
    (∑ i ∈ Finset.range 127,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((7196342330178174346018426858996860137512452235940859548001084616726402156876175544946559168600540172417427567709447869 : Rat) / 1410208650487036833818106020164445910634274745180126573209401076058891441956003447816640963490574400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix126,
    observedConstantTrainBaseRateLoss126,
    observedConstantTrainBaseRatePredictor126]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix128 :
    (∑ i ∈ Finset.range 128,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((118053782962886953430559850116985306162058045617573930899849619473395591375233781592417894567857331348597513621025684679101 : Rat) / 22745255323705417092652231999232348092620217365010261499294429955753860067308379609834602100139474497600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix127,
    observedConstantTrainBaseRateLoss127,
    observedConstantTrainBaseRatePredictor127]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix129 :
    (∑ i ∈ Finset.range 129,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((120006881925966728857874693129580533364660993482403504089394912885107322879687351826243957945794642247152170630806309679101 : Rat) / 22745255323705417092652231999232348092620217365010261499294429955753860067308379609834602100139474497600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix128,
    observedConstantTrainBaseRateLoss128,
    observedConstantTrainBaseRatePredictor128]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix130 :
    (∑ i ∈ Finset.range 130,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((120424296047205617691284239839448364383169666511111995765632267197006679138921877922122738280638250472997037947446309679101 : Rat) / 22745255323705417092652231999232348092620217365010261499294429955753860067308379609834602100139474497600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix129,
    observedConstantTrainBaseRateLoss129,
    observedConstantTrainBaseRatePredictor129]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix131 :
    (∑ i ∈ Finset.range 131,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((120835313111793567340797155034650173612696461059676375054642078623297636979745650038188938490823604584611501676215909679101 : Rat) / 22745255323705417092652231999232348092620217365010261499294429955753860067308379609834602100139474497600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix130,
    observedConstantTrainBaseRateLoss130,
    observedConstantTrainBaseRatePredictor130]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix132 :
    (∑ i ∈ Finset.range 132,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2080600996703025758212188244348542205346486796115844282296978524358727935719336849066879156993156362762802417281747466003052261 : Rat) / 390331326610108662727004953338826325617455550200941097589391712470691992615079102484371606640493521853313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix131,
    observedConstantTrainBaseRateLoss131,
    observedConstantTrainBaseRatePredictor131]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix133 :
    (∑ i ∈ Finset.range 133,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2087442338472261024884962591601532586107257430246338714651201757754227663385645798245966843204023302975677028371917076003052261 : Rat) / 390331326610108662727004953338826325617455550200941097589391712470691992615079102484371606640493521853313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix132,
    observedConstantTrainBaseRateLoss132,
    observedConstantTrainBaseRatePredictor132]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix134 :
    (∑ i ∈ Finset.range 134,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2094181189678499663954803748622059715644012901391668297405455000938307444880233798160966212560015476997336094663686836003052261 : Rat) / 390331326610108662727004953338826325617455550200941097589391712470691992615079102484371606640493521853313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix133,
    observedConstantTrainBaseRateLoss133,
    observedConstantTrainBaseRatePredictor133]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix135 :
    (∑ i ∈ Finset.range 135,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2100819836314006195838654284740131914038737089913039147780816196008656478899935687807681730745476914192097022689701276003052261 : Rat) / 390331326610108662727004953338826325617455550200941097589391712470691992615079102484371606640493521853313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix134,
    observedConstantTrainBaseRateLoss134,
    observedConstantTrainBaseRatePredictor134]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix136 :
    (∑ i ∈ Finset.range 136,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2107360496889433097704575833521262470657429409753353824836508136677144119770046367121614451982137850612899613835660962403052261 : Rat) / 390331326610108662727004953338826325617455550200941097589391712470691992615079102484371606640493521853313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix135,
    observedConstantTrainBaseRateLoss135,
    observedConstantTrainBaseRatePredictor135]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix137 :
    (∑ i ∈ Finset.range 137,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((2113805324905607150824516373450766384713207282217115448395114625576537894362269936028211761916077381661187201618701364903052261 : Rat) / 390331326610108662727004953338826325617455550200941097589391712470691992615079102484371606640493521853313600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix136,
    observedConstantTrainBaseRateLoss136,
    observedConstantTrainBaseRatePredictor136]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix138 :
    (∑ i ∈ Finset.range 138,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((39793215682140495900331768039833538669057855009022774840267892026129226994143211559809930403941001942667949810816521202505387886709 : Rat) / 7326128669145129490723155969216431305514023221721463460655293051362418009392419674529170685035422911664842958400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix137,
    observedConstantTrainBaseRateLoss137,
    observedConstantTrainBaseRatePredictor137]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix139 :
    (∑ i ∈ Finset.range 139,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((39910697892981176302161163189584438867442485541131850455418185560946741255140136117270935399642349040615085331736888708145387886709 : Rat) / 7326128669145129490723155969216431305514023221721463460655293051362418009392419674529170685035422911664842958400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix138,
    observedConstantTrainBaseRateLoss138,
    observedConstantTrainBaseRatePredictor138]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix140 :
    (∑ i ∈ Finset.range 140,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((773351925213539224906494835217817086735893166993693718664056953300116729376988001194079121994626279947029312554895905507485199359104589 : Rat) / 141548132016553046890262096481230669253836442666880395523320917045373278359470940531578106805569406076276430799246400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix139,
    observedConstantTrainBaseRateLoss139,
    observedConstantTrainBaseRatePredictor139]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix141 :
    (∑ i ∈ Finset.range 141,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((775557408711723493142060852707648339093395770021917608717338159140880396325525029643664043031765791697518634658565951296174130959104589 : Rat) / 141548132016553046890262096481230669253836442666880395523320917045373278359470940531578106805569406076276430799246400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix140,
    observedConstantTrainBaseRateLoss140,
    observedConstantTrainBaseRatePredictor140]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix142 :
    (∑ i ∈ Finset.range 142,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16547483397665242688223018187450917186753579888805340953089725972043029463113064084448799390246937506940721429611381951523844488491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix141,
    observedConstantTrainBaseRateLoss141,
    observedConstantTrainBaseRatePredictor141]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix143 :
    (∑ i ∈ Finset.range 143,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16593096051103233775580193543996068801182339611581964390946440945936853164286131904507155394763027304968796230322078598020764488491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix142,
    observedConstantTrainBaseRateLoss142,
    observedConstantTrainBaseRatePredictor142]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix144 :
    (∑ i ∈ Finset.range 144,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16638072995888976466443809558929632161412253595154160341894790534356583278739344263236515777914400706476845537453502490629884488491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix143,
    observedConstantTrainBaseRateLoss143,
    observedConstantTrainBaseRatePredictor143]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix145 :
    (∑ i ∈ Finset.range 145,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16682427429913072352124272709458974230921392824034746520566800600598629049883911176993107718262704848425056392079779843058698863491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix144,
    observedConstantTrainBaseRateLoss144,
    observedConstantTrainBaseRatePredictor144]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix146 :
    (∑ i ∈ Finset.range 146,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16726172188244756170695977056159399303613022362682443785772165677107312099132602712006505600548670826424490412604416569810846063491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix145,
    observedConstantTrainBaseRateLoss145,
    observedConstantTrainBaseRatePredictor145]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix147 :
    (∑ i ∈ Finset.range 147,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16769319755514584106775451811712806938879559754785457249880947847007624592586052680277132851208383468920179110368091141961526063491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix146,
    observedConstantTrainBaseRateLoss146,
    observedConstantTrainBaseRatePredictor146]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix148 :
    (∑ i ∈ Finset.range 148,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16811882277793433303196854185232008991419774991495524120210107027608071679931776199350513871850821096179103645586309809181846063491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix147,
    observedConstantTrainBaseRateLoss147,
    observedConstantTrainBaseRatePredictor147]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix149 :
    (∑ i ∈ Finset.range 149,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((16853871573991554755236211557829545384468602194292631269632258266358759276281928661168295577249946127563238976189418245082316063491587 : Rat) / 3011662383330915891282172265558099345826307290784689266453636532880282518286615755991023549054668214388860229771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix148,
    observedConstantTrainBaseRateLoss148,
    observedConstantTrainBaseRatePredictor148]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix150 :
    (∑ i ∈ Finset.range 150,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((375092536358110159406469216684750174233928948365558541818048566505025875803188837730254020585588488665469568791911761639036393805576722987 : Rat) / 66861916572329663702355506467655363576689848162710886404537184666475152188481156398756713812562689027647085961150411200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix149,
    observedConstantTrainBaseRateLoss149,
    observedConstantTrainBaseRatePredictor149]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix151 :
    (∑ i ∈ Finset.range 151,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((376000047665161226268234609237107786733543832224338808700534394019983384768219214226463006596115649220839047207478799233808768482504722987 : Rat) / 66861916572329663702355506467655363576689848162710886404537184666475152188481156398756713812562689027647085961150411200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix150,
    observedConstantTrainBaseRateLoss150,
    observedConstantTrainBaseRatePredictor150]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix152 :
    (∑ i ∈ Finset.range 152,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((8593596091221990124531738657643340926552867805369705182036815837136185107813349774742285198634894030380164379727982447212452160400470188826587 : Rat) / 1524518559765688662077407902969009944912105227957970920909852347580299945049558847048051831640241872519381207000190525771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix151,
    observedConstantTrainBaseRateLoss151,
    observedConstantTrainBaseRatePredictor151]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix153 :
    (∑ i ∈ Finset.range 153,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((8613747308306547168727117643996002078673006169048769390257041142117672670270599442593149747006849978528408763403979700695143927527127688826587 : Rat) / 1524518559765688662077407902969009944912105227957970920909852347580299945049558847048051831640241872519381207000190525771200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix152,
    observedConstantTrainBaseRateLoss152,
    observedConstantTrainBaseRatePredictor152]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix154 :
    (∑ i ∈ Finset.range 154,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((507860939507101513550150728927773621302616334506094292851786923435995929623289078553722215822644938908334800800531724495196002510791040519211 : Rat) / 89677562339158156592788700174647643818359131056351230641756020445899996767621108649885401861190698383493012176481795633600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix153,
    observedConstantTrainBaseRateLoss153,
    observedConstantTrainBaseRatePredictor153]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix155 :
    (∑ i ∈ Finset.range 155,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((509015716424947013607421660690623926528633212549314306807915041078819063776981042097882957455460884028573900342291173426332367604831040519211 : Rat) / 89677562339158156592788700174647643818359131056351230641756020445899996767621108649885401861190698383493012176481795633600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix154,
    observedConstantTrainBaseRateLoss154,
    observedConstantTrainBaseRatePredictor154]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix156 :
    (∑ i ∈ Finset.range 156,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((510155641061102013788825923653693971845603713264111636713577244534269363447697321282620362182364649043000143203159730797854949688920640519211 : Rat) / 89677562339158156592788700174647643818359131056351230641756020445899996767621108649885401861190698383493012176481795633600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix155,
    observedConstantTrainBaseRateLoss155,
    observedConstantTrainBaseRatePredictor155]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix157 :
    (∑ i ∈ Finset.range 157,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((511280998119929425005058559160258643062739490699721673325326687253582046287480301534646831140445802661983973114910515267399247624910640519211 : Rat) / 89677562339158156592788700174647643818359131056351230641756020445899996767621108649885401861190698383493012176481795633600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix156,
    observedConstantTrainBaseRateLoss156,
    observedConstantTrainBaseRatePredictor156]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix158 :
    (∑ i ∈ Finset.range 158,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((12629952012041764276307925842428973131593681985930445376779511952130737308529060559940825889344711544286833438041796381676954089276675018158031939 : Rat) / 2210462234097909401855648670604889772478734221408001484088644147970989020325092707111025270476489524454719257138099780572606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix157,
    observedConstantTrainBaseRateLoss157,
    observedConstantTrainBaseRatePredictor157]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix159 :
    (∑ i ∈ Finset.range 159,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((12656993131518488559367579508050890411160561936165180243823781314520009914638587907887101716373659548002994063669424823528504703045388258158031939 : Rat) / 2210462234097909401855648670604889772478734221408001484088644147970989020325092707111025270476489524454719257138099780572606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix158,
    observedConstantTrainBaseRateLoss158,
    observedConstantTrainBaseRatePredictor158]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix160 :
    (∑ i ∈ Finset.range 160,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((12683695180749806347520785239967568666257575150739758829358101173809033344839855291065410713088609825475017870408403361655244528294474818158031939 : Rat) / 2210462234097909401855648670604889772478734221408001484088644147970989020325092707111025270476489524454719257138099780572606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix159,
    observedConstantTrainBaseRateLoss159,
    observedConstantTrainBaseRatePredictor159]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix161 :
    (∑ i ∈ Finset.range 161,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((12710064497414530761673175634834191438410215427210849502049239469226447459641349068961146250039807402223855130493095409404545681502371588601781939 : Rat) / 2210462234097909401855648670604889772478734221408001484088644147970989020325092707111025270476489524454719257138099780572606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix160,
    observedConstantTrainBaseRateLoss160,
    observedConstantTrainBaseRatePredictor160]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix162 :
    (∑ i ∈ Finset.range 162,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((12736107262223640942696330378423772973347432011357291430250047322422149837594292270000104227970853965426286898486927299469825166172027748601781939 : Rat) / 2210462234097909401855648670604889772478734221408001484088644147970989020325092707111025270476489524454719257138099780572606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix161,
    observedConstantTrainBaseRateLoss161,
    observedConstantTrainBaseRatePredictor161]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix163 :
    (∑ i ∈ Finset.range 163,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((12761829503749968674837055653099338548987867580541101871527792344624779060994621515318303806767937411729069776789324663529500121290232188601781939 : Rat) / 2210462234097909401855648670604889772478734221408001484088644147970989020325092707111025270476489524454719257138099780572606400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix162,
    observedConstantTrainBaseRateLoss162,
    observedConstantTrainBaseRatePredictor162]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix164 :
    (∑ i ∈ Finset.range 164,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((339744102591749862724046925755781868875166244825056456845515055167021556210484339754622843587967987056999888757683683407697398244682336342320744337291 : Rat) / 58729771097747354897902729529301316364987489528589191430751186367441207281017388135232830411289850175237435942902173070033579441600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix163,
    observedConstantTrainBaseRateLoss163,
    observedConstantTrainBaseRatePredictor163]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix165 :
    (∑ i ∈ Finset.range 165,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((340410949825030113012793967184656396354831681594179986252040555103673811407306125058524613944904447179917063927882548860785971560166556967110744337291 : Rat) / 58729771097747354897902729529301316364987489528589191430751186367441207281017388135232830411289850175237435942902173070033579441600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix164,
    observedConstantTrainBaseRateLoss164,
    observedConstantTrainBaseRatePredictor164]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix166 :
    (∑ i ∈ Finset.range 166,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((341069738555472927035425387800671430003797029154964061437271403452478184438480367024869591558133575975729014097861196619326660922637212538253144337291 : Rat) / 58729771097747354897902729529301316364987489528589191430751186367441207281017388135232830411289850175237435942902173070033579441600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix165,
    observedConstantTrainBaseRateLoss165,
    observedConstantTrainBaseRatePredictor165]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix167 :
    (∑ i ∈ Finset.range 167,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((341720613979565887253386645830538220941998567380481061252843687031234137979404983715744247368852222784626544340917833476137165636429620649893144337291 : Rat) / 58729771097747354897902729529301316364987489528589191430751186367441207281017388135232830411289850175237435942902173070033579441600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix166,
    observedConstantTrainBaseRateLoss166,
    observedConstantTrainBaseRatePredictor166]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix168 :
    (∑ i ∈ Finset.range 168,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((9548181726462418641375840591838889734944479633016582764198467433910287929881344328382133330390082672706430038501526143042259680327649288229221742422708699 : Rat) / 1637914586145075980747609223842684412103136095462823959812219836601567829860293937703508407340462631537196851011598704750166497046782400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix167,
    observedConstantTrainBaseRateLoss167,
    observedConstantTrainBaseRatePredictor167]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix169 :
    (∑ i ∈ Finset.range 169,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((9565904366986188383671259042387081986903626188763135345621851351971324475603893997850618699963560095628578769952057675152359294176686578567665919922708699 : Rat) / 1637914586145075980747609223842684412103136095462823959812219836601567829860293937703508407340462631537196851011598704750166497046782400000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix168,
    observedConstantTrainBaseRateLoss168,
    observedConstantTrainBaseRatePredictor168]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix170 :
    (∑ i ∈ Finset.range 170,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((1619597623855830790725329703301122051758872307494997684404729492112471561030745907359112732310657199265103929260713143327230682261867300905226951506937770131 : Rat) / 276807565058517840746345958829413665645430000133217249208265152385664963246389675471892920840538184729786267820960181102778138000906225600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix169,
    observedConstantTrainBaseRateLoss169,
    observedConstantTrainBaseRatePredictor169]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix171 :
    (∑ i ∈ Finset.range 171,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((27582885748630385941098990526035544351760150964948506699479116849363159792719137999347429243970742226677207185433127278695010600637340358650369934861142092227 : Rat) / 4705728605994803292687881300100032315972310002264693236540507590556304375188624483022179654289149140406366552956323078747228346015405835200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix170,
    observedConstantTrainBaseRateLoss170,
    observedConstantTrainBaseRatePredictor170]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix172 :
    (∑ i ∈ Finset.range 172,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((27632031999957238176467354910652553610565745787790389031372789345917246180844633840652740955831778728576106922556652843402694064375370228704666636141142092227 : Rat) / 4705728605994803292687881300100032315972310002264693236540507590556304375188624483022179654289149140406366552956323078747228346015405835200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix171,
    observedConstantTrainBaseRateLoss171,
    observedConstantTrainBaseRatePredictor171]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix173 :
    (∑ i ∈ Finset.range 173,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((27680608444489704584471895979155324288524588345075390426278916897017098806425272831174936053402376631227057680169856299244276411697021507445123972611142092227 : Rat) / 4705728605994803292687881300100032315972310002264693236540507590556304375188624483022179654289149140406366552956323078747228346015405835200000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix172,
    observedConstantTrainBaseRateLoss172,
    observedConstantTrainBaseRatePredictor172]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix174 :
    (∑ i ∈ Finset.range 174,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((829890015670180854723065717730725668367986802794480841335004581282562790252679614459843280908808298548020336523032640217699320888843888126582805218407351678261883 : Rat) / 140837751448818467746855599430693867184735266057780003876420851677759633645020342152370814873219944623222144563429793423825797167895081241700800000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix173,
    observedConstantTrainBaseRateLoss173,
    observedConstantTrainBaseRatePredictor173]
  norm_num [ratToReal]

theorem observedConstantTrainBaseRateQuadraticPrefix175 :
    (∑ i ∈ Finset.range 175,
      (observedTrajectoryScore
          (monitorBrierScore constantTrainBaseRate) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore constantTrainBaseRate)) i replayPath) ^ 2) =
      ratToReal ((831310630446851027266035972677438161048417632632251331321698207252031934175588555719311849444692613589894361815829940764166830846279722383954399857232271678261883 : Rat) / 140837751448818467746855599430693867184735266057780003876420851677759633645020342152370814873219944623222144563429793423825797167895081241700800000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedConstantTrainBaseRateQuadraticPrefix174,
    observedConstantTrainBaseRateLoss174,
    observedConstantTrainBaseRatePredictor174]
  norm_num [ratToReal]

end

end FormalSLT.Applications.GJPBrierMonitorReplayPathData
