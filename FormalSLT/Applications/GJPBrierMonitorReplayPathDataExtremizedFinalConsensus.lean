/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathDataBase
import Mathlib.Tactic

/-!
# Generated GJP path calculation: extremized-final-consensus

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

theorem observedExtremizedFinalConsensusLoss0 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 0 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss1 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 1 replayPath =
      ratToReal ((12074273689 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss2 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 2 replayPath =
      ratToReal ((50522002441 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss3 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 3 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss4 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 4 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss5 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 5 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss6 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 6 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss7 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 7 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss8 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 8 replayPath =
      ratToReal ((81 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss9 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 9 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss10 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 10 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss11 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 11 replayPath =
      ratToReal ((44608396849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss12 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 12 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss13 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 13 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss14 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 14 replayPath =
      ratToReal ((1504896849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss15 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 15 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss16 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 16 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss17 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 17 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss18 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 18 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss19 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 19 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss20 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 20 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss21 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 21 replayPath =
      ratToReal ((176827819081 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss22 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 22 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss23 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 23 replayPath =
      ratToReal ((50522002441 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss24 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 24 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss25 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 25 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss26 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 26 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss27 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 27 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss28 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 28 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss29 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 29 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss30 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 30 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss31 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 31 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss32 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 32 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss33 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 33 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss34 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 34 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss35 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 35 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss36 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 36 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss37 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 37 replayPath =
      ratToReal ((5430363481 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss38 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 38 replayPath =
      ratToReal ((13840816609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss39 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 39 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss40 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 40 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss41 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 41 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss42 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 42 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss43 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 43 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss44 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 44 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss45 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 45 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss46 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 46 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss47 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 47 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss48 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 48 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss49 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 49 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss50 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 50 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss51 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 51 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss52 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 52 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss53 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 53 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss54 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 54 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss55 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 55 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss56 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 56 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss57 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 57 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss58 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 58 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss59 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 59 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss60 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 60 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss61 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 61 replayPath =
      ratToReal ((912100401 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss62 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 62 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss63 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 63 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss64 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 64 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss65 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 65 replayPath =
      ratToReal ((11029041 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss66 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 66 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss67 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 67 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss68 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 68 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss69 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 69 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss70 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 70 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss71 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 71 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss72 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 72 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss73 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 73 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss74 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 74 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss75 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 75 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss76 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 76 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss77 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 77 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss78 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 78 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss79 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 79 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss80 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 80 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss81 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 81 replayPath =
      ratToReal ((1 : Rat) / 4) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss82 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 82 replayPath =
      ratToReal ((5917147929 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss83 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 83 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss84 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 84 replayPath =
      ratToReal ((1504896849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss85 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 85 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss86 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 86 replayPath =
      ratToReal ((101868649 : Rat) / 3906250000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss87 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 87 replayPath =
      ratToReal ((666517489 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss88 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 88 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss89 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 89 replayPath =
      ratToReal ((1504896849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss90 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 90 replayPath =
      ratToReal ((50522002441 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss91 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 91 replayPath =
      ratToReal ((600980002441 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss92 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 92 replayPath =
      ratToReal ((5917147929 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss93 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 93 replayPath =
      ratToReal ((29955647929 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss94 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 94 replayPath =
      ratToReal ((124821596601 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss95 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 95 replayPath =
      ratToReal ((1 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss96 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 96 replayPath =
      ratToReal ((2749009761 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss97 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 97 replayPath =
      ratToReal ((81 : Rat) / 100) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss98 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 98 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss99 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 99 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss100 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 100 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss101 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 101 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss102 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 102 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss103 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 103 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss104 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 104 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss105 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 105 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss106 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 106 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss107 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 107 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss108 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 108 replayPath =
      ratToReal ((666517489 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss109 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 109 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss110 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 110 replayPath =
      ratToReal ((21132409 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss111 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 111 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss112 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 112 replayPath =
      ratToReal ((5917147929 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss113 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 113 replayPath =
      ratToReal ((1 : Rat) / 4) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss114 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 114 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss115 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 115 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss116 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 116 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss117 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 117 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss118 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 118 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss119 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 119 replayPath =
      ratToReal ((940510100401 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss120 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 120 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss121 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 121 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss122 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 122 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss123 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 123 replayPath =
      ratToReal ((44608396849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss124 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 124 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss125 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 125 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss126 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 126 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss127 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 127 replayPath =
      ratToReal ((2749009761 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss128 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 128 replayPath =
      ratToReal ((145697180209 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss129 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 129 replayPath =
      ratToReal ((5917147929 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss130 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 130 replayPath =
      ratToReal ((2719935409 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss131 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 131 replayPath =
      ratToReal ((5917147929 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss132 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 132 replayPath =
      ratToReal ((74567771041 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss133 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 133 replayPath =
      ratToReal ((912100401 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss134 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 134 replayPath =
      ratToReal ((1301881 : Rat) / 3906250000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss135 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 135 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss136 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 136 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss137 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 137 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss138 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 138 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss139 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 139 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss140 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 140 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss141 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 141 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss142 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 142 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss143 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 143 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss144 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 144 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss145 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 145 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss146 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 146 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss147 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 147 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss148 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 148 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss149 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 149 replayPath =
      ratToReal ((912100401 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss150 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 150 replayPath =
      ratToReal ((54066609 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss151 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 151 replayPath =
      ratToReal ((14480993569 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss152 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 152 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss153 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 153 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss154 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 154 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss155 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 155 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss156 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 156 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss157 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 157 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss158 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 158 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss159 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 159 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss160 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 160 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss161 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 161 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss162 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 162 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss163 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 163 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss164 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 164 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss165 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 165 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss166 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 166 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss167 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 167 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss168 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 168 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss169 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 169 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss170 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 170 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss171 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 171 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss172 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 172 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss173 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 173 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLoss174 :
    observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) 174 replayPath =
      ratToReal ((1 : Rat) / 10000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    extremizedFinalConsensusPredictionsQ]

theorem observedExtremizedFinalConsensusLossPrefix0 :
    (∑ i ∈ Finset.range 0, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) = ratToReal 0 := by
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix1 :
    (∑ i ∈ Finset.range 1, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix0,
    observedExtremizedFinalConsensusLoss0]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix2 :
    (∑ i ∈ Finset.range 2, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((6111495857 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix1,
    observedExtremizedFinalConsensusLoss1]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix3 :
    (∑ i ∈ Finset.range 3, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((12548998831 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix2,
    observedExtremizedFinalConsensusLoss2]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix4 :
    (∑ i ∈ Finset.range 4, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((12568998831 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix3,
    observedExtremizedFinalConsensusLoss3]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix5 :
    (∑ i ∈ Finset.range 5, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((12588998831 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix4,
    observedExtremizedFinalConsensusLoss4]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix6 :
    (∑ i ∈ Finset.range 6, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((12608998831 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix5,
    observedExtremizedFinalConsensusLoss5]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix7 :
    (∑ i ∈ Finset.range 7, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((12628998831 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix6,
    observedExtremizedFinalConsensusLoss6]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix8 :
    (∑ i ∈ Finset.range 8, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3164685609 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix7,
    observedExtremizedFinalConsensusLoss7]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix9 :
    (∑ i ∈ Finset.range 9, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((43664685609 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix8,
    observedExtremizedFinalConsensusLoss8]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix10 :
    (∑ i ∈ Finset.range 10, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((174688486041 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix9,
    observedExtremizedFinalConsensusLoss9]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix11 :
    (∑ i ∈ Finset.range 11, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((876902693181 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix10,
    observedExtremizedFinalConsensusLoss10]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix12 :
    (∑ i ∈ Finset.range 12, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((318127408553 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix11,
    observedExtremizedFinalConsensusLoss11]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix13 :
    (∑ i ∈ Finset.range 13, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((318147408553 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix12,
    observedExtremizedFinalConsensusLoss12]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix14 :
    (∑ i ∈ Finset.range 14, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((318167408553 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix13,
    observedExtremizedFinalConsensusLoss13]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix15 :
    (∑ i ∈ Finset.range 15, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1614915392349 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix14,
    observedExtremizedFinalConsensusLoss14]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix16 :
    (∑ i ∈ Finset.range 16, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((807532055187 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix15,
    observedExtremizedFinalConsensusLoss15]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix17 :
    (∑ i ∈ Finset.range 17, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((807582055187 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix16,
    observedExtremizedFinalConsensusLoss16]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix18 :
    (∑ i ∈ Finset.range 18, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1615312828399 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix17,
    observedExtremizedFinalConsensusLoss17]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix19 :
    (∑ i ∈ Finset.range 19, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((201932693303 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix18,
    observedExtremizedFinalConsensusLoss18]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix20 :
    (∑ i ∈ Finset.range 20, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((201945193303 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix19,
    observedExtremizedFinalConsensusLoss19]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix21 :
    (∑ i ∈ Finset.range 21, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((201957693303 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix20,
    observedExtremizedFinalConsensusLoss20]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix22 :
    (∑ i ∈ Finset.range 22, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((358497873101 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix21,
    observedExtremizedFinalConsensusLoss21]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix23 :
    (∑ i ∈ Finset.range 23, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((358517873101 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix22,
    observedExtremizedFinalConsensusLoss22]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix24 :
    (∑ i ∈ Finset.range 24, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((921555683973 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix23,
    observedExtremizedFinalConsensusLoss23]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix25 :
    (∑ i ∈ Finset.range 25, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((921605683973 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix24,
    observedExtremizedFinalConsensusLoss24]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix26 :
    (∑ i ∈ Finset.range 26, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((921655683973 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix25,
    observedExtremizedFinalConsensusLoss25]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix27 :
    (∑ i ∈ Finset.range 27, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((921705683973 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix26,
    observedExtremizedFinalConsensusLoss26]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix28 :
    (∑ i ∈ Finset.range 28, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((921755683973 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix27,
    observedExtremizedFinalConsensusLoss27]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix29 :
    (∑ i ∈ Finset.range 29, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1843660085971 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix28,
    observedExtremizedFinalConsensusLoss28]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix30 :
    (∑ i ∈ Finset.range 30, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1843760085971 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix29,
    observedExtremizedFinalConsensusLoss29]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix31 :
    (∑ i ∈ Finset.range 31, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((460977200999 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix30,
    observedExtremizedFinalConsensusLoss30]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix32 :
    (∑ i ∈ Finset.range 32, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((461002200999 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix31,
    observedExtremizedFinalConsensusLoss31]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix33 :
    (∑ i ∈ Finset.range 33, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1844157522021 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix32,
    observedExtremizedFinalConsensusLoss32]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix34 :
    (∑ i ∈ Finset.range 34, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1844257522021 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix33,
    observedExtremizedFinalConsensusLoss33]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix35 :
    (∑ i ∈ Finset.range 35, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1844357522021 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix34,
    observedExtremizedFinalConsensusLoss34]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix36 :
    (∑ i ∈ Finset.range 36, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((922253120023 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix35,
    observedExtremizedFinalConsensusLoss35]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix37 :
    (∑ i ∈ Finset.range 37, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1844654958071 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix36,
    observedExtremizedFinalConsensusLoss36]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix38 :
    (∑ i ∈ Finset.range 38, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((115630332597 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix37,
    observedExtremizedFinalConsensusLoss37]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix39 :
    (∑ i ∈ Finset.range 39, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((170993599033 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix38,
    observedExtremizedFinalConsensusLoss38]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix40 :
    (∑ i ∈ Finset.range 40, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((170999849033 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix39,
    observedExtremizedFinalConsensusLoss39]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix41 :
    (∑ i ∈ Finset.range 41, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((171006099033 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix40,
    observedExtremizedFinalConsensusLoss40]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix42 :
    (∑ i ∈ Finset.range 42, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((171012349033 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix41,
    observedExtremizedFinalConsensusLoss41]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix43 :
    (∑ i ∈ Finset.range 43, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((171018599033 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix42,
    observedExtremizedFinalConsensusLoss42]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix44 :
    (∑ i ∈ Finset.range 44, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((171024849033 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix43,
    observedExtremizedFinalConsensusLoss43]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix45 :
    (∑ i ∈ Finset.range 45, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2736546302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix44,
    observedExtremizedFinalConsensusLoss44]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix46 :
    (∑ i ∈ Finset.range 46, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2736646302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix45,
    observedExtremizedFinalConsensusLoss45]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix47 :
    (∑ i ∈ Finset.range 47, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2736746302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix46,
    observedExtremizedFinalConsensusLoss46]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix48 :
    (∑ i ∈ Finset.range 48, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2736846302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix47,
    observedExtremizedFinalConsensusLoss47]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix49 :
    (∑ i ∈ Finset.range 49, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2736946302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix48,
    observedExtremizedFinalConsensusLoss48]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix50 :
    (∑ i ∈ Finset.range 50, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737046302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix49,
    observedExtremizedFinalConsensusLoss49]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix51 :
    (∑ i ∈ Finset.range 51, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737146302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix50,
    observedExtremizedFinalConsensusLoss50]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix52 :
    (∑ i ∈ Finset.range 52, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737246302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix51,
    observedExtremizedFinalConsensusLoss51]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix53 :
    (∑ i ∈ Finset.range 53, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737346302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix52,
    observedExtremizedFinalConsensusLoss52]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix54 :
    (∑ i ∈ Finset.range 54, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737446302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix53,
    observedExtremizedFinalConsensusLoss53]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix55 :
    (∑ i ∈ Finset.range 55, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737546302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix54,
    observedExtremizedFinalConsensusLoss54]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix56 :
    (∑ i ∈ Finset.range 56, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737646302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix55,
    observedExtremizedFinalConsensusLoss55]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix57 :
    (∑ i ∈ Finset.range 57, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737746302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix56,
    observedExtremizedFinalConsensusLoss56]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix58 :
    (∑ i ∈ Finset.range 58, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737846302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix57,
    observedExtremizedFinalConsensusLoss57]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix59 :
    (∑ i ∈ Finset.range 59, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2737946302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix58,
    observedExtremizedFinalConsensusLoss58]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix60 :
    (∑ i ∈ Finset.range 60, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2738046302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix59,
    observedExtremizedFinalConsensusLoss59]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix61 :
    (∑ i ∈ Finset.range 61, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2738146302553 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix60,
    observedExtremizedFinalConsensusLoss60]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix62 :
    (∑ i ∈ Finset.range 62, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1369529201477 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix61,
    observedExtremizedFinalConsensusLoss61]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix63 :
    (∑ i ∈ Finset.range 63, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1369579201477 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix62,
    observedExtremizedFinalConsensusLoss62]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix64 :
    (∑ i ∈ Finset.range 64, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1369629201477 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix63,
    observedExtremizedFinalConsensusLoss63]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix65 :
    (∑ i ∈ Finset.range 65, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2739407120979 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix64,
    observedExtremizedFinalConsensusLoss64]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix66 :
    (∑ i ∈ Finset.range 66, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((684920711751 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix65,
    observedExtremizedFinalConsensusLoss65]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix67 :
    (∑ i ∈ Finset.range 67, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((137157155499 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix66,
    observedExtremizedFinalConsensusLoss66]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix68 :
    (∑ i ∈ Finset.range 68, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((137162155499 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix67,
    observedExtremizedFinalConsensusLoss67]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix69 :
    (∑ i ∈ Finset.range 69, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((137167155499 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix68,
    observedExtremizedFinalConsensusLoss68]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix70 :
    (∑ i ∈ Finset.range 70, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686700843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix69,
    observedExtremizedFinalConsensusLoss69]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix71 :
    (∑ i ∈ Finset.range 71, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686725843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix70,
    observedExtremizedFinalConsensusLoss70]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix72 :
    (∑ i ∈ Finset.range 72, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686750843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix71,
    observedExtremizedFinalConsensusLoss71]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix73 :
    (∑ i ∈ Finset.range 73, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686775843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix72,
    observedExtremizedFinalConsensusLoss72]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix74 :
    (∑ i ∈ Finset.range 74, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686800843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix73,
    observedExtremizedFinalConsensusLoss73]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix75 :
    (∑ i ∈ Finset.range 75, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686825843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix74,
    observedExtremizedFinalConsensusLoss74]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix76 :
    (∑ i ∈ Finset.range 76, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686850843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix75,
    observedExtremizedFinalConsensusLoss75]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix77 :
    (∑ i ∈ Finset.range 77, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((686875843239 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix76,
    observedExtremizedFinalConsensusLoss76]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix78 :
    (∑ i ∈ Finset.range 78, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2747652090981 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix77,
    observedExtremizedFinalConsensusLoss77]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix79 :
    (∑ i ∈ Finset.range 79, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1373900404503 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix78,
    observedExtremizedFinalConsensusLoss78]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix80 :
    (∑ i ∈ Finset.range 80, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2747949527031 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix79,
    observedExtremizedFinalConsensusLoss79]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix81 :
    (∑ i ∈ Finset.range 81, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2751409790007 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix80,
    observedExtremizedFinalConsensusLoss80]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix82 :
    (∑ i ∈ Finset.range 82, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3001409790007 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix81,
    observedExtremizedFinalConsensusLoss81]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix83 :
    (∑ i ∈ Finset.range 83, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3096084156871 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix82,
    observedExtremizedFinalConsensusLoss82]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix84 :
    (∑ i ∈ Finset.range 84, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3106084156871 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix83,
    observedExtremizedFinalConsensusLoss83]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix85 :
    (∑ i ∈ Finset.range 85, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((626032501291 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix84,
    observedExtremizedFinalConsensusLoss84]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix86 :
    (∑ i ∈ Finset.range 86, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3133622769431 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix85,
    observedExtremizedFinalConsensusLoss85]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix87 :
    (∑ i ∈ Finset.range 87, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((126388045743 : Rat) / 40000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix86,
    observedExtremizedFinalConsensusLoss86]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix88 :
    (∑ i ∈ Finset.range 88, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((395045957633 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix87,
    observedExtremizedFinalConsensusLoss87]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix89 :
    (∑ i ∈ Finset.range 89, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((79095698101 : Rat) / 25000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix88,
    observedExtremizedFinalConsensusLoss88]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix90 :
    (∑ i ∈ Finset.range 90, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((398488284203 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix89,
    observedExtremizedFinalConsensusLoss89]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix91 :
    (∑ i ∈ Finset.range 91, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((647685655213 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix90,
    observedExtremizedFinalConsensusLoss90]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix92 :
    (∑ i ∈ Finset.range 92, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1919704139253 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix91,
    observedExtremizedFinalConsensusLoss91]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix93 :
    (∑ i ∈ Finset.range 93, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((393408264537 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix92,
    observedExtremizedFinalConsensusLoss92]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix94 :
    (∑ i ∈ Finset.range 94, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2206686506117 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix93,
    observedExtremizedFinalConsensusLoss93]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix95 :
    (∑ i ∈ Finset.range 95, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((907638921767 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix94,
    observedExtremizedFinalConsensusLoss94]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix96 :
    (∑ i ∈ Finset.range 96, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((909638921767 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix95,
    observedExtremizedFinalConsensusLoss95]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix97 :
    (∑ i ∈ Finset.range 97, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((4592178765011 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix96,
    observedExtremizedFinalConsensusLoss96]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix98 :
    (∑ i ∈ Finset.range 98, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5402178765011 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix97,
    observedExtremizedFinalConsensusLoss97]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix99 :
    (∑ i ∈ Finset.range 99, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5405639027987 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix98,
    observedExtremizedFinalConsensusLoss98]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix100 :
    (∑ i ∈ Finset.range 100, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1351446936503 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix99,
    observedExtremizedFinalConsensusLoss99]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix101 :
    (∑ i ∈ Finset.range 101, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1351471936503 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix100,
    observedExtremizedFinalConsensusLoss100]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix102 :
    (∑ i ∈ Finset.range 102, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5406036464037 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix101,
    observedExtremizedFinalConsensusLoss101]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix103 :
    (∑ i ∈ Finset.range 103, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5406136464037 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix102,
    observedExtremizedFinalConsensusLoss102]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix104 :
    (∑ i ∈ Finset.range 104, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2703142591031 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix103,
    observedExtremizedFinalConsensusLoss103]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix105 :
    (∑ i ∈ Finset.range 105, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5406433900087 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix104,
    observedExtremizedFinalConsensusLoss104]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix106 :
    (∑ i ∈ Finset.range 106, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2639932919 : Rat) / 488281250) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix105,
    observedExtremizedFinalConsensusLoss105]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix107 :
    (∑ i ∈ Finset.range 107, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5406731336137 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix106,
    observedExtremizedFinalConsensusLoss106]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix108 :
    (∑ i ∈ Finset.range 108, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5406831336137 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix107,
    observedExtremizedFinalConsensusLoss107]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix109 :
    (∑ i ∈ Finset.range 109, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2703748926813 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix108,
    observedExtremizedFinalConsensusLoss108]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix110 :
    (∑ i ∈ Finset.range 110, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2705479058301 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix109,
    observedExtremizedFinalConsensusLoss109]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix111 :
    (∑ i ∈ Finset.range 111, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2706535678751 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix110,
    observedExtremizedFinalConsensusLoss110]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix112 :
    (∑ i ∈ Finset.range 112, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2706585678751 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix111,
    observedExtremizedFinalConsensusLoss111]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix113 :
    (∑ i ∈ Finset.range 113, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2753922862183 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix112,
    observedExtremizedFinalConsensusLoss112]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix114 :
    (∑ i ∈ Finset.range 114, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2878922862183 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix113,
    observedExtremizedFinalConsensusLoss113]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix115 :
    (∑ i ∈ Finset.range 115, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((2878972862183 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix114,
    observedExtremizedFinalConsensusLoss114]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix116 :
    (∑ i ∈ Finset.range 116, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5758094442391 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix115,
    observedExtremizedFinalConsensusLoss115]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix117 :
    (∑ i ∈ Finset.range 117, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((5758194442391 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix116,
    observedExtremizedFinalConsensusLoss116]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix118 :
    (∑ i ∈ Finset.range 118, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((179948223763 : Rat) / 31250000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix117,
    observedExtremizedFinalConsensusLoss117]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix119 :
    (∑ i ∈ Finset.range 119, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((180056356981 : Rat) / 31250000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix118,
    observedExtremizedFinalConsensusLoss118]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix120 :
    (∑ i ∈ Finset.range 120, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((6702313523793 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix119,
    observedExtremizedFinalConsensusLoss119]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix121 :
    (∑ i ∈ Finset.range 121, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3351231120909 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix120,
    observedExtremizedFinalConsensusLoss120]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix122 :
    (∑ i ∈ Finset.range 122, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3352961252397 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix121,
    observedExtremizedFinalConsensusLoss121]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix123 :
    (∑ i ∈ Finset.range 123, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3353011252397 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix122,
    observedExtremizedFinalConsensusLoss122]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix124 :
    (∑ i ∈ Finset.range 124, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3709878427189 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix123,
    observedExtremizedFinalConsensusLoss123]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix125 :
    (∑ i ∈ Finset.range 125, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3709928427189 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix124,
    observedExtremizedFinalConsensusLoss124]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix126 :
    (∑ i ∈ Finset.range 126, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3709978427189 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix125,
    observedExtremizedFinalConsensusLoss125]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix127 :
    (∑ i ∈ Finset.range 127, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3711708558677 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix126,
    observedExtremizedFinalConsensusLoss126]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix128 :
    (∑ i ∈ Finset.range 128, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((746740127353 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix127,
    observedExtremizedFinalConsensusLoss127]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix129 :
    (∑ i ∈ Finset.range 129, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7613098453739 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix128,
    observedExtremizedFinalConsensusLoss128]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix130 :
    (∑ i ∈ Finset.range 130, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7707772820603 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix129,
    observedExtremizedFinalConsensusLoss129]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix131 :
    (∑ i ∈ Finset.range 131, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1927623189003 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix130,
    observedExtremizedFinalConsensusLoss130]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix132 :
    (∑ i ∈ Finset.range 132, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1951291780719 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix131,
    observedExtremizedFinalConsensusLoss131]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix133 :
    (∑ i ∈ Finset.range 133, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7879734893917 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix132,
    observedExtremizedFinalConsensusLoss132]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix134 :
    (∑ i ∈ Finset.range 134, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3940323497159 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix133,
    observedExtremizedFinalConsensusLoss133]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix135 :
    (∑ i ∈ Finset.range 135, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3940490137927 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix134,
    observedExtremizedFinalConsensusLoss134]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix136 :
    (∑ i ∈ Finset.range 136, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7881128993879 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix135,
    observedExtremizedFinalConsensusLoss135]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix137 :
    (∑ i ∈ Finset.range 137, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((246289928497 : Rat) / 31250000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix136,
    observedExtremizedFinalConsensusLoss136]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix138 :
    (∑ i ∈ Finset.range 138, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((49279612343 : Rat) / 6250000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix137,
    observedExtremizedFinalConsensusLoss137]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix139 :
    (∑ i ∈ Finset.range 139, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1576977338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix138,
    observedExtremizedFinalConsensusLoss138]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix140 :
    (∑ i ∈ Finset.range 140, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1576997338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix139,
    observedExtremizedFinalConsensusLoss139]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix141 :
    (∑ i ∈ Finset.range 141, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1577017338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix140,
    observedExtremizedFinalConsensusLoss140]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix142 :
    (∑ i ∈ Finset.range 142, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1577037338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix141,
    observedExtremizedFinalConsensusLoss141]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix143 :
    (∑ i ∈ Finset.range 143, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1577057338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix142,
    observedExtremizedFinalConsensusLoss142]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix144 :
    (∑ i ∈ Finset.range 144, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1577077338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix143,
    observedExtremizedFinalConsensusLoss143]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix145 :
    (∑ i ∈ Finset.range 145, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1577097338581 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix144,
    observedExtremizedFinalConsensusLoss144]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix146 :
    (∑ i ∈ Finset.range 146, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((788563541093 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix145,
    observedExtremizedFinalConsensusLoss145]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix147 :
    (∑ i ∈ Finset.range 147, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((788573541093 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix146,
    observedExtremizedFinalConsensusLoss146]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix148 :
    (∑ i ∈ Finset.range 148, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((788583541093 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix147,
    observedExtremizedFinalConsensusLoss147]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix149 :
    (∑ i ∈ Finset.range 149, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((788593541093 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix148,
    observedExtremizedFinalConsensusLoss148]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix150 :
    (∑ i ∈ Finset.range 150, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7886847511331 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix149,
    observedExtremizedFinalConsensusLoss149]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix151 :
    (∑ i ∈ Finset.range 151, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7890307774307 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix150,
    observedExtremizedFinalConsensusLoss150]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix152 :
    (∑ i ∈ Finset.range 152, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1976197191969 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix151,
    observedExtremizedFinalConsensusLoss151]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix153 :
    (∑ i ∈ Finset.range 153, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((1976222191969 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix152,
    observedExtremizedFinalConsensusLoss152]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix154 :
    (∑ i ∈ Finset.range 154, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7905037485901 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix153,
    observedExtremizedFinalConsensusLoss153]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix155 :
    (∑ i ∈ Finset.range 155, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3952593101963 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix154,
    observedExtremizedFinalConsensusLoss154]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix156 :
    (∑ i ∈ Finset.range 156, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7905334921951 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix155,
    observedExtremizedFinalConsensusLoss155]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix157 :
    (∑ i ∈ Finset.range 157, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((988185454997 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix156,
    observedExtremizedFinalConsensusLoss156]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix158 :
    (∑ i ∈ Finset.range 158, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((988197954997 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix157,
    observedExtremizedFinalConsensusLoss157]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix159 :
    (∑ i ∈ Finset.range 159, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((988210454997 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix158,
    observedExtremizedFinalConsensusLoss158]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix160 :
    (∑ i ∈ Finset.range 160, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((988222954997 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix159,
    observedExtremizedFinalConsensusLoss159]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix161 :
    (∑ i ∈ Finset.range 161, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7905932358001 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix160,
    observedExtremizedFinalConsensusLoss160]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix162 :
    (∑ i ∈ Finset.range 162, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7906032358001 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix161,
    observedExtremizedFinalConsensusLoss161]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix163 :
    (∑ i ∈ Finset.range 163, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3953090538013 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix162,
    observedExtremizedFinalConsensusLoss162]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix164 :
    (∑ i ∈ Finset.range 164, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3953140538013 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix163,
    observedExtremizedFinalConsensusLoss163]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix165 :
    (∑ i ∈ Finset.range 165, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((3953190538013 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix164,
    observedExtremizedFinalConsensusLoss164]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix166 :
    (∑ i ∈ Finset.range 166, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7906529794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix165,
    observedExtremizedFinalConsensusLoss165]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix167 :
    (∑ i ∈ Finset.range 167, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7906629794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix166,
    observedExtremizedFinalConsensusLoss166]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix168 :
    (∑ i ∈ Finset.range 168, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7906729794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix167,
    observedExtremizedFinalConsensusLoss167]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix169 :
    (∑ i ∈ Finset.range 169, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7906829794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix168,
    observedExtremizedFinalConsensusLoss168]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix170 :
    (∑ i ∈ Finset.range 170, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7906929794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix169,
    observedExtremizedFinalConsensusLoss169]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix171 :
    (∑ i ∈ Finset.range 171, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7907029794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix170,
    observedExtremizedFinalConsensusLoss170]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix172 :
    (∑ i ∈ Finset.range 172, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7907129794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix171,
    observedExtremizedFinalConsensusLoss171]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix173 :
    (∑ i ∈ Finset.range 173, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7907229794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix172,
    observedExtremizedFinalConsensusLoss172]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix174 :
    (∑ i ∈ Finset.range 174, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7907329794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix173,
    observedExtremizedFinalConsensusLoss173]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusLossPrefix175 :
    (∑ i ∈ Finset.range 175, observedTrajectoryScore
        (monitorBrierScore extremizedFinalConsensus) i replayPath) =
      ratToReal ((7907429794051 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusLossPrefix174,
    observedExtremizedFinalConsensusLoss174]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor0 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 0 replayPath =
      ratToReal ((1 : Rat) / 2) := by
  norm_num [forwardPredictorProcess, forwardPredictor, ratToReal]

theorem observedExtremizedFinalConsensusPredictor1 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 1 replayPath =
      ratToReal ((5948721 : Rat) / 40000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix1]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor2 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 2 replayPath =
      ratToReal ((6111495857 : Rat) / 1000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix2]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor3 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 3 replayPath =
      ratToReal ((12548998831 : Rat) / 600000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix3]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor4 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 4 replayPath =
      ratToReal ((12568998831 : Rat) / 800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix4]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor5 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 5 replayPath =
      ratToReal ((12588998831 : Rat) / 1000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix5]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor6 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 6 replayPath =
      ratToReal ((12608998831 : Rat) / 1200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix6]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor7 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 7 replayPath =
      ratToReal ((12628998831 : Rat) / 1400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix7]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor8 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 8 replayPath =
      ratToReal ((3164685609 : Rat) / 400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix8]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor9 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 9 replayPath =
      ratToReal ((14554895203 : Rat) / 150000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix9]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor10 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 10 replayPath =
      ratToReal ((174688486041 : Rat) / 2000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix10]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor11 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 11 replayPath =
      ratToReal ((876902693181 : Rat) / 11000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix11]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor12 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 12 replayPath =
      ratToReal ((318127408553 : Rat) / 2400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix12]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor13 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 13 replayPath =
      ratToReal ((24472877581 : Rat) / 200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix13]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor14 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 14 replayPath =
      ratToReal ((318167408553 : Rat) / 2800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix14]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor15 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 15 replayPath =
      ratToReal ((538305130783 : Rat) / 5000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix15]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor16 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 16 replayPath =
      ratToReal ((807532055187 : Rat) / 8000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix16]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor17 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 17 replayPath =
      ratToReal ((807582055187 : Rat) / 8500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix17]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor18 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 18 replayPath =
      ratToReal ((1615312828399 : Rat) / 18000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix18]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor19 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 19 replayPath =
      ratToReal ((201932693303 : Rat) / 2375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix19]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor20 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 20 replayPath =
      ratToReal ((201945193303 : Rat) / 2500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix20]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor21 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 21 replayPath =
      ratToReal ((67319231101 : Rat) / 875000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix21]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor22 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 22 replayPath =
      ratToReal ((358497873101 : Rat) / 4400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix22]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor23 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 23 replayPath =
      ratToReal ((358517873101 : Rat) / 4600000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix23]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor24 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 24 replayPath =
      ratToReal ((307185227991 : Rat) / 4000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix24]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor25 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 25 replayPath =
      ratToReal ((921605683973 : Rat) / 12500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix25]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor26 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 26 replayPath =
      ratToReal ((921655683973 : Rat) / 13000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix26]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor27 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 27 replayPath =
      ratToReal ((307235227991 : Rat) / 4500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix27]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor28 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 28 replayPath =
      ratToReal ((921755683973 : Rat) / 14000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix28]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor29 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 29 replayPath =
      ratToReal ((1843660085971 : Rat) / 29000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix29]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor30 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 30 replayPath =
      ratToReal ((1843760085971 : Rat) / 30000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix30]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor31 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 31 replayPath =
      ratToReal ((460977200999 : Rat) / 7750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix31]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor32 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 32 replayPath =
      ratToReal ((461002200999 : Rat) / 8000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix32]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor33 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 33 replayPath =
      ratToReal ((614719174007 : Rat) / 11000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix33]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor34 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 34 replayPath =
      ratToReal ((1844257522021 : Rat) / 34000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix34]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor35 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 35 replayPath =
      ratToReal ((263479646003 : Rat) / 5000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix35]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor36 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 36 replayPath =
      ratToReal ((922253120023 : Rat) / 18000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix36]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor37 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 37 replayPath =
      ratToReal ((1844654958071 : Rat) / 37000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix37]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor38 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 38 replayPath =
      ratToReal ((115630332597 : Rat) / 2375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix38]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor39 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 39 replayPath =
      ratToReal ((170993599033 : Rat) / 2437500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix39]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor40 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 40 replayPath =
      ratToReal ((170999849033 : Rat) / 2500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix40]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor41 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 41 replayPath =
      ratToReal ((171006099033 : Rat) / 2562500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix41]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor42 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 42 replayPath =
      ratToReal ((171012349033 : Rat) / 2625000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix42]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor43 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 43 replayPath =
      ratToReal ((171018599033 : Rat) / 2687500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix43]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor44 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 44 replayPath =
      ratToReal ((171024849033 : Rat) / 2750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix44]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor45 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 45 replayPath =
      ratToReal ((912182100851 : Rat) / 15000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix45]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor46 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 46 replayPath =
      ratToReal ((2736646302553 : Rat) / 46000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix46]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor47 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 47 replayPath =
      ratToReal ((2736746302553 : Rat) / 47000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix47]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor48 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 48 replayPath =
      ratToReal ((912282100851 : Rat) / 16000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix48]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor49 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 49 replayPath =
      ratToReal ((2736946302553 : Rat) / 49000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix49]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor50 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 50 replayPath =
      ratToReal ((2737046302553 : Rat) / 50000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix50]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor51 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 51 replayPath =
      ratToReal ((912382100851 : Rat) / 17000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix51]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor52 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 52 replayPath =
      ratToReal ((2737246302553 : Rat) / 52000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix52]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor53 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 53 replayPath =
      ratToReal ((2737346302553 : Rat) / 53000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix53]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor54 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 54 replayPath =
      ratToReal ((912482100851 : Rat) / 18000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix54]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor55 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 55 replayPath =
      ratToReal ((2737546302553 : Rat) / 55000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix55]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor56 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 56 replayPath =
      ratToReal ((2737646302553 : Rat) / 56000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix56]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor57 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 57 replayPath =
      ratToReal ((912582100851 : Rat) / 19000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix57]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor58 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 58 replayPath =
      ratToReal ((2737846302553 : Rat) / 58000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix58]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor59 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 59 replayPath =
      ratToReal ((2737946302553 : Rat) / 59000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix59]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor60 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 60 replayPath =
      ratToReal ((912682100851 : Rat) / 20000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix60]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor61 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 61 replayPath =
      ratToReal ((2738146302553 : Rat) / 61000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix61]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor62 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 62 replayPath =
      ratToReal ((1369529201477 : Rat) / 31000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix62]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor63 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 63 replayPath =
      ratToReal ((1369579201477 : Rat) / 31500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix63]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor64 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 64 replayPath =
      ratToReal ((1369629201477 : Rat) / 32000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix64]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor65 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 65 replayPath =
      ratToReal ((2739407120979 : Rat) / 65000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix65]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor66 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 66 replayPath =
      ratToReal ((228306903917 : Rat) / 5500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix66]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor67 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 67 replayPath =
      ratToReal ((137157155499 : Rat) / 3350000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix67]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor68 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 68 replayPath =
      ratToReal ((137162155499 : Rat) / 3400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix68]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor69 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 69 replayPath =
      ratToReal ((137167155499 : Rat) / 3450000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix69]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor70 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 70 replayPath =
      ratToReal ((686700843239 : Rat) / 17500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix70]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor71 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 71 replayPath =
      ratToReal ((686725843239 : Rat) / 17750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix71]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor72 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 72 replayPath =
      ratToReal ((686750843239 : Rat) / 18000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix72]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor73 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 73 replayPath =
      ratToReal ((686775843239 : Rat) / 18250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix73]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor74 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 74 replayPath =
      ratToReal ((686800843239 : Rat) / 18500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix74]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor75 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 75 replayPath =
      ratToReal ((686825843239 : Rat) / 18750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix75]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor76 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 76 replayPath =
      ratToReal ((36150044381 : Rat) / 1000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix76]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor77 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 77 replayPath =
      ratToReal ((686875843239 : Rat) / 19250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix77]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor78 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 78 replayPath =
      ratToReal ((915884030327 : Rat) / 26000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix78]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor79 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 79 replayPath =
      ratToReal ((1373900404503 : Rat) / 39500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix79]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor80 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 80 replayPath =
      ratToReal ((2747949527031 : Rat) / 80000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix80]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor81 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 81 replayPath =
      ratToReal ((917136596669 : Rat) / 27000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix81]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor82 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 82 replayPath =
      ratToReal ((3001409790007 : Rat) / 82000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix82]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor83 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 83 replayPath =
      ratToReal ((3096084156871 : Rat) / 83000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix83]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor84 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 84 replayPath =
      ratToReal ((3106084156871 : Rat) / 84000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix84]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor85 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 85 replayPath =
      ratToReal ((626032501291 : Rat) / 17000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix85]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor86 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 86 replayPath =
      ratToReal ((3133622769431 : Rat) / 86000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix86]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor87 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 87 replayPath =
      ratToReal ((42129348581 : Rat) / 1160000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix87]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor88 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 88 replayPath =
      ratToReal ((395045957633 : Rat) / 11000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix88]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor89 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 89 replayPath =
      ratToReal ((888715709 : Rat) / 25000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix89]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor90 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 90 replayPath =
      ratToReal ((398488284203 : Rat) / 11250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix90]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor91 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 91 replayPath =
      ratToReal ((647685655213 : Rat) / 18200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix91]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor92 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 92 replayPath =
      ratToReal ((1919704139253 : Rat) / 46000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix92]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor93 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 93 replayPath =
      ratToReal ((131136088179 : Rat) / 3100000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix93]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor94 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 94 replayPath =
      ratToReal ((2206686506117 : Rat) / 47000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix94]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor95 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 95 replayPath =
      ratToReal ((907638921767 : Rat) / 19000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix95]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor96 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 96 replayPath =
      ratToReal ((909638921767 : Rat) / 19200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix96]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor97 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 97 replayPath =
      ratToReal ((4592178765011 : Rat) / 97000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix97]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor98 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 98 replayPath =
      ratToReal ((771739823573 : Rat) / 14000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix98]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor99 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 99 replayPath =
      ratToReal ((491421729817 : Rat) / 9000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix99]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor100 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 100 replayPath =
      ratToReal ((1351446936503 : Rat) / 25000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix100]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor101 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 101 replayPath =
      ratToReal ((1351471936503 : Rat) / 25250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix101]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor102 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 102 replayPath =
      ratToReal ((1802012154679 : Rat) / 34000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix102]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor103 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 103 replayPath =
      ratToReal ((5406136464037 : Rat) / 103000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix103]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor104 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 104 replayPath =
      ratToReal ((2703142591031 : Rat) / 52000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix104]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor105 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 105 replayPath =
      ratToReal ((5406433900087 : Rat) / 105000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix105]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor106 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 106 replayPath =
      ratToReal ((2639932919 : Rat) / 51757812500) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix106]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor107 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 107 replayPath =
      ratToReal ((5406731336137 : Rat) / 107000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix107]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor108 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 108 replayPath =
      ratToReal ((5406831336137 : Rat) / 108000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix108]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor109 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 109 replayPath =
      ratToReal ((2703748926813 : Rat) / 54500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix109]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor110 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 110 replayPath =
      ratToReal ((2705479058301 : Rat) / 55000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix110]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor111 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 111 replayPath =
      ratToReal ((2706535678751 : Rat) / 55500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix111]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor112 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 112 replayPath =
      ratToReal ((2706585678751 : Rat) / 56000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix112]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor113 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 113 replayPath =
      ratToReal ((2753922862183 : Rat) / 56500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix113]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor114 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 114 replayPath =
      ratToReal ((959640954061 : Rat) / 19000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix114]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor115 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 115 replayPath =
      ratToReal ((2878972862183 : Rat) / 57500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix115]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor116 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 116 replayPath =
      ratToReal ((5758094442391 : Rat) / 116000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix116]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor117 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 117 replayPath =
      ratToReal ((5758194442391 : Rat) / 117000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix117]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor118 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 118 replayPath =
      ratToReal ((179948223763 : Rat) / 3687500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix118]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor119 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 119 replayPath =
      ratToReal ((180056356981 : Rat) / 3718750000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix119]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor120 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 120 replayPath =
      ratToReal ((2234104507931 : Rat) / 40000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix120]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor121 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 121 replayPath =
      ratToReal ((3351231120909 : Rat) / 60500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix121]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor122 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 122 replayPath =
      ratToReal ((3352961252397 : Rat) / 61000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix122]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor123 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 123 replayPath =
      ratToReal ((3353011252397 : Rat) / 61500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix123]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor124 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 124 replayPath =
      ratToReal ((3709878427189 : Rat) / 62000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix124]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor125 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 125 replayPath =
      ratToReal ((3709928427189 : Rat) / 62500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix125]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor126 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 126 replayPath =
      ratToReal ((3709978427189 : Rat) / 63000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix126]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor127 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 127 replayPath =
      ratToReal ((3711708558677 : Rat) / 63500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix127]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor128 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 128 replayPath =
      ratToReal ((746740127353 : Rat) / 12800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix128]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor129 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 129 replayPath =
      ratToReal ((7613098453739 : Rat) / 129000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix129]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor130 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 130 replayPath =
      ratToReal ((7707772820603 : Rat) / 130000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix130]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor131 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 131 replayPath =
      ratToReal ((1927623189003 : Rat) / 32750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix131]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor132 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 132 replayPath =
      ratToReal ((650430593573 : Rat) / 11000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix132]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor133 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 133 replayPath =
      ratToReal ((7879734893917 : Rat) / 133000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix133]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor134 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 134 replayPath =
      ratToReal ((3940323497159 : Rat) / 67000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix134]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor135 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 135 replayPath =
      ratToReal ((3940490137927 : Rat) / 67500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix135]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor136 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 136 replayPath =
      ratToReal ((7881128993879 : Rat) / 136000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix136]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor137 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 137 replayPath =
      ratToReal ((246289928497 : Rat) / 4281250000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix137]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor138 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 138 replayPath =
      ratToReal ((2142591841 : Rat) / 37500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix138]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor139 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 139 replayPath =
      ratToReal ((1576977338581 : Rat) / 27800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix139]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor140 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 140 replayPath =
      ratToReal ((225285334083 : Rat) / 4000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix140]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor141 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 141 replayPath =
      ratToReal ((1577017338581 : Rat) / 28200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix141]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor142 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 142 replayPath =
      ratToReal ((1577037338581 : Rat) / 28400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix142]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor143 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 143 replayPath =
      ratToReal ((1577057338581 : Rat) / 28600000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix143]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor144 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 144 replayPath =
      ratToReal ((1577077338581 : Rat) / 28800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix144]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor145 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 145 replayPath =
      ratToReal ((1577097338581 : Rat) / 29000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix145]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor146 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 146 replayPath =
      ratToReal ((788563541093 : Rat) / 14600000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix146]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor147 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 147 replayPath =
      ratToReal ((262857847031 : Rat) / 4900000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix147]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor148 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 148 replayPath =
      ratToReal ((788583541093 : Rat) / 14800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix148]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor149 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 149 replayPath =
      ratToReal ((788593541093 : Rat) / 14900000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix149]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor150 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 150 replayPath =
      ratToReal ((7886847511331 : Rat) / 150000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix150]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor151 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 151 replayPath =
      ratToReal ((7890307774307 : Rat) / 151000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix151]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor152 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 152 replayPath =
      ratToReal ((1976197191969 : Rat) / 38000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix152]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor153 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 153 replayPath =
      ratToReal ((1976222191969 : Rat) / 38250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix153]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor154 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 154 replayPath =
      ratToReal ((7905037485901 : Rat) / 154000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix154]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor155 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 155 replayPath =
      ratToReal ((3952593101963 : Rat) / 77500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix155]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor156 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 156 replayPath =
      ratToReal ((7905334921951 : Rat) / 156000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix156]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor157 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 157 replayPath =
      ratToReal ((988185454997 : Rat) / 19625000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix157]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor158 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 158 replayPath =
      ratToReal ((988197954997 : Rat) / 19750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix158]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor159 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 159 replayPath =
      ratToReal ((329403484999 : Rat) / 6625000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix159]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor160 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 160 replayPath =
      ratToReal ((988222954997 : Rat) / 20000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix160]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor161 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 161 replayPath =
      ratToReal ((7905932358001 : Rat) / 161000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix161]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor162 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 162 replayPath =
      ratToReal ((7906032358001 : Rat) / 162000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix162]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor163 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 163 replayPath =
      ratToReal ((3953090538013 : Rat) / 81500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix163]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor164 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 164 replayPath =
      ratToReal ((3953140538013 : Rat) / 82000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix164]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor165 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 165 replayPath =
      ratToReal ((3953190538013 : Rat) / 82500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix165]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor166 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 166 replayPath =
      ratToReal ((7906529794051 : Rat) / 166000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix166]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor167 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 167 replayPath =
      ratToReal ((7906629794051 : Rat) / 167000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix167]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor168 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 168 replayPath =
      ratToReal ((2635576598017 : Rat) / 56000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix168]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor169 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 169 replayPath =
      ratToReal ((7906829794051 : Rat) / 169000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix169]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor170 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 170 replayPath =
      ratToReal ((7906929794051 : Rat) / 170000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix170]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor171 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 171 replayPath =
      ratToReal ((2635676598017 : Rat) / 57000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix171]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor172 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 172 replayPath =
      ratToReal ((7907129794051 : Rat) / 172000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix172]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor173 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 173 replayPath =
      ratToReal ((7907229794051 : Rat) / 173000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix173]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusPredictor174 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus)) 174 replayPath =
      ratToReal ((2635776598017 : Rat) / 58000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedExtremizedFinalConsensusLossPrefix174]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix0 :
    (∑ i ∈ Finset.range 0,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal 0 := by
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix1 :
    (∑ i ∈ Finset.range 1,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((399762086547281535841 : Rat) / 1600000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix0,
    observedExtremizedFinalConsensusLoss0,
    observedExtremizedFinalConsensusPredictor0]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix2 :
    (∑ i ∈ Finset.range 2,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((249993522969946122381521 : Rat) / 1000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix1,
    observedExtremizedFinalConsensusLoss1,
    observedExtremizedFinalConsensusPredictor1]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix3 :
    (∑ i ∈ Finset.range 3,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((251965816064993629730577 : Rat) / 1000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix2,
    observedExtremizedFinalConsensusLoss2,
    observedExtremizedFinalConsensusPredictor2]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix4 :
    (∑ i ∈ Finset.range 4,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1135795860939980325869609 : Rat) / 4500000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix3,
    observedExtremizedFinalConsensusLoss3,
    observedExtremizedFinalConsensusPredictor3]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix5 :
    (∑ i ∈ Finset.range 5,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((36380561945734532285303713 : Rat) / 144000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix4,
    observedExtremizedFinalConsensusLoss4,
    observedExtremizedFinalConsensusPredictor4]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix6 :
    (∑ i ∈ Finset.range 6,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((36403022358953835874088497 : Rat) / 144000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix5,
    observedExtremizedFinalConsensusLoss5,
    observedExtremizedFinalConsensusPredictor5]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix7 :
    (∑ i ∈ Finset.range 7,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((36418619868133907810744597 : Rat) / 144000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix6,
    observedExtremizedFinalConsensusLoss6,
    observedExtremizedFinalConsensusPredictor6]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix8 :
    (∑ i ∈ Finset.range 8,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1785067767547357447326862853 : Rat) / 7056000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix7,
    observedExtremizedFinalConsensusLoss7,
    observedExtremizedFinalConsensusPredictor7]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix9 :
    (∑ i ∈ Finset.range 9,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((6324514451699754343335714953 : Rat) / 7056000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix8,
    observedExtremizedFinalConsensusLoss8,
    observedExtremizedFinalConsensusPredictor8]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix10 :
    (∑ i ∈ Finset.range 10,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((2130248516159639738058630451 : Rat) / 2352000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix9,
    observedExtremizedFinalConsensusLoss9,
    observedExtremizedFinalConsensusPredictor9]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix11 :
    (∑ i ∈ Finset.range 11,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((2146798416157905224628727999 : Rat) / 2352000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix10,
    observedExtremizedFinalConsensusLoss10,
    observedExtremizedFinalConsensusPredictor10]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix12 :
    (∑ i ∈ Finset.range 12,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((374161816370499489260169915127 : Rat) / 284592000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix11,
    observedExtremizedFinalConsensusLoss11,
    observedExtremizedFinalConsensusPredictor11]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix13 :
    (∑ i ∈ Finset.range 13,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((568731970885481448237211542203 : Rat) / 426888000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix12,
    observedExtremizedFinalConsensusLoss12,
    observedExtremizedFinalConsensusPredictor12]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix14 :
    (∑ i ∈ Finset.range 14,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((575113340539217772887872846403 : Rat) / 426888000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix13,
    observedExtremizedFinalConsensusLoss13,
    observedExtremizedFinalConsensusPredictor13]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix15 :
    (∑ i ∈ Finset.range 15,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((578536861115698454753421672341 : Rat) / 426888000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix14,
    observedExtremizedFinalConsensusLoss14,
    observedExtremizedFinalConsensusPredictor14]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix16 :
    (∑ i ∈ Finset.range 16,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((14586780382050237278025945264557 : Rat) / 10672200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix15,
    observedExtremizedFinalConsensusLoss15,
    observedExtremizedFinalConsensusPredictor15]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix17 :
    (∑ i ∈ Finset.range 17,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((117562448683044685125576930886681 : Rat) / 85377600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix16,
    observedExtremizedFinalConsensusLoss16,
    observedExtremizedFinalConsensusPredictor16]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix18 :
    (∑ i ∈ Finset.range 18,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((34197580191395240873558666952588409 : Rat) / 24674126400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix17,
    observedExtremizedFinalConsensusLoss17,
    observedExtremizedFinalConsensusPredictor17]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix19 :
    (∑ i ∈ Finset.range 19,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((309560649468575208586615333259728081 : Rat) / 222067137600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix18,
    observedExtremizedFinalConsensusLoss18,
    observedExtremizedFinalConsensusPredictor18]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix20 :
    (∑ i ∈ Finset.range 20,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((112329564208156074467968141428791814841 : Rat) / 80166236673600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix19,
    observedExtremizedFinalConsensusLoss19,
    observedExtremizedFinalConsensusPredictor19]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix21 :
    (∑ i ∈ Finset.range 21,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((902810899260251658238149175631390957 : Rat) / 641329893388800000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix20,
    observedExtremizedFinalConsensusLoss20,
    observedExtremizedFinalConsensusPredictor20]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix22 :
    (∑ i ∈ Finset.range 22,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((649435925662795877346717883567225303 : Rat) / 458092780992000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix21,
    observedExtremizedFinalConsensusLoss21,
    observedExtremizedFinalConsensusPredictor21]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix23 :
    (∑ i ∈ Finset.range 23,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((652469499359706550715283733315682503 : Rat) / 458092780992000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix22,
    observedExtremizedFinalConsensusLoss22,
    observedExtremizedFinalConsensusPredictor22]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix24 :
    (∑ i ∈ Finset.range 24,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((69067703805256864476091743377442126347 : Rat) / 48466216228953600000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix23,
    observedExtremizedFinalConsensusLoss23,
    observedExtremizedFinalConsensusPredictor23]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix25 :
    (∑ i ∈ Finset.range 25,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((346763988841401480465423888448667935123 : Rat) / 242331081144768000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix24,
    observedExtremizedFinalConsensusLoss24,
    observedExtremizedFinalConsensusPredictor24]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix26 :
    (∑ i ∈ Finset.range 26,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((217548563639383408347829869099816866203363 : Rat) / 151456925715480000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix25,
    observedExtremizedFinalConsensusLoss25,
    observedExtremizedFinalConsensusPredictor25]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix27 :
    (∑ i ∈ Finset.range 27,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((36893999538416340238430113318400207693288347 : Rat) / 25596220445916120000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix26,
    observedExtremizedFinalConsensusLoss26,
    observedExtremizedFinalConsensusPredictor26]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix28 :
    (∑ i ∈ Finset.range 28,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((37012964673603895653916095537603311037768347 : Rat) / 25596220445916120000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix27,
    observedExtremizedFinalConsensusLoss27,
    observedExtremizedFinalConsensusPredictor27]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix29 :
    (∑ i ∈ Finset.range 29,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((259863941026852194401192184165448556580788429 : Rat) / 179173543121412840000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix28,
    observedExtremizedFinalConsensusLoss28,
    observedExtremizedFinalConsensusPredictor28]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix30 :
    (∑ i ∈ Finset.range 30,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((219152685623939727795269421964453771386721508789 : Rat) / 150684949765108198440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix29,
    observedExtremizedFinalConsensusLoss29,
    observedExtremizedFinalConsensusPredictor29]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix31 :
    (∑ i ∈ Finset.range 31,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((219719096811642008177631794606913229670912184389 : Rat) / 150684949765108198440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix30,
    observedExtremizedFinalConsensusLoss30,
    observedExtremizedFinalConsensusPredictor30]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix32 :
    (∑ i ∈ Finset.range 32,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((211660659598974761229409555845821313457991704237829 : Rat) / 144808236724268978700840000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix31,
    observedExtremizedFinalConsensusLoss31,
    observedExtremizedFinalConsensusPredictor31]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix33 :
    (∑ i ∈ Finset.range 33,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((106069520758924016441909291394954324796959702719227 : Rat) / 72404118362134489350420000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix32,
    observedExtremizedFinalConsensusLoss32,
    observedExtremizedFinalConsensusPredictor32]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix34 :
    (∑ i ∈ Finset.range 34,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((106294828307750567497145945460917591922441035699227 : Rat) / 72404118362134489350420000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix33,
    observedExtremizedFinalConsensusLoss33,
    observedExtremizedFinalConsensusPredictor33]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix35 :
    (∑ i ∈ Finset.range 35,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((106507077374075925714406080649355306368504332944227 : Rat) / 72404118362134489350420000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix34,
    observedExtremizedFinalConsensusLoss34,
    observedExtremizedFinalConsensusPredictor34]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix36 :
    (∑ i ∈ Finset.range 36,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((106707000306465090230085834001546363009592043795427 : Rat) / 72404118362134489350420000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix35,
    observedExtremizedFinalConsensusLoss35,
    observedExtremizedFinalConsensusPredictor35]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix37 :
    (∑ i ∈ Finset.range 37,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((11877330074533220462096959767012871300219798915603 : Rat) / 8044902040237165483380000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix36,
    observedExtremizedFinalConsensusLoss36,
    observedExtremizedFinalConsensusPredictor36]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix38 :
    (∑ i ∈ Finset.range 38,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((16281801016957070384845718865405723298208105112340507 : Rat) / 11013470893084679546747220000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix37,
    observedExtremizedFinalConsensusLoss37,
    observedExtremizedFinalConsensusPredictor37]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix39 :
    (∑ i ∈ Finset.range 39,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((23999816931135902116356066123523021593854264268820507 : Rat) / 11013470893084679546747220000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix38,
    observedExtremizedFinalConsensusLoss38,
    observedExtremizedFinalConsensusPredictor38]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix40 :
    (∑ i ∈ Finset.range 40,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((616765690845691236110996383493600627037548260300013 : Rat) / 282396689566273834531980000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix39,
    observedExtremizedFinalConsensusLoss39,
    observedExtremizedFinalConsensusPredictor39]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix41 :
    (∑ i ∈ Finset.range 41,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((618083038009438853352833208791331071764919883695213 : Rat) / 282396689566273834531980000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix40,
    observedExtremizedFinalConsensusLoss40,
    observedExtremizedFinalConsensusPredictor40]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix42 :
    (∑ i ∈ Finset.range 42,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1041105342355862900073051544454596243200624921923973053 : Rat) / 474708835160906315848258380000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix41,
    observedExtremizedFinalConsensusLoss41,
    observedExtremizedFinalConsensusPredictor41]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix43 :
    (∑ i ∈ Finset.range 43,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3129341770148567597045080356698441457728981429519759159 : Rat) / 1424126505482718947544775140000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix42,
    observedExtremizedFinalConsensusLoss42,
    observedExtremizedFinalConsensusPredictor42]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix44 :
    (∑ i ∈ Finset.range 44,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5796782343799548260937286555497745667757102818033224444991 : Rat) / 2633209908637547334010289233860000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix43,
    observedExtremizedFinalConsensusLoss43,
    observedExtremizedFinalConsensusPredictor43]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix45 :
    (∑ i ∈ Finset.range 45,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5806918165582279490933599971074682083490033040399266784991 : Rat) / 2633209908637547334010289233860000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix44,
    observedExtremizedFinalConsensusLoss44,
    observedExtremizedFinalConsensusPredictor44]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix46 :
    (∑ i ∈ Finset.range 46,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5816624082379007048504221801149731257130733454379100766591 : Rat) / 2633209908637547334010289233860000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix45,
    observedExtremizedFinalConsensusLoss45,
    observedExtremizedFinalConsensusPredictor45]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix47 :
    (∑ i ∈ Finset.range 47,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5825912589710468912436409516604350622264201478154698031591 : Rat) / 2633209908637547334010289233860000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix46,
    observedExtremizedFinalConsensusLoss46,
    observedExtremizedFinalConsensusPredictor46]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix48 :
    (∑ i ∈ Finset.range 48,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((12889095392183799131652537828080985101204039403552891764524519 : Rat) / 5816760688180342060828728917596740000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix47,
    observedExtremizedFinalConsensusLoss47,
    observedExtremizedFinalConsensusPredictor47]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix49 :
    (∑ i ∈ Finset.range 49,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((103263515740467065375143374971305734419906350330245852388219277 : Rat) / 46534085505442736486629831340773920000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix48,
    observedExtremizedFinalConsensusLoss48,
    observedExtremizedFinalConsensusPredictor48]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix50 :
    (∑ i ∈ Finset.range 50,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5067000720207464428478163305975607409393194367704486418017464573 : Rat) / 2280170189766694087844861735697922080000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix49,
    observedExtremizedFinalConsensusLoss49,
    observedExtremizedFinalConsensusPredictor49]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix51 :
    (∑ i ∈ Finset.range 51,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5073808466554629355860494176234921425867393354446637458832793661 : Rat) / 2280170189766694087844861735697922080000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix50,
    observedExtremizedFinalConsensusLoss50,
    observedExtremizedFinalConsensusPredictor50]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix52 :
    (∑ i ∈ Finset.range 52,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5080351859814111216089570368333454698141709950700146725283513661 : Rat) / 2280170189766694087844861735697922080000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix51,
    observedExtremizedFinalConsensusLoss51,
    observedExtremizedFinalConsensusPredictor51]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix53 :
    (∑ i ∈ Finset.range 53,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((66126398051948408878663583902028589158464813334368145900023767593 : Rat) / 29642212466967023141983202564072987040000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix52,
    observedExtremizedFinalConsensusLoss52,
    observedExtremizedFinalConsensusPredictor52]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix54 :
    (∑ i ∈ Finset.range 54,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((185970303884205940680091760464226012481539127725360030659664958528737 : Rat) / 83264974819710368005830816002481020595360000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix53,
    observedExtremizedFinalConsensusLoss53,
    observedExtremizedFinalConsensusPredictor53]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix55 :
    (∑ i ∈ Finset.range 55,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1675650933054762583815429057058121843349194158778727386719803857518633 : Rat) / 749384773377393312052477344022329185358240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix54,
    observedExtremizedFinalConsensusLoss54,
    observedExtremizedFinalConsensusPredictor54]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix56 :
    (∑ i ∈ Finset.range 56,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1677500012608675637434425079788150214800677563398370499130614064757033 : Rat) / 749384773377393312052477344022329185358240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix55,
    observedExtremizedFinalConsensusLoss55,
    observedExtremizedFinalConsensusPredictor55]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix57 :
    (∑ i ∈ Finset.range 57,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1679283643237051589984636485642211383053463691897866804947801844379533 : Rat) / 749384773377393312052477344022329185358240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix56,
    observedExtremizedFinalConsensusLoss56,
    observedExtremizedFinalConsensusPredictor56]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix58 :
    (∑ i ∈ Finset.range 58,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1681005239312947861821344078365614221970280342859522826813822428219533 : Rat) / 749384773377393312052477344022329185358240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix57,
    observedExtremizedFinalConsensusLoss57,
    observedExtremizedFinalConsensusPredictor57]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix59 :
    (∑ i ∈ Finset.range 59,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1682667981777450533402040561349661731970499516157507492403210322659533 : Rat) / 749384773377393312052477344022329185358240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix58,
    observedExtremizedFinalConsensusLoss58,
    observedExtremizedFinalConsensusPredictor58]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix60 :
    (∑ i ∈ Finset.range 60,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5862960710217892293969966162816508312630046114718703996098276010073994373 : Rat) / 2608608396126706119254673634541727894232033440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix59,
    observedExtremizedFinalConsensusLoss59,
    observedExtremizedFinalConsensusPredictor59]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix61 :
    (∑ i ∈ Finset.range 61,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5868369280753918211312846327885332479878214597421469958532620941317197973 : Rat) / 2608608396126706119254673634541727894232033440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix60,
    observedExtremizedFinalConsensusLoss60,
    observedExtremizedFinalConsensusPredictor60]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix62 :
    (∑ i ∈ Finset.range 62,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((21854973248740057837549998094143172257905266250558683099067479918439209817533 : Rat) / 9706631841987473469746640594129769494437396430240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix61,
    observedExtremizedFinalConsensusLoss61,
    observedExtremizedFinalConsensusPredictor61]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix63 :
    (∑ i ∈ Finset.range 63,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((21873832282559641763182884672675060647739263384437849624198222985522141177533 : Rat) / 9706631841987473469746640594129769494437396430240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix62,
    observedExtremizedFinalConsensusLoss62,
    observedExtremizedFinalConsensusPredictor62]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix64 :
    (∑ i ∈ Finset.range 64,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((21892097368476114580046783893606423452103557912689680342918952728496892537533 : Rat) / 9706631841987473469746640594129769494437396430240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix63,
    observedExtremizedFinalConsensusLoss63,
    observedExtremizedFinalConsensusPredictor63]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix65 :
    (∑ i ∈ Finset.range 65,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((87639023069011338524360411301083524132438987265350068312033005097003142450757 : Rat) / 38826527367949893878986562376519077977749585720960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix64,
    observedExtremizedFinalConsensusLoss64,
    observedExtremizedFinalConsensusPredictor64]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix66 :
    (∑ i ∈ Finset.range 66,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((87707086478949616598778723675871885534780335613612819323192030684872290508357 : Rat) / 38826527367949893878986562376519077977749585720960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix65,
    observedExtremizedFinalConsensusLoss65,
    observedExtremizedFinalConsensusPredictor65]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix67 :
    (∑ i ∈ Finset.range 67,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((87763299868143058026847678224729969175052126894115867067600215902411385548357 : Rat) / 38826527367949893878986562376519077977749585720960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix66,
    observedExtremizedFinalConsensusLoss66,
    observedExtremizedFinalConsensusPredictor66]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix68 :
    (∑ i ∈ Finset.range 68,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((394260190838925692231770960030740120946613690757378206565721935495991574110574573 : Rat) / 174292281354727073622770678508194141042117890301389440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix67,
    observedExtremizedFinalConsensusLoss67,
    observedExtremizedFinalConsensusPredictor67]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix69 :
    (∑ i ∈ Finset.range 69,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((394542440335833699329390126791638391222695712266718116594787384926331140334574573 : Rat) / 174292281354727073622770678508194141042117890301389440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix68,
    observedExtremizedFinalConsensusLoss68,
    observedExtremizedFinalConsensusPredictor68]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix70 :
    (∑ i ∈ Finset.range 70,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((394772082436685153621574720351360883152834072456007674715108772302244362898414573 : Rat) / 174292281354727073622770678508194141042117890301389440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix69,
    observedExtremizedFinalConsensusLoss69,
    observedExtremizedFinalConsensusPredictor69]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix71 :
    (∑ i ∈ Finset.range 71,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((395039088341885231410140252612100425310122371239375891373533504835670376390536173 : Rat) / 174292281354727073622770678508194141042117890301389440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix70,
    observedExtremizedFinalConsensusLoss70,
    observedExtremizedFinalConsensusPredictor70]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix72 :
    (∑ i ∈ Finset.range 72,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1992700373266923832702488121495222000559039537456198130040263587290401833496088688093 : Rat) / 878607390309179178132386990359806664993316285009304167040000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix71,
    observedExtremizedFinalConsensusLoss71,
    observedExtremizedFinalConsensusPredictor71]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix73 :
    (∑ i ∈ Finset.range 73,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((221552512456693453150233127092989802121292513322853032600025932620634982028276538677 : Rat) / 97623043367686575348042998928867407221479587223256018560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix72,
    observedExtremizedFinalConsensusLoss72,
    observedExtremizedFinalConsensusPredictor72]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix74 :
    (∑ i ∈ Finset.range 74,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1181386148455470145331767707147353917379141418988383808820880803361464109969524166769733 : Rat) / 520233198106401760029721141291934413083264720312731322906240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix73,
    observedExtremizedFinalConsensusLoss73,
    observedExtremizedFinalConsensusPredictor73]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix75 :
    (∑ i ∈ Finset.range 75,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1182099286187120557820894909853324555533025384830422904849018268719880554337297783409733 : Rat) / 520233198106401760029721141291934413083264720312731322906240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix74,
    observedExtremizedFinalConsensusLoss74,
    observedExtremizedFinalConsensusPredictor74]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix76 :
    (∑ i ∈ Finset.range 76,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((131421503743626089808059149233438930161065410106116245523472760925471932197634140373341 : Rat) / 57803688678489084447746793476881601453696080034747924767360000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix75,
    observedExtremizedFinalConsensusLoss75,
    observedExtremizedFinalConsensusPredictor75]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix77 :
    (∑ i ∈ Finset.range 77,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((131496625746906284844810083405836114189433150121332583047520174750931466849794965333341 : Rat) / 57803688678489084447746793476881601453696080034747924767360000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix76,
    observedExtremizedFinalConsensusLoss76,
    observedExtremizedFinalConsensusPredictor76]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix78 :
    (∑ i ∈ Finset.range 78,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((131569608933931225332925943452619969284235649738452721302584270382747193914113455573341 : Rat) / 57803688678489084447746793476881601453696080034747924767360000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix77,
    observedExtremizedFinalConsensusLoss77,
    observedExtremizedFinalConsensusPredictor77]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix79 :
    (∑ i ∈ Finset.range 79,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((131640732753107897284608871496239541417221188895241889565943084156750390127845265013341 : Rat) / 57803688678489084447746793476881601453696080034747924767360000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix78,
    observedExtremizedFinalConsensusLoss78,
    observedExtremizedFinalConsensusPredictor78]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix80 :
    (∑ i ∈ Finset.range 80,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((822002530428017259107282901225412454841961460125109932495325811223314630552226627581221181 : Rat) / 360752821042450376038387738089218074672517235496861798473093760000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix79,
    observedExtremizedFinalConsensusLoss79,
    observedExtremizedFinalConsensusPredictor79]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix81 :
    (∑ i ∈ Finset.range 81,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((822346737997836104915787676274861452262295740696639306062250662137667278947563057933002081 : Rat) / 360752821042450376038387738089218074672517235496861798473093760000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix80,
    observedExtremizedFinalConsensusLoss80,
    observedExtremizedFinalConsensusPredictor80]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix82 :
    (∑ i ∈ Finset.range 82,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((611764411073864287336923367906290994761242604958889862268488096792526129279568010113957877049 : Rat) / 262988806539946324131984661067039976436265064677212251086885351040000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix81,
    observedExtremizedFinalConsensusLoss81,
    observedExtremizedFinalConsensusPredictor81]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix83 :
    (∑ i ∈ Finset.range 83,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((612651297414085777409867263319101312217282088365931683497964123813820211389674127009311637049 : Rat) / 262988806539946324131984661067039976436265064677212251086885351040000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix82,
    observedExtremizedFinalConsensusLoss82,
    observedExtremizedFinalConsensusPredictor82]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix84 :
    (∑ i ∈ Finset.range 84,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4221905271543465216631691991540452523506368461719007170633940798808790024380522127763128284270561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix83,
    observedExtremizedFinalConsensusLoss83,
    observedExtremizedFinalConsensusPredictor83]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix85 :
    (∑ i ∈ Finset.range 85,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4222206707424139445869156772091512189172596351965293621178884165628546461277154321352338845270561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix84,
    observedExtremizedFinalConsensusLoss84,
    observedExtremizedFinalConsensusPredictor84]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix86 :
    (∑ i ∈ Finset.range 86,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4224223588766263878663923554611332897700034072590730086762466810356600838463511513120547716310561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix85,
    observedExtremizedFinalConsensusLoss85,
    observedExtremizedFinalConsensusPredictor85]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix87 :
    (∑ i ∈ Finset.range 87,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4224418007223772012658765803388122020642717892369902943328408949257734635220211062535268114550561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix86,
    observedExtremizedFinalConsensusLoss86,
    observedExtremizedFinalConsensusPredictor86]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix88 :
    (∑ i ∈ Finset.range 88,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4226720819195141695710649759048073100921357612356310783646407296222814421908396801777786888310561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix87,
    observedExtremizedFinalConsensusLoss87,
    observedExtremizedFinalConsensusPredictor87]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix89 :
    (∑ i ∈ Finset.range 89,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4228628928750673983367699840612970746069948300841927831517096667865685882052820941774687266550561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix88,
    observedExtremizedFinalConsensusLoss88,
    observedExtremizedFinalConsensusPredictor88]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix90 :
    (∑ i ∈ Finset.range 90,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4228867293151702990647651212169344484106469790862531418719288618605388910931492230278555109110561 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix89,
    observedExtremizedFinalConsensusLoss89,
    observedExtremizedFinalConsensusPredictor89]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix91 :
    (∑ i ∈ Finset.range 91,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4229280430639224485441918259218200181357524662809676825990401042646067947209256165515424167696161 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix90,
    observedExtremizedFinalConsensusLoss90,
    observedExtremizedFinalConsensusPredictor90]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix92 :
    (∑ i ∈ Finset.range 92,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4808434506306274412117407551050983816465468638180059397486559906203194029497436289472890794256161 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix91,
    observedExtremizedFinalConsensusLoss91,
    observedExtremizedFinalConsensusPredictor91]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix93 :
    (∑ i ∈ Finset.range 93,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((4813512459488669884446261172340212245491801333150348302996660283675477312453513523918026903216161 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix92,
    observedExtremizedFinalConsensusLoss92,
    observedExtremizedFinalConsensusPredictor92]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix94 :
    (∑ i ∈ Finset.range 94,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5159478341367843898939398128626214647469082244494548723456484685821230792843760329983712409776161 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix93,
    observedExtremizedFinalConsensusLoss93,
    observedExtremizedFinalConsensusPredictor93]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix95 :
    (∑ i ∈ Finset.range 95,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5170464426080285171578045942981752544867279106357015328637675707113111503631591542726374105776161 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix94,
    observedExtremizedFinalConsensusLoss94,
    observedExtremizedFinalConsensusPredictor94]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix96 :
    (∑ i ∈ Finset.range 96,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((5173049055105380229343338093461648699172153010534827424125926013220429981256069129243050535216161 : Rat) / 1811729888253690226945242330090838397669430030561315197737553183314560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix95,
    observedExtremizedFinalConsensusLoss95,
    observedExtremizedFinalConsensusPredictor95]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix97 :
    (∑ i ∈ Finset.range 97,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((2586534955483682694540611647137660914432193735381146108255397472376676251555388633588124109858393 : Rat) / 905864944126845113472621165045419198834715015280657598868776591657280000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix96,
    observedExtremizedFinalConsensusLoss96,
    observedExtremizedFinalConsensusPredictor96]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix98 :
    (∑ i ∈ Finset.range 98,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((29294250812849713220939561802651881398983159076803732915132990360647553844283745530390535842588499737 : Rat) / 8523283259289485672663892541912349241835833578775707347756318950903347520000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix97,
    observedExtremizedFinalConsensusLoss97,
    observedExtremizedFinalConsensusPredictor97]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix99 :
    (∑ i ∈ Finset.range 99,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((29317000904344234113066789523652834627461274955135808074811484713810207297345768422166876011741219737 : Rat) / 8523283259289485672663892541912349241835833578775707347756318950903347520000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix98,
    observedExtremizedFinalConsensusLoss98,
    observedExtremizedFinalConsensusPredictor98]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix100 :
    (∑ i ∈ Finset.range 100,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((29342274186920271113139619673056723330927804559077838288828237855117874884700233560598435447640099737 : Rat) / 8523283259289485672663892541912349241835833578775707347756318950903347520000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix99,
    observedExtremizedFinalConsensusLoss99,
    observedExtremizedFinalConsensusPredictor99]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix101 :
    (∑ i ∈ Finset.range 101,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1174683572864587210647098596650048821269319530834319729807939255495875483955604050836163908074244481 : Rat) / 340931330371579426906555701676493969673433343151028293910252758036133900800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix100,
    observedExtremizedFinalConsensusLoss100,
    observedExtremizedFinalConsensusPredictor100]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix102 :
    (∑ i ∈ Finset.range 102,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((11992855085412724531118610272848528795978326535292101605538341789608436549947937615215239980233206785881 : Rat) / 3477840501120481733873774712801914984638693533483639626178488384726601922060800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix101,
    observedExtremizedFinalConsensusLoss101,
    observedExtremizedFinalConsensusPredictor101]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix103 :
    (∑ i ∈ Finset.range 103,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((12002587640590535825768911403297060678908055434109977190347537228929025433269530918704179831809104414681 : Rat) / 3477840501120481733873774712801914984638693533483639626178488384726601922060800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix102,
    observedExtremizedFinalConsensusLoss102,
    observedExtremizedFinalConsensusPredictor102]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix104 :
    (∑ i ∈ Finset.range 104,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((127436521538139563239887552964831724853040538309330641244811892906881008646576718395395091196342184735145929 : Rat) / 36896409876387190714666875928115516072031899696727932794127583273564519791143027200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix103,
    observedExtremizedFinalConsensusLoss103,
    observedExtremizedFinalConsensusPredictor103]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix105 :
    (∑ i ∈ Finset.range 105,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((127535656502076920762041174317630290389685075459642530048684799762727913393769764817348836023399110785610729 : Rat) / 36896409876387190714666875928115516072031899696727932794127583273564519791143027200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix104,
    observedExtremizedFinalConsensusLoss104,
    observedExtremizedFinalConsensusPredictor104]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix106 :
    (∑ i ∈ Finset.range 106,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((127632912172820363751575284843876937541099797801390683273418528611058083166616929452256020064165343181241321 : Rat) / 36896409876387190714666875928115516072031899696727932794127583273564519791143027200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix105,
    observedExtremizedFinalConsensusLoss105,
    observedExtremizedFinalConsensusPredictor105]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix107 :
    (∑ i ∈ Finset.range 107,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((127728341486628343367062430496410693757221844242986748537096826987067349964911695392079062432396716638150121 : Rat) / 36896409876387190714666875928115516072031899696727932794127583273564519791143027200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix106,
    observedExtremizedFinalConsensusLoss106,
    observedExtremizedFinalConsensusPredictor106]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix108 :
    (∑ i ∈ Finset.range 108,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1463436100135488265408809516988546533576403393231292626566974694660053646964187340673431666049501371417799052129 : Rat) / 422426996674756946492221062500994543508693219627838102559966700899040187088796518412800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix107,
    observedExtremizedFinalConsensusLoss107,
    observedExtremizedFinalConsensusPredictor107]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix109 :
    (∑ i ∈ Finset.range 109,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1464466837844266720980204338363229794875202024401888501253887306279311431021544683082764891751520235335639552129 : Rat) / 422426996674756946492221062500994543508693219627838102559966700899040187088796518412800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix108,
    observedExtremizedFinalConsensusLoss108,
    observedExtremizedFinalConsensusPredictor108]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix110 :
    (∑ i ∈ Finset.range 110,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((17410019682601411533939895359514085354605559032673880328334285640884402930660522085770027697895780394114216738863849 : Rat) / 5018855147492787281274078443574316171426784142398344496514964373381496462801991435262476800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix109,
    observedExtremizedFinalConsensusLoss109,
    observedExtremizedFinalConsensusPredictor109]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix111 :
    (∑ i ∈ Finset.range 111,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((17421142825677976823132304619757892164325617754779118900014682163161802870946057193157820721140944040034472066178281 : Rat) / 5018855147492787281274078443574316171426784142398344496514964373381496462801991435262476800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix110,
    observedExtremizedFinalConsensusLoss110,
    observedExtremizedFinalConsensusPredictor110]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix112 :
    (∑ i ∈ Finset.range 112,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((17433029579216575904885768949530772911481040711539993808771638147367397570721487097539674363405761237537914619061481 : Rat) / 5018855147492787281274078443574316171426784142398344496514964373381496462801991435262476800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix111,
    observedExtremizedFinalConsensusLoss111,
    observedExtremizedFinalConsensusPredictor111]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix113 :
    (∑ i ∈ Finset.range 113,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((17443808200154653369417952644625868263487930980011258383247884595612897811634895056268315630656787215872367173869681 : Rat) / 5018855147492787281274078443574316171426784142398344496514964373381496462801991435262476800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix112,
    observedExtremizedFinalConsensusLoss112,
    observedExtremizedFinalConsensusPredictor112]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix114 :
    (∑ i ∈ Finset.range 114,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((225335766800774129755449974289318477354470270511590342223134650328534451807676434367101227085122091272657512957026577489 : Rat) / 64085761378335400794588707646000443192948606714284460875999580083708328333518628636866566259200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix113,
    observedExtremizedFinalConsensusLoss113,
    observedExtremizedFinalConsensusPredictor113]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix115 :
    (∑ i ∈ Finset.range 115,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((225498602815152929499257483030280548627709968506943129017879070041747179864645428878902681446796082480174506402212228689 : Rat) / 64085761378335400794588707646000443192948606714284460875999580083708328333518628636866566259200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix114,
    observedExtremizedFinalConsensusLoss114,
    observedExtremizedFinalConsensusPredictor114]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix116 :
    (∑ i ∈ Finset.range 116,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((225658307343510438576504131093563801284444492270364747990746013308585455134124873662683605272738861797006167568066703441 : Rat) / 64085761378335400794588707646000443192948606714284460875999580083708328333518628636866566259200000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix115,
    observedExtremizedFinalConsensusLoss115,
    observedExtremizedFinalConsensusPredictor115]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix117 :
    (∑ i ∈ Finset.range 117,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((7786744117070237737333992965926255241693393810965242166843539856459441167530083908023097584268293085272733665198704229 : Rat) / 2209853840632255199813403711931049765274089886699464168137916554610632011500642366788502284800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix116,
    observedExtremizedFinalConsensusLoss116,
    observedExtremizedFinalConsensusPredictor116]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix118 :
    (∑ i ∈ Finset.range 118,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((7792064413357322254983502780266896843426255007749601316590508631761919521578519836295402642794666664051344088194723429 : Rat) / 2209853840632255199813403711931049765274089886699464168137916554610632011500642366788502284800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix117,
    observedExtremizedFinalConsensusLoss117,
    observedExtremizedFinalConsensusPredictor117]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix119 :
    (∑ i ∈ Finset.range 119,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((7796607095148894955945415160419476833952708155027840967505210218208580111937996905557577930530590201052649823955824229 : Rat) / 2209853840632255199813403711931049765274089886699464168137916554610632011500642366788502284800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix118,
    observedExtremizedFinalConsensusLoss118,
    observedExtremizedFinalConsensusPredictor118]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix120 :
    (∑ i ∈ Finset.range 120,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((9555269319737086790601374815659919537251069871922938411927559536618856895533713475194474346500000064363169072282851429 : Rat) / 2209853840632255199813403711931049765274089886699464168137916554610632011500642366788502284800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix119,
    observedExtremizedFinalConsensusLoss119,
    observedExtremizedFinalConsensusPredictor119]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix121 :
    (∑ i ∈ Finset.range 121,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((9562126327994408676635849648354228000889700331421706690611874809456578152849284941948580199943152583791968117367594637 : Rat) / 2209853840632255199813403711931049765274089886699464168137916554610632011500642366788502284800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix120,
    observedExtremizedFinalConsensusLoss120,
    observedExtremizedFinalConsensusPredictor120]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix122 :
    (∑ i ∈ Finset.range 122,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1157738424382036218367148489863400654072201802883586383949832113930426645584059728416571721523812597249124106216938330277 : Rat) / 267392314716502879177421849143657021598164876290635164344687903107886473391577726381408776460800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix121,
    observedExtremizedFinalConsensusLoss121,
    observedExtremizedFinalConsensusPredictor121]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix123 :
    (∑ i ∈ Finset.range 123,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1158543366529408566707167630962407653235508072473907916946495882404510635775678252936495085897852801250449987943336653477 : Rat) / 267392314716502879177421849143657021598164876290635164344687903107886473391577726381408776460800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix122,
    observedExtremizedFinalConsensusLoss122,
    observedExtremizedFinalConsensusPredictor122]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix124 :
    (∑ i ∈ Finset.range 124,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1274742143232279909186452530141859130344484195756930209638901359928346807943210080664727019160996594443520053986101402277 : Rat) / 267392314716502879177421849143657021598164876290635164344687903107886473391577726381408776460800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix123,
    observedExtremizedFinalConsensusLoss123,
    observedExtremizedFinalConsensusPredictor123]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix125 :
    (∑ i ∈ Finset.range 125,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1275696327134958441413586166164228018044004642764814168052797671964487380769345645721795204802679655913901246502752349477 : Rat) / 267392314716502879177421849143657021598164876290635164344687903107886473391577726381408776460800000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix124,
    observedExtremizedFinalConsensusLoss124,
    observedExtremizedFinalConsensusPredictor124]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix126 :
    (∑ i ∈ Finset.range 126,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((797897065726852430344467625351840271968215957455737804815881332732512510891827446508821219898735535072931527709661216989013 : Rat) / 167120196697814299485888655714785638498853047681646977715429939442429045869736078988380485288000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix125,
    observedExtremizedFinalConsensusLoss125,
    observedExtremizedFinalConsensusPredictor125]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix127 :
    (∑ i ∈ Finset.range 127,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((798410508206447828852519474400434345782823982070271150517925540062064630668315604104511096136202505240341965358668168989013 : Rat) / 167120196697814299485888655714785638498853047681646977715429939442429045869736078988380485288000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix126,
    observedExtremizedFinalConsensusLoss126,
    observedExtremizedFinalConsensusPredictor126]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix128 :
    (∑ i ∈ Finset.range 128,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((12878127309107237599007849742969462249480911560148704032628420495363672130900217815030689940639646205664513441573666854775790677 : Rat) / 2695481652539046836407898128023777563348000806057284103572169493266938080832973218003588847210152000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix127,
    observedExtremizedFinalConsensusLoss127,
    observedExtremizedFinalConsensusPredictor127]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix129 :
    (∑ i ∈ Finset.range 129,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((103189581703126679528448317342173143916759369943030314906202319144007129812050828837758001558060347420464556722079812009649278541 : Rat) / 21563853220312374691263185024190220506784006448458272828577355946135504646663785744028710777681216000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix128,
    observedExtremizedFinalConsensusLoss128,
    observedExtremizedFinalConsensusPredictor128]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix130 :
    (∑ i ∈ Finset.range 130,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((103217000144220855634497435696695614760897143835238034875063768806119968836400950124590211508977952934478698730064374972913278541 : Rat) / 21563853220312374691263185024190220506784006448458272828577355946135504646663785744028710777681216000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix129,
    observedExtremizedFinalConsensusLoss129,
    observedExtremizedFinalConsensusPredictor129]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix131 :
    (∑ i ∈ Finset.range 131,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((103286009554636447743392243200350157511182128405250275506133147250702869180637219767930307021785405847890273719120976008810238541 : Rat) / 21563853220312374691263185024190220506784006448458272828577355946135504646663785744028710777681216000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix130,
    observedExtremizedFinalConsensusLoss130,
    observedExtremizedFinalConsensusPredictor130]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix132 :
    (∑ i ∈ Finset.range 132,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1772965904769280362492648571666571792153038407280750948063854772969135526986420069969327040371578375105161268425274732554398647602101 : Rat) / 370057285113780662076767518200128374116920334661992420011216005391631395241397227153276705655787347776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix131,
    observedExtremizedFinalConsensusLoss131,
    observedExtremizedFinalConsensusPredictor131]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix133 :
    (∑ i ∈ Finset.range 133,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1773054097971842266000319752431955343801309459820801528672944673535282921536112416641227046195752145051793078867550066849364151602101 : Rat) / 370057285113780662076767518200128374116920334661992420011216005391631395241397227153276705655787347776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix132,
    observedExtremizedFinalConsensusLoss132,
    observedExtremizedFinalConsensusPredictor132]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix134 :
    (∑ i ∈ Finset.range 134,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1774313350609858194875096630400913328560617678729018229901810159584744703047873235376828730705067657291071341281264362662070455602101 : Rat) / 370057285113780662076767518200128374116920334661992420011216005391631395241397227153276705655787347776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix133,
    observedExtremizedFinalConsensusLoss133,
    observedExtremizedFinalConsensusPredictor133]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix135 :
    (∑ i ∈ Finset.range 135,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1775578805898067921980350427937944515517627576276879711559014180761116621361244423446955944841400142629354173097321011394705911602101 : Rat) / 370057285113780662076767518200128374116920334661992420011216005391631395241397227153276705655787347776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix134,
    observedExtremizedFinalConsensusLoss134,
    observedExtremizedFinalConsensusPredictor134]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix136 :
    (∑ i ∈ Finset.range 136,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((592277841497217280183609057687825743640525680309611059545112901523299362329301494388815861405165583006939927301818298925080966587367 : Rat) / 123352428371260220692255839400042791372306778220664140003738668463877131747132409051092235218595782592000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix135,
    observedExtremizedFinalConsensusLoss135,
    observedExtremizedFinalConsensusPredictor135]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix137 :
    (∑ i ∈ Finset.range 137,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((592689953059502223161314844162610088692374350171236130505789344112959148428023372783923544644657196535711206146401633358837573587367 : Rat) / 123352428371260220692255839400042791372306778220664140003738668463877131747132409051092235218595782592000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix136,
    observedExtremizedFinalConsensusLoss136,
    observedExtremizedFinalConsensusPredictor136]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix138 :
    (∑ i ∈ Finset.range 138,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((11130965698406346211681664982359080139493362455487599386051765718499354277186728813767599050407569677172211804397103575621676242149291223 : Rat) / 2315201728100183082172949849699403151266825920423645243730171068398509885761928185479950162817824243469248000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix137,
    observedExtremizedFinalConsensusLoss137,
    observedExtremizedFinalConsensusPredictor137]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix139 :
    (∑ i ∈ Finset.range 139,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((11138484375077109577814994165958847337893173919828161947712005204476964149384014794993700232778889741906723286811211572975523062949291223 : Rat) / 2315201728100183082172949849699403151266825920423645243730171068398509885761928185479950162817824243469248000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix138,
    observedExtremizedFinalConsensusLoss138,
    observedExtremizedFinalConsensusPredictor138]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix140 :
    (∑ i ∈ Finset.range 140,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((215350088987379686150404321945069864175527054847314914225346935001189974034733216461106214384495765275722025957779857646393652957046455719583 : Rat) / 44732012588623637330663564046042168285626343608505249754110635212527609502806214471658117095803182208069340608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix139,
    observedExtremizedFinalConsensusLoss139,
    observedExtremizedFinalConsensusPredictor139]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix141 :
    (∑ i ∈ Finset.range 141,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((215491479647922719591350958513403046386739180135022468386084129905747265404138739089396177791870296776447747165162397387361078562383987719583 : Rat) / 44732012588623637330663564046042168285626343608505249754110635212527609502806214471658117095803182208069340608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix140,
    observedExtremizedFinalConsensusLoss140,
    observedExtremizedFinalConsensusPredictor140]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix142 :
    (∑ i ∈ Finset.range 142,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((215630871879029980566279487095432641041925421050422501661595875800285915916705926027401473440204928707146612195326764316738954014555187719583 : Rat) / 44732012588623637330663564046042168285626343608505249754110635212527609502806214471658117095803182208069340608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix141,
    observedExtremizedFinalConsensusLoss141,
    observedExtremizedFinalConsensusPredictor141]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix143 :
    (∑ i ∈ Finset.range 143,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((215768307752202141617784846981334762215291700342183464841046828990591555216465311244346686829638613363674292004129471067530540101869987719583 : Rat) / 44732012588623637330663564046042168285626343608505249754110635212527609502806214471658117095803182208069340608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix142,
    observedExtremizedFinalConsensusLoss142,
    observedExtremizedFinalConsensusPredictor142]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix144 :
    (∑ i ∈ Finset.range 144,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((215903828166239182815034300584901213941036609904463677152184245007478586897249126761706131437420940979412183131553686379915573202002787719583 : Rat) / 44732012588623637330663564046042168285626343608505249754110635212527609502806214471658117095803182208069340608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix143,
    observedExtremizedFinalConsensusLoss143,
    observedExtremizedFinalConsensusPredictor143]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix145 :
    (∑ i ∈ Finset.range 145,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((216037472887817281553583397649876636941603626476563795861214386796122631594410982641069715676644552930329627945630546860382468546554081469583 : Rat) / 44732012588623637330663564046042168285626343608505249754110635212527609502806214471658117095803182208069340608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix144,
    observedExtremizedFinalConsensusLoss144,
    observedExtremizedFinalConsensusPredictor144]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix146 :
    (∑ i ∈ Finset.range 146,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((6268902279044472612930800025228176178369867342905296372386924818757065795011846872232895711532054271203926544780471148655619806294385034617907 : Rat) / 1297228365070085482589243357335222880283163964646652242869208421163300675581380219678085395778292284034010877632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix145,
    observedExtremizedFinalConsensusLoss145,
    observedExtremizedFinalConsensusPredictor145]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix147 :
    (∑ i ∈ Finset.range 147,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((6272672566449395283535672796386473752529941513805336158858293727135422934746599667495983351557774255221552996859584516074631524787189834617907 : Rat) / 1297228365070085482589243357335222880283163964646652242869208421163300675581380219678085395778292284034010877632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix146,
    observedExtremizedFinalConsensusLoss146,
    observedExtremizedFinalConsensusPredictor146]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix148 :
    (∑ i ∈ Finset.range 148,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((6276391731904683896919608563428459549688354259740143326632077782436133786270778971666836983599435006728782644345279390428079337799945034617907 : Rat) / 1297228365070085482589243357335222880283163964646652242869208421163300675581380219678085395778292284034010877632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix147,
    observedExtremizedFinalConsensusLoss147,
    observedExtremizedFinalConsensusPredictor147]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix149 :
    (∑ i ∈ Finset.range 149,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((6280060808161227525782531682037401801824774138616387304372385472857657744935223392038822745779322113162298232937243439912358637991354234617907 : Rat) / 1297228365070085482589243357335222880283163964646652242869208421163300675581380219678085395778292284034010877632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix148,
    observedExtremizedFinalConsensusLoss148,
    observedExtremizedFinalConsensusPredictor148]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix150 :
    (∑ i ∈ Finset.range 150,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((139501545433162983728300870168098927949215887043930832858751462407839284478440116721747629311283820742642746918154229887959940285943893048704153307 : Rat) / 28799766932920967798963791776199283165166523179120326443939296158246438298582222257073173871673866997839075494308032000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix149,
    observedExtremizedFinalConsensusLoss149,
    observedExtremizedFinalConsensusPredictor149]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix151 :
    (∑ i ∈ Finset.range 151,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((139571029153326526923333907572025480829123765537143508823867411427680319016548765900856070741716585919370134332812835405368641028936414312059724507 : Rat) / 28799766932920967798963791776199283165166523179120326443939296158246438298582222257073173871673866997839075494308032000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix150,
    observedExtremizedFinalConsensusLoss150,
    observedExtremizedFinalConsensusPredictor150]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix152 :
    (∑ i ∈ Finset.range 152,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3183295948009783099488282333244408903743795787308217396077258611875189105642604578764027183070729137610675778360329263684742508064286701361483186484107 : Rat) / 656663485837530986784173416289119855448961895007122563248259891704177039645973249683525437448035841417728760345717437632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix151,
    observedExtremizedFinalConsensusLoss151,
    observedExtremizedFinalConsensusPredictor151]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix153 :
    (∑ i ∈ Finset.range 153,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3185065097068339280506261998449256747617553755188504933337196501709417048949569122307157011670901773515221256863540724166164787948936279711127394484107 : Rat) / 656663485837530986784173416289119855448961895007122563248259891704177039645973249683525437448035841417728760345717437632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix152,
    observedExtremizedFinalConsensusLoss152,
    observedExtremizedFinalConsensusPredictor152]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix154 :
    (∑ i ∈ Finset.range 154,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3186807897801705937467838841610692988115793238260409564653377712729230478616869038704813235094242278972933932010785559281678550703099769385758242484107 : Rat) / 656663485837530986784173416289119855448961895007122563248259891704177039645973249683525437448035841417728760345717437632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix153,
    observedExtremizedFinalConsensusLoss153,
    observedExtremizedFinalConsensusPredictor153]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix155 :
    (∑ i ∈ Finset.range 155,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3188528138245599514496576922297404952773546993498654442140326859666437957748334030396191820611065431792110690845405830205066207656726566897709394484107 : Rat) / 656663485837530986784173416289119855448961895007122563248259891704177039645973249683525437448035841417728760345717437632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix154,
    observedExtremizedFinalConsensusLoss154,
    observedExtremizedFinalConsensusPredictor154]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix156 :
    (∑ i ∈ Finset.range 156,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3190226253640703783916495853476013109020093842998351237748255516014525890113862594098698981240284074550054333406148987134059409417900890718455846964107 : Rat) / 656663485837530986784173416289119855448961895007122563248259891704177039645973249683525437448035841417728760345717437632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix155,
    observedExtremizedFinalConsensusLoss155,
    observedExtremizedFinalConsensusPredictor155]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix157 :
    (∑ i ∈ Finset.range 157,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((3191902668103531696178722691147202332960892990731348259217703493034694059701380006284462234614584612529163308279663712036223350587863626163616658964107 : Rat) / 656663485837530986784173416289119855448961895007122563248259891704177039645973249683525437448035841417728760345717437632000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix156,
    observedExtremizedFinalConsensusLoss156,
    observedExtremizedFinalConsensusPredictor156]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix158 :
    (∑ i ∈ Finset.range 158,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((78718085305146418020226678009956753630392501753706055767937164202746440345050104442537657729521046913769608939535205666485539722519022317838288062838273443 : Rat) / 16186098262409301293243090538110515316961461750030564061506358070616259850233594631449218507656635455105596213761589120191168000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix157,
    observedExtremizedFinalConsensusLoss157,
    observedExtremizedFinalConsensusPredictor157]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix159 :
    (∑ i ∈ Finset.range 159,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((78758445958345052282696689735472854279480276690815171924210409407902935063712477053836323365099003613730297678814896411070206424680448612210185164150273443 : Rat) / 16186098262409301293243090538110515316961461750030564061506358070616259850233594631449218507656635455105596213761589120191168000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix158,
    observedExtremizedFinalConsensusLoss158,
    observedExtremizedFinalConsensusPredictor158]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix160 :
    (∑ i ∈ Finset.range 160,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((78798300526853050610622854551571265600386380623808011437093811698220831276547707854376645699127250560362892658735714406711661254503550784303853897078273443 : Rat) / 16186098262409301293243090538110515316961461750030564061506358070616259850233594631449218507656635455105596213761589120191168000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix159,
    observedExtremizedFinalConsensusLoss159,
    observedExtremizedFinalConsensusPredictor159]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix161 :
    (∑ i ∈ Finset.range 161,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((78837580739412044535376593209859778876138333014939631078460407978410245880887990857245250029420826604772765326048680120610160777185127031159584480739553443 : Rat) / 16186098262409301293243090538110515316961461750030564061506358070616259850233594631449218507656635455105596213761589120191168000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix160,
    observedExtremizedFinalConsensusLoss160,
    observedExtremizedFinalConsensusPredictor160]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix162 :
    (∑ i ∈ Finset.range 162,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((78876451762503039989451100720889617772123543973888645118981410131437556989332517866541577658940971782862916625357330073619114687493028167178060816547553443 : Rat) / 16186098262409301293243090538110515316961461750030564061506358070616259850233594631449218507656635455105596213761589120191168000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix161,
    observedExtremizedFinalConsensusLoss161,
    observedExtremizedFinalConsensusPredictor161]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix163 :
    (∑ i ∈ Finset.range 163,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((2130698725376460141592522389568455361245430548967763067005498807009034964074986888569985451922940149440114947194998899118924879627980734358845370546127942961 : Rat) / 437024653085051134917563444528983913557959467250825229660671667906639015956307055049128899706729157287851097771562906245161536000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix162,
    observedExtremizedFinalConsensusLoss162,
    observedExtremizedFinalConsensusPredictor162]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix164 :
    (∑ i ∈ Finset.range 164,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((56637739316810326387015600375217291079727329902838730922377140114399250710513020414363115629830239111772016109888749587895000493162022754267664509327543652530809 : Rat) / 11611308007816723603624743157690573599321425085387175526854385544611492014943122145600305736308086979980915816692654856027696849984000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix163,
    observedExtremizedFinalConsensusLoss163,
    observedExtremizedFinalConsensusPredictor163]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix165 :
    (∑ i ∈ Finset.range 165,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((56664613443720692065136163355472788275987829462754401766221041667058630459430134811554683783371884924227250702645683872944102883774785897218729236402528756530809 : Rat) / 11611308007816723603624743157690573599321425085387175526854385544611492014943122145600305736308086979980915816692654856027696849984000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix164,
    observedExtremizedFinalConsensusLoss164,
    observedExtremizedFinalConsensusPredictor164]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix166 :
    (∑ i ∈ Finset.range 166,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((56691108739546956116069183992098723178774750488844731178723042243859693460089676006869206819327082346454251385490541570140715724048953628311478547407675710770809 : Rat) / 11611308007816723603624743157690573599321425085387175526854385544611492014943122145600305736308086979980915816692654856027696849984000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix165,
    observedExtremizedFinalConsensusLoss165,
    observedExtremizedFinalConsensusPredictor165]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix167 :
    (∑ i ∈ Finset.range 167,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((56717339522088127205764756905063009426134838597911515090249929624890138534840134879327454013189440763687999709745610125493890149380282244696100071610858574770809 : Rat) / 11611308007816723603624743157690573599321425085387175526854385544611492014943122145600305736308086979980915816692654856027696849984000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix166,
    observedExtremizedFinalConsensusLoss166,
    observedExtremizedFinalConsensusPredictor166]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix168 :
    (∑ i ∈ Finset.range 168,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1582512697375220290189224512514946141717729101590598541818015195980236018077980166339022824647911462003787792728267989901211176840496782875424165618098141792167092201 : Rat) / 323827769030000604581490461924832407111475224206362938268441958453669900804748733518646926679896237784687761211741451279756437449203776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix167,
    observedExtremizedFinalConsensusLoss167,
    observedExtremizedFinalConsensusPredictor167]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix169 :
    (∑ i ∈ Finset.range 169,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((1583226933483124027953660613610183455405716211953262516167159455048558811679092752320610653121911258693827517264459265724814579786163265930499851423667045325816092201 : Rat) / 323827769030000604581490461924832407111475224206362938268441958453669900804748733518646926679896237784687761211741451279756437449203776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix168,
    observedExtremizedFinalConsensusLoss168,
    observedExtremizedFinalConsensusPredictor168]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix170 :
    (∑ i ∈ Finset.range 170,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((267684633414917044124544055045162293558416620902206856427695199784533909745351300152504708489142471723870348555619429924330246497107099739570783507027995354345223581969 : Rat) / 54726892966070102174271888065296676801839312890875336567366690978670213236002535964651330608902464185612231644784305266278837928915438144000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix169,
    observedExtremizedFinalConsensusLoss169,
    observedExtremizedFinalConsensusPredictor169]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix171 :
    (∑ i ∈ Finset.range 171,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((267802515884975912325171118139478012316843176137017061757560661341025047703656783713743206522833778791024885590820093389204628267377167151306115354564592860691136541969 : Rat) / 54726892966070102174271888065296676801839312890875336567366690978670213236002535964651330608902464185612231644784305266278837928915438144000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix170,
    observedExtremizedFinalConsensusLoss170,
    observedExtremizedFinalConsensusPredictor170]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix172 :
    (∑ i ∈ Finset.range 172,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((267919023644105261218783584314565193744240578629613584928215284609127844700853475855591727201800940455836831841539944766889031439662825924916836273610031386507520541969 : Rat) / 54726892966070102174271888065296676801839312890875336567366690978670213236002535964651330608902464185612231644784305266278837928915438144000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix171,
    observedExtremizedFinalConsensusLoss171,
    observedExtremizedFinalConsensusPredictor171]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix173 :
    (∑ i ∈ Finset.range 173,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((268034180600051086360688739919815473358847374407264170854158762130172797614422583309613921400478562624602587666218797326883272690366075931648552417262264618436836541969 : Rat) / 54726892966070102174271888065296676801839312890875336567366690978670213236002535964651330608902464185612231644784305266278837928915438144000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix172,
    observedExtremizedFinalConsensusLoss172,
    observedExtremizedFinalConsensusPredictor172]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix174 :
    (∑ i ∈ Finset.range 174,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((8025401794563630254687175420485881574275470514921024303527229430776535546797081970793227646768601675032496966579561559331159101510771234757460615690049985698592965408590201 : Rat) / 1637921179581512087973783337906264240002248795511007948124717694300620811940319898886049673793841850611188480896749472314459340374510148211776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix173,
    observedExtremizedFinalConsensusLoss173,
    observedExtremizedFinalConsensusPredictor173]
  norm_num [ratToReal]

theorem observedExtremizedFinalConsensusQuadraticPrefix175 :
    (∑ i ∈ Finset.range 175,
      (observedTrajectoryScore
          (monitorBrierScore extremizedFinalConsensus) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore extremizedFinalConsensus)) i replayPath) ^ 2) =
      ratToReal ((8028769551813621169546562295634794962445486631313352912348639267905286122958867121601606313735672359213098407158780973477100218265617690519529349485672580941644734384590201 : Rat) / 1637921179581512087973783337906264240002248795511007948124717694300620811940319898886049673793841850611188480896749472314459340374510148211776000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedExtremizedFinalConsensusQuadraticPrefix174,
    observedExtremizedFinalConsensusLoss174,
    observedExtremizedFinalConsensusPredictor174]
  norm_num [ratToReal]

end

end FormalSLT.Applications.GJPBrierMonitorReplayPathData
