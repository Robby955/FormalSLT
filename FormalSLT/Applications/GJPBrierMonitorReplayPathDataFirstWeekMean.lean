/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathDataConstantTrainBaseRate
import Mathlib.Tactic

/-!
# Generated GJP path calculation: first-week-mean

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

theorem observedFirstWeekMeanLoss0 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 0 replayPath =
      ratToReal ((61945734321 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss1 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 1 replayPath =
      ratToReal ((1754520769 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss2 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 2 replayPath =
      ratToReal ((102146077609 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss3 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 3 replayPath =
      ratToReal ((97980894361 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss4 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 4 replayPath =
      ratToReal ((68666533849 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss5 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 5 replayPath =
      ratToReal ((5311057129 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss6 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 6 replayPath =
      ratToReal ((2493241 : Rat) / 39062500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss7 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 7 replayPath =
      ratToReal ((2593151929 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss8 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 8 replayPath =
      ratToReal ((174464100721 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss9 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 9 replayPath =
      ratToReal ((68897325289 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss10 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 10 replayPath =
      ratToReal ((66091668889 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss11 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 11 replayPath =
      ratToReal ((20331052569 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss12 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 12 replayPath =
      ratToReal ((10751841 : Rat) / 156250000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss13 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 13 replayPath =
      ratToReal ((67338693009 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss14 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 14 replayPath =
      ratToReal ((269889601081 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss15 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 15 replayPath =
      ratToReal ((119827437921 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss16 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 16 replayPath =
      ratToReal ((3657467529 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss17 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 17 replayPath =
      ratToReal ((1645032481 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss18 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 18 replayPath =
      ratToReal ((14203157329 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss19 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 19 replayPath =
      ratToReal ((71690598001 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss20 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 20 replayPath =
      ratToReal ((218222582449 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss21 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 21 replayPath =
      ratToReal ((149251641561 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss22 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 22 replayPath =
      ratToReal ((16575790009 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss23 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 23 replayPath =
      ratToReal ((192265587361 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss24 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 24 replayPath =
      ratToReal ((441 : Rat) / 6400) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss25 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 25 replayPath =
      ratToReal ((19405325809 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss26 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 26 replayPath =
      ratToReal ((2197078129 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss27 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 27 replayPath =
      ratToReal ((11566357209 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss28 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 28 replayPath =
      ratToReal ((128979384769 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss29 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 29 replayPath =
      ratToReal ((112783803889 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss30 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 30 replayPath =
      ratToReal ((56348789641 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss31 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 31 replayPath =
      ratToReal ((121374289 : Rat) / 976562500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss32 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 32 replayPath =
      ratToReal ((186440013369 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss33 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 33 replayPath =
      ratToReal ((16720817481 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss34 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 34 replayPath =
      ratToReal ((43810257481 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss35 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 35 replayPath =
      ratToReal ((286997481 : Rat) / 2500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss36 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 36 replayPath =
      ratToReal ((3324560281 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss37 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 37 replayPath =
      ratToReal ((131713103929 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss38 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 38 replayPath =
      ratToReal ((9624198609 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss39 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 39 replayPath =
      ratToReal ((111301637161 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss40 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 40 replayPath =
      ratToReal ((233508961 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss41 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 41 replayPath =
      ratToReal ((2429799849 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss42 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 42 replayPath =
      ratToReal ((2789001721 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss43 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 43 replayPath =
      ratToReal ((98233976929 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss44 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 44 replayPath =
      ratToReal ((5273228689 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss45 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 45 replayPath =
      ratToReal ((252587449 : Rat) / 2500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss46 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 46 replayPath =
      ratToReal ((47114609481 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss47 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 47 replayPath =
      ratToReal ((21188586969 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss48 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 48 replayPath =
      ratToReal ((322575153849 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss49 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 49 replayPath =
      ratToReal ((112271234761 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss50 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 50 replayPath =
      ratToReal ((4745694321 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss51 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 51 replayPath =
      ratToReal ((53458526521 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss52 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 52 replayPath =
      ratToReal ((1004826601 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss53 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 53 replayPath =
      ratToReal ((164713410801 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss54 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 54 replayPath =
      ratToReal ((53699256361 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss55 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 55 replayPath =
      ratToReal ((2202706489 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss56 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 56 replayPath =
      ratToReal ((34283114649 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss57 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 57 replayPath =
      ratToReal ((225246109201 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss58 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 58 replayPath =
      ratToReal ((120846049 : Rat) / 3906250000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss59 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 59 replayPath =
      ratToReal ((8958811801 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss60 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 60 replayPath =
      ratToReal ((37790971201 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss61 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 61 replayPath =
      ratToReal ((297560431081 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss62 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 62 replayPath =
      ratToReal ((53277410761 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss63 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 63 replayPath =
      ratToReal ((26026400929 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss64 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 64 replayPath =
      ratToReal ((97435749609 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss65 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 65 replayPath =
      ratToReal ((17049308329 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss66 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 66 replayPath =
      ratToReal ((10260271849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss67 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 67 replayPath =
      ratToReal ((5358679209 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss68 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 68 replayPath =
      ratToReal ((84070422601 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss69 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 69 replayPath =
      ratToReal ((44612621089 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss70 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 70 replayPath =
      ratToReal ((4783520569 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss71 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 71 replayPath =
      ratToReal ((172431732001 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss72 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 72 replayPath =
      ratToReal ((12370555729 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss73 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 73 replayPath =
      ratToReal ((11833305961 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss74 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 74 replayPath =
      ratToReal ((20575894249 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss75 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 75 replayPath =
      ratToReal ((118493604441 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss76 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 76 replayPath =
      ratToReal ((109561 : Rat) / 9765625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss77 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 77 replayPath =
      ratToReal ((77920814449 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss78 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 78 replayPath =
      ratToReal ((134298062089 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss79 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 79 replayPath =
      ratToReal ((162951890929 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss80 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 80 replayPath =
      ratToReal ((56909442249 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss81 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 81 replayPath =
      ratToReal ((2580538401 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss82 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 82 replayPath =
      ratToReal ((329231521369 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss83 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 83 replayPath =
      ratToReal ((113131995201 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss84 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 84 replayPath =
      ratToReal ((17258339641 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss85 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 85 replayPath =
      ratToReal ((114181140649 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss86 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 86 replayPath =
      ratToReal ((24970009 : Rat) / 100000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss87 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 87 replayPath =
      ratToReal ((63792169 : Rat) / 976562500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss88 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 88 replayPath =
      ratToReal ((127694019649 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss89 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 89 replayPath =
      ratToReal ((8937244369 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss90 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 90 replayPath =
      ratToReal ((2084196409 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss91 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 91 replayPath =
      ratToReal ((330230667649 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss92 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 92 replayPath =
      ratToReal ((6302930881 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss93 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 93 replayPath =
      ratToReal ((280462009 : Rat) / 976562500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss94 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 94 replayPath =
      ratToReal ((15460684281 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss95 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 95 replayPath =
      ratToReal ((4794039121 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss96 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 96 replayPath =
      ratToReal ((40642156801 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss97 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 97 replayPath =
      ratToReal ((123892032289 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss98 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 98 replayPath =
      ratToReal ((28249877929 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss99 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 99 replayPath =
      ratToReal ((159561101401 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss100 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 100 replayPath =
      ratToReal ((2828856969 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss101 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 101 replayPath =
      ratToReal ((223480271169 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss102 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 102 replayPath =
      ratToReal ((349951849 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss103 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 103 replayPath =
      ratToReal ((112652195769 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss104 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 104 replayPath =
      ratToReal ((781456 : Rat) / 9765625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss105 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 105 replayPath =
      ratToReal ((156992665729 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss106 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 106 replayPath =
      ratToReal ((2345174329 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss107 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 107 replayPath =
      ratToReal ((7619718681 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss108 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 108 replayPath =
      ratToReal ((120098981809 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss109 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 109 replayPath =
      ratToReal ((102619637649 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss110 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 110 replayPath =
      ratToReal ((88303471281 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss111 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 111 replayPath =
      ratToReal ((1121111289 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss112 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 112 replayPath =
      ratToReal ((39271745241 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss113 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 113 replayPath =
      ratToReal ((260443853569 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss114 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 114 replayPath =
      ratToReal ((38565497161 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss115 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 115 replayPath =
      ratToReal ((13995081 : Rat) / 64000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss116 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 116 replayPath =
      ratToReal ((126181958841 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss117 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 117 replayPath =
      ratToReal ((5007968289 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss118 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 118 replayPath =
      ratToReal ((17872213969 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss119 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 119 replayPath =
      ratToReal ((105021504 : Rat) / 244140625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss120 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 120 replayPath =
      ratToReal ((6996151449 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss121 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 121 replayPath =
      ratToReal ((421420390561 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss122 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 122 replayPath =
      ratToReal ((109910151729 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss123 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 123 replayPath =
      ratToReal ((90353746921 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss124 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 124 replayPath =
      ratToReal ((49067123121 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss125 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 125 replayPath =
      ratToReal ((90437931441 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss126 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 126 replayPath =
      ratToReal ((155027401 : Rat) / 400000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss127 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 127 replayPath =
      ratToReal ((8781376681 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss128 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 128 replayPath =
      ratToReal ((467416975041 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss129 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 129 replayPath =
      ratToReal ((266193051721 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss130 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 130 replayPath =
      ratToReal ((133748924089 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss131 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 131 replayPath =
      ratToReal ((305710573921 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss132 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 132 replayPath =
      ratToReal ((279351360369 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss133 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 133 replayPath =
      ratToReal ((26713614249 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss134 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 134 replayPath =
      ratToReal ((35218902889 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss135 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 135 replayPath =
      ratToReal ((275327649 : Rat) / 2500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss136 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 136 replayPath =
      ratToReal ((4642105689 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss137 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 137 replayPath =
      ratToReal ((236062854769 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss138 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 138 replayPath =
      ratToReal ((5455447321 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss139 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 139 replayPath =
      ratToReal ((4612175569 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss140 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 140 replayPath =
      ratToReal ((68707521 : Rat) / 976562500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss141 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 141 replayPath =
      ratToReal ((13088046409 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss142 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 142 replayPath =
      ratToReal ((2094801361 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss143 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 143 replayPath =
      ratToReal ((3660129001 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss144 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 144 replayPath =
      ratToReal ((3464852769 : Rat) / 62500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss145 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 145 replayPath =
      ratToReal ((262083721 : Rat) / 1600000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss146 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 146 replayPath =
      ratToReal ((34797544681 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss147 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 147 replayPath =
      ratToReal ((66532527721 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss148 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 148 replayPath =
      ratToReal ((85865994841 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss149 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 149 replayPath =
      ratToReal ((43155492121 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss150 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 150 replayPath =
      ratToReal ((234417683889 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss151 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 151 replayPath =
      ratToReal ((236144486809 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss152 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 152 replayPath =
      ratToReal ((1015888129 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss153 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 153 replayPath =
      ratToReal ((22719231441 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss154 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 154 replayPath =
      ratToReal ((94409322121 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss155 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 155 replayPath =
      ratToReal ((46811216881 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss156 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 156 replayPath =
      ratToReal ((2098464481 : Rat) / 15625000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss157 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 157 replayPath =
      ratToReal ((6561 : Rat) / 160000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss158 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 158 replayPath =
      ratToReal ((3694329961 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss159 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 159 replayPath =
      ratToReal ((92059448569 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss160 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 160 replayPath =
      ratToReal ((44373843801 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss161 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 161 replayPath =
      ratToReal ((132522937369 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss162 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 162 replayPath =
      ratToReal ((745999969 : Rat) / 2500000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss163 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 163 replayPath =
      ratToReal ((89271281089 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss164 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 164 replayPath =
      ratToReal ((41141225889 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss165 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 165 replayPath =
      ratToReal ((1076430481 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss166 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 166 replayPath =
      ratToReal ((4460544 : Rat) / 244140625) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss167 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 167 replayPath =
      ratToReal ((23697831481 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss168 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 168 replayPath =
      ratToReal ((7241481 : Rat) / 39062500) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss169 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 169 replayPath =
      ratToReal ((6863625409 : Rat) / 40000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss170 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 170 replayPath =
      ratToReal ((4404578689 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss171 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 171 replayPath =
      ratToReal ((32796123409 : Rat) / 250000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss172 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 172 replayPath =
      ratToReal ((1127817889 : Rat) / 10000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss173 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 173 replayPath =
      ratToReal ((147146658409 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLoss174 :
    observedTrajectoryScore
        (monitorBrierScore firstWeekMean) 174 replayPath =
      ratToReal ((202034967289 : Rat) / 1000000000000) := by
  norm_num [observedTrajectoryScore, monitorBrierScore,
    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,
    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,
    firstWeekMeanPredictionsQ]

theorem observedFirstWeekMeanLossPrefix0 :
    (∑ i ∈ Finset.range 0, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) = ratToReal 0 := by
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix1 :
    (∑ i ∈ Finset.range 1, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((61945734321 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix0,
    observedFirstWeekMeanLoss0]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix2 :
    (∑ i ∈ Finset.range 2, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((237397811221 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix1,
    observedFirstWeekMeanLoss1]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix3 :
    (∑ i ∈ Finset.range 3, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((33954388883 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix2,
    observedFirstWeekMeanLoss2]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix4 :
    (∑ i ∈ Finset.range 4, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((437524783191 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix3,
    observedFirstWeekMeanLoss3]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix5 :
    (∑ i ∈ Finset.range 5, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((6327391463 : Rat) / 12500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix4,
    observedFirstWeekMeanLoss4]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix6 :
    (∑ i ∈ Finset.range 6, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((9237003611 : Rat) / 15625000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix5,
    observedFirstWeekMeanLoss5]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix7 :
    (∑ i ∈ Finset.range 7, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((10234300011 : Rat) / 15625000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix6,
    observedFirstWeekMeanLoss6]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix8 :
    (∑ i ∈ Finset.range 8, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((719823998929 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix7,
    observedFirstWeekMeanLoss7]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix9 :
    (∑ i ∈ Finset.range 9, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((17885761993 : Rat) / 20000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix8,
    observedFirstWeekMeanLoss8]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix10 :
    (∑ i ∈ Finset.range 10, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((963185424939 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix9,
    observedFirstWeekMeanLoss9]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix11 :
    (∑ i ∈ Finset.range 11, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((257319273457 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix10,
    observedFirstWeekMeanLoss10]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix12 :
    (∑ i ∈ Finset.range 12, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1537553408053 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix11,
    observedFirstWeekMeanLoss11]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix13 :
    (∑ i ∈ Finset.range 13, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1606365190453 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix12,
    observedFirstWeekMeanLoss12]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix14 :
    (∑ i ∈ Finset.range 14, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((836851941731 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix13,
    observedFirstWeekMeanLoss13]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix15 :
    (∑ i ∈ Finset.range 15, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1943593484543 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix14,
    observedFirstWeekMeanLoss14]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix16 :
    (∑ i ∈ Finset.range 16, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((64481903827 : Rat) / 31250000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix15,
    observedFirstWeekMeanLoss15]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix17 :
    (∑ i ∈ Finset.range 17, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((132621275183 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix16,
    observedFirstWeekMeanLoss16]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix18 :
    (∑ i ∈ Finset.range 18, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((571610912757 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix17,
    observedFirstWeekMeanLoss17]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix19 :
    (∑ i ∈ Finset.range 19, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((292907035043 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix18,
    observedFirstWeekMeanLoss18]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix20 :
    (∑ i ∈ Finset.range 20, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((657504668087 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix19,
    observedFirstWeekMeanLoss19]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix21 :
    (∑ i ∈ Finset.range 21, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2848241254797 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix20,
    observedFirstWeekMeanLoss20]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix22 :
    (∑ i ∈ Finset.range 22, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1498746448179 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix21,
    observedFirstWeekMeanLoss21]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix23 :
    (∑ i ∈ Finset.range 23, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3014068686367 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix22,
    observedFirstWeekMeanLoss22]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix24 :
    (∑ i ∈ Finset.range 24, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((50098973027 : Rat) / 15625000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix23,
    observedFirstWeekMeanLoss23]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix25 :
    (∑ i ∈ Finset.range 25, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((204702532733 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix24,
    observedFirstWeekMeanLoss24]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix26 :
    (∑ i ∈ Finset.range 26, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((838215456741 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix25,
    observedFirstWeekMeanLoss25]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix27 :
    (∑ i ∈ Finset.range 27, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((446571204983 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix26,
    observedFirstWeekMeanLoss26]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix28 :
    (∑ i ∈ Finset.range 28, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((36188350687 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix27,
    observedFirstWeekMeanLoss27]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix29 :
    (∑ i ∈ Finset.range 29, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3747814453469 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix28,
    observedFirstWeekMeanLoss28]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix30 :
    (∑ i ∈ Finset.range 30, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1930299128679 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix29,
    observedFirstWeekMeanLoss29]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix31 :
    (∑ i ∈ Finset.range 31, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2042996707961 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix30,
    observedFirstWeekMeanLoss30]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix32 :
    (∑ i ∈ Finset.range 32, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2105140343929 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix31,
    observedFirstWeekMeanLoss31]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix33 :
    (∑ i ∈ Finset.range 33, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4396720701227 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix32,
    observedFirstWeekMeanLoss32]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix34 :
    (∑ i ∈ Finset.range 34, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4664253780923 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix33,
    observedFirstWeekMeanLoss33]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix35 :
    (∑ i ∈ Finset.range 35, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1177016009601 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix34,
    observedFirstWeekMeanLoss34]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix36 :
    (∑ i ∈ Finset.range 36, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1205715757701 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix35,
    observedFirstWeekMeanLoss35]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix37 :
    (∑ i ∈ Finset.range 37, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((48760559953 : Rat) / 10000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix36,
    observedFirstWeekMeanLoss36]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix38 :
    (∑ i ∈ Finset.range 38, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5007769099229 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix37,
    observedFirstWeekMeanLoss37]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix39 :
    (∑ i ∈ Finset.range 39, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2624187032227 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix38,
    observedFirstWeekMeanLoss38]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix40 :
    (∑ i ∈ Finset.range 40, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1071935140323 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix39,
    observedFirstWeekMeanLoss39]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix41 :
    (∑ i ∈ Finset.range 41, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1076605319543 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix40,
    observedFirstWeekMeanLoss40]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix42 :
    (∑ i ∈ Finset.range 42, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5392745797111 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix41,
    observedFirstWeekMeanLoss41]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix43 :
    (∑ i ∈ Finset.range 43, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5437369824647 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix42,
    observedFirstWeekMeanLoss42]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix44 :
    (∑ i ∈ Finset.range 44, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((691950475197 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix43,
    observedFirstWeekMeanLoss43]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix45 :
    (∑ i ∈ Finset.range 45, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5667434518801 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix44,
    observedFirstWeekMeanLoss44]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix46 :
    (∑ i ∈ Finset.range 46, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5768469498401 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix45,
    observedFirstWeekMeanLoss45]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix47 :
    (∑ i ∈ Finset.range 47, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2907792053941 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix46,
    observedFirstWeekMeanLoss46]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix48 :
    (∑ i ∈ Finset.range 48, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2950169227879 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix47,
    observedFirstWeekMeanLoss47]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix49 :
    (∑ i ∈ Finset.range 49, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((6222913609607 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix48,
    observedFirstWeekMeanLoss48]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix50 :
    (∑ i ∈ Finset.range 50, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((395949052773 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix49,
    observedFirstWeekMeanLoss49]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix51 :
    (∑ i ∈ Finset.range 51, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1588541905413 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix50,
    observedFirstWeekMeanLoss50]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix52 :
    (∑ i ∈ Finset.range 52, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((821000215967 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix51,
    observedFirstWeekMeanLoss51]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix53 :
    (∑ i ∈ Finset.range 53, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((33161553151 : Rat) / 5000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix52,
    observedFirstWeekMeanLoss52]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix54 :
    (∑ i ∈ Finset.range 54, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((6797024041001 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix53,
    observedFirstWeekMeanLoss53]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix55 :
    (∑ i ∈ Finset.range 55, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3425361648681 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix54,
    observedFirstWeekMeanLoss54]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix56 :
    (∑ i ∈ Finset.range 56, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3442983300593 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix55,
    observedFirstWeekMeanLoss55]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix57 :
    (∑ i ∈ Finset.range 57, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1384049943167 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix56,
    observedFirstWeekMeanLoss56]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix58 :
    (∑ i ∈ Finset.range 58, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1786373956259 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix57,
    observedFirstWeekMeanLoss57]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix59 :
    (∑ i ∈ Finset.range 59, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((358821620679 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix58,
    observedFirstWeekMeanLoss58]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix60 :
    (∑ i ∈ Finset.range 60, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((450766728799 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix59,
    observedFirstWeekMeanLoss59]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix61 :
    (∑ i ∈ Finset.range 61, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1450011726397 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix60,
    observedFirstWeekMeanLoss60]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix62 :
    (∑ i ∈ Finset.range 62, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3773809531533 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix61,
    observedFirstWeekMeanLoss61]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix63 :
    (∑ i ∈ Finset.range 63, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((7600896473827 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix62,
    observedFirstWeekMeanLoss62]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix64 :
    (∑ i ∈ Finset.range 64, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1906730718689 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix63,
    observedFirstWeekMeanLoss63]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix65 :
    (∑ i ∈ Finset.range 65, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1544871724873 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix64,
    observedFirstWeekMeanLoss64]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix66 :
    (∑ i ∈ Finset.range 66, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((7997147557629 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix65,
    observedFirstWeekMeanLoss65]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix67 :
    (∑ i ∈ Finset.range 67, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((8161311907213 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix66,
    observedFirstWeekMeanLoss66]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix68 :
    (∑ i ∈ Finset.range 68, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((8247050774557 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix67,
    observedFirstWeekMeanLoss67]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix69 :
    (∑ i ∈ Finset.range 69, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4165560598579 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix68,
    observedFirstWeekMeanLoss68]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix70 :
    (∑ i ∈ Finset.range 70, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4254785840757 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix69,
    observedFirstWeekMeanLoss69]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix71 :
    (∑ i ∈ Finset.range 71, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((8629159695739 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix70,
    observedFirstWeekMeanLoss70]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix72 :
    (∑ i ∈ Finset.range 72, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((440079571387 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix71,
    observedFirstWeekMeanLoss71]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix73 :
    (∑ i ∈ Finset.range 73, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((276596051583 : Rat) / 31250000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix72,
    observedFirstWeekMeanLoss72]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix74 :
    (∑ i ∈ Finset.range 74, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((17796813749 : Rat) / 2000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix73,
    observedFirstWeekMeanLoss73]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix75 :
    (∑ i ∈ Finset.range 75, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1122588806437 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix74,
    observedFirstWeekMeanLoss74]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix76 :
    (∑ i ∈ Finset.range 76, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((9099204055937 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix75,
    observedFirstWeekMeanLoss75]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix77 :
    (∑ i ∈ Finset.range 77, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((9110423102337 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix76,
    observedFirstWeekMeanLoss76]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix78 :
    (∑ i ∈ Finset.range 78, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4594171958393 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix77,
    observedFirstWeekMeanLoss77]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix79 :
    (∑ i ∈ Finset.range 79, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((74581135831 : Rat) / 8000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix78,
    observedFirstWeekMeanLoss78]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix80 :
    (∑ i ∈ Finset.range 80, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2371398467451 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix79,
    observedFirstWeekMeanLoss79]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix81 :
    (∑ i ∈ Finset.range 81, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((9542503312053 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix80,
    observedFirstWeekMeanLoss80]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix82 :
    (∑ i ∈ Finset.range 82, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((9800557152153 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix81,
    observedFirstWeekMeanLoss81]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix83 :
    (∑ i ∈ Finset.range 83, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5064894336761 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix82,
    observedFirstWeekMeanLoss82]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix84 :
    (∑ i ∈ Finset.range 84, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((10242920668723 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix83,
    observedFirstWeekMeanLoss83]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix85 :
    (∑ i ∈ Finset.range 85, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((10311954027287 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix84,
    observedFirstWeekMeanLoss84]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix86 :
    (∑ i ∈ Finset.range 86, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((162908361999 : Rat) / 15625000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix85,
    observedFirstWeekMeanLoss85]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix87 :
    (∑ i ∈ Finset.range 87, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((667239703621 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix86,
    observedFirstWeekMeanLoss86]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix88 :
    (∑ i ∈ Finset.range 88, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((671322402437 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix87,
    observedFirstWeekMeanLoss87]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix89 :
    (∑ i ∈ Finset.range 89, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((10868852458641 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix88,
    observedFirstWeekMeanLoss88]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix90 :
    (∑ i ∈ Finset.range 90, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5546141783933 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix89,
    observedFirstWeekMeanLoss89]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix91 :
    (∑ i ∈ Finset.range 91, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5650351604383 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix90,
    observedFirstWeekMeanLoss90]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix92 :
    (∑ i ∈ Finset.range 92, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2326186775283 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix91,
    observedFirstWeekMeanLoss91]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix93 :
    (∑ i ∈ Finset.range 93, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((294712678711 : Rat) / 25000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix92,
    observedFirstWeekMeanLoss92]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix94 :
    (∑ i ∈ Finset.range 94, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1509462530707 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix93,
    observedFirstWeekMeanLoss93]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix95 :
    (∑ i ∈ Finset.range 95, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1540383899269 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix94,
    observedFirstWeekMeanLoss94]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix96 :
    (∑ i ∈ Finset.range 96, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((12442922172177 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix95,
    observedFirstWeekMeanLoss95]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix97 :
    (∑ i ∈ Finset.range 97, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((12605490799381 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix96,
    observedFirstWeekMeanLoss96]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix98 :
    (∑ i ∈ Finset.range 98, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((13101058928537 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix97,
    observedFirstWeekMeanLoss97]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix99 :
    (∑ i ∈ Finset.range 99, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((13214058440253 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix98,
    observedFirstWeekMeanLoss98]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix100 :
    (∑ i ∈ Finset.range 100, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((6686809770827 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix99,
    observedFirstWeekMeanLoss99]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix101 :
    (∑ i ∈ Finset.range 101, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((6709440626579 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix100,
    observedFirstWeekMeanLoss100]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix102 :
    (∑ i ∈ Finset.range 102, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((13642361524327 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix101,
    observedFirstWeekMeanLoss101]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix103 :
    (∑ i ∈ Finset.range 103, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((13647960753911 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix102,
    observedFirstWeekMeanLoss102]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix104 :
    (∑ i ∈ Finset.range 104, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((172007661871 : Rat) / 12500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix103,
    observedFirstWeekMeanLoss103]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix105 :
    (∑ i ∈ Finset.range 105, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((173007925551 : Rat) / 12500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix104,
    observedFirstWeekMeanLoss104]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix106 :
    (∑ i ∈ Finset.range 106, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((13997626709809 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix105,
    observedFirstWeekMeanLoss105]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix107 :
    (∑ i ∈ Finset.range 107, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2829543573373 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix106,
    observedFirstWeekMeanLoss106]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix108 :
    (∑ i ∈ Finset.range 108, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1433821083389 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix107,
    observedFirstWeekMeanLoss107]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix109 :
    (∑ i ∈ Finset.range 109, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((14458309815699 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix108,
    observedFirstWeekMeanLoss108]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix110 :
    (∑ i ∈ Finset.range 110, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3640232363337 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix109,
    observedFirstWeekMeanLoss109]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix111 :
    (∑ i ∈ Finset.range 111, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((14649232924629 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix110,
    observedFirstWeekMeanLoss110]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix112 :
    (∑ i ∈ Finset.range 112, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((14761344053529 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix111,
    observedFirstWeekMeanLoss111]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix113 :
    (∑ i ∈ Finset.range 113, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((14918431034493 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix112,
    observedFirstWeekMeanLoss112]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix114 :
    (∑ i ∈ Finset.range 114, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((7589437444031 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix113,
    observedFirstWeekMeanLoss113]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix115 :
    (∑ i ∈ Finset.range 115, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((15217440385223 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix114,
    observedFirstWeekMeanLoss114]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix116 :
    (∑ i ∈ Finset.range 116, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1929514190731 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix115,
    observedFirstWeekMeanLoss115]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix117 :
    (∑ i ∈ Finset.range 117, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((15562295484689 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix116,
    observedFirstWeekMeanLoss116]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix118 :
    (∑ i ∈ Finset.range 118, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((15642422977313 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix117,
    observedFirstWeekMeanLoss117]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix119 :
    (∑ i ∈ Finset.range 119, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((15713911833189 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix118,
    observedFirstWeekMeanLoss118]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix120 :
    (∑ i ∈ Finset.range 120, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((16144079913573 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix119,
    observedFirstWeekMeanLoss119]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix121 :
    (∑ i ∈ Finset.range 121, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((16256018336757 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix120,
    observedFirstWeekMeanLoss120]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix122 :
    (∑ i ∈ Finset.range 122, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((8338719363659 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix121,
    observedFirstWeekMeanLoss121]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix123 :
    (∑ i ∈ Finset.range 123, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((16787348879047 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix122,
    observedFirstWeekMeanLoss122]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix124 :
    (∑ i ∈ Finset.range 124, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((17148763866731 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix123,
    observedFirstWeekMeanLoss123]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix125 :
    (∑ i ∈ Finset.range 125, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4299457747463 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix124,
    observedFirstWeekMeanLoss124]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix126 :
    (∑ i ∈ Finset.range 126, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((17288268921293 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix125,
    observedFirstWeekMeanLoss125]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix127 :
    (∑ i ∈ Finset.range 127, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((17675837423793 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix126,
    observedFirstWeekMeanLoss126]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix128 :
    (∑ i ∈ Finset.range 128, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((8947685920409 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix127,
    observedFirstWeekMeanLoss127]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix129 :
    (∑ i ∈ Finset.range 129, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((18362788815859 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix128,
    observedFirstWeekMeanLoss128]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix130 :
    (∑ i ∈ Finset.range 130, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((931449093379 : Rat) / 50000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix129,
    observedFirstWeekMeanLoss129]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix131 :
    (∑ i ∈ Finset.range 131, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((18762730791669 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix130,
    observedFirstWeekMeanLoss130]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix132 :
    (∑ i ∈ Finset.range 132, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1906844136559 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix131,
    observedFirstWeekMeanLoss131]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix133 :
    (∑ i ∈ Finset.range 133, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((19347792725959 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix132,
    observedFirstWeekMeanLoss132]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix134 :
    (∑ i ∈ Finset.range 134, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((3890929436591 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix133,
    observedFirstWeekMeanLoss133]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix135 :
    (∑ i ∈ Finset.range 135, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((19595522794511 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix134,
    observedFirstWeekMeanLoss134]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix136 :
    (∑ i ∈ Finset.range 136, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((19705653854111 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix135,
    observedFirstWeekMeanLoss135]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix137 :
    (∑ i ∈ Finset.range 137, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((1238856656021 : Rat) / 62500000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix136,
    observedFirstWeekMeanLoss136]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix138 :
    (∑ i ∈ Finset.range 138, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4011553870221 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix137,
    observedFirstWeekMeanLoss137]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix139 :
    (∑ i ∈ Finset.range 139, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((20145056508241 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix138,
    observedFirstWeekMeanLoss138]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix140 :
    (∑ i ∈ Finset.range 140, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4043770263469 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix139,
    observedFirstWeekMeanLoss139]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix141 :
    (∑ i ∈ Finset.range 141, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((20289207818849 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix140,
    observedFirstWeekMeanLoss140]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix142 :
    (∑ i ∈ Finset.range 142, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4068312000897 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix141,
    observedFirstWeekMeanLoss141]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix143 :
    (∑ i ∈ Finset.range 143, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((20475627291589 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix142,
    observedFirstWeekMeanLoss142]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix144 :
    (∑ i ∈ Finset.range 144, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((20490267807593 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix143,
    observedFirstWeekMeanLoss143]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix145 :
    (∑ i ∈ Finset.range 145, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((20545705451897 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix144,
    observedFirstWeekMeanLoss144]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix146 :
    (∑ i ∈ Finset.range 146, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((10354753888761 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix145,
    observedFirstWeekMeanLoss145]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix147 :
    (∑ i ∈ Finset.range 147, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((20744305322203 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix146,
    observedFirstWeekMeanLoss146]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix148 :
    (∑ i ∈ Finset.range 148, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5202709462481 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix147,
    observedFirstWeekMeanLoss147]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix149 :
    (∑ i ∈ Finset.range 149, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4179340768953 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix148,
    observedFirstWeekMeanLoss148]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix150 :
    (∑ i ∈ Finset.range 150, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((21069325813249 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix149,
    observedFirstWeekMeanLoss149]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix151 :
    (∑ i ∈ Finset.range 151, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((10651871748569 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix150,
    observedFirstWeekMeanLoss150]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix152 :
    (∑ i ∈ Finset.range 152, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((21539887983947 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix151,
    observedFirstWeekMeanLoss151]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix153 :
    (∑ i ∈ Finset.range 153, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((21604904824203 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix152,
    observedFirstWeekMeanLoss152]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix154 :
    (∑ i ∈ Finset.range 154, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((21695781749967 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix153,
    observedFirstWeekMeanLoss153]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix155 :
    (∑ i ∈ Finset.range 155, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2723773884011 : Rat) / 125000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix154,
    observedFirstWeekMeanLoss154]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix156 :
    (∑ i ∈ Finset.range 156, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5494358984903 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix155,
    observedFirstWeekMeanLoss155]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix157 :
    (∑ i ∈ Finset.range 157, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5527934416599 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix156,
    observedFirstWeekMeanLoss156]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix158 :
    (∑ i ∈ Finset.range 158, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5538185979099 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix157,
    observedFirstWeekMeanLoss157]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix159 :
    (∑ i ∈ Finset.range 159, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((22245102165421 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix158,
    observedFirstWeekMeanLoss158]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix160 :
    (∑ i ∈ Finset.range 160, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((2233716161399 : Rat) / 100000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix159,
    observedFirstWeekMeanLoss159]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix161 :
    (∑ i ∈ Finset.range 161, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((11257328494597 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix160,
    observedFirstWeekMeanLoss160]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix162 :
    (∑ i ∈ Finset.range 162, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((22647179926563 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix161,
    observedFirstWeekMeanLoss161]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix163 :
    (∑ i ∈ Finset.range 163, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((22945579914163 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix162,
    observedFirstWeekMeanLoss162]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix164 :
    (∑ i ∈ Finset.range 164, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((5758712798813 : Rat) / 250000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix163,
    observedFirstWeekMeanLoss163]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix165 :
    (∑ i ∈ Finset.range 165, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((23075992421141 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix164,
    observedFirstWeekMeanLoss164]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix166 :
    (∑ i ∈ Finset.range 166, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((23183635469241 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix165,
    observedFirstWeekMeanLoss165]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix167 :
    (∑ i ∈ Finset.range 167, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((4640381171493 : Rat) / 200000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix166,
    observedFirstWeekMeanLoss166]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix168 :
    (∑ i ∈ Finset.range 168, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((11612801844473 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix167,
    observedFirstWeekMeanLoss167]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix169 :
    (∑ i ∈ Finset.range 169, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((11705492801273 : Rat) / 500000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix168,
    observedFirstWeekMeanLoss168]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix170 :
    (∑ i ∈ Finset.range 170, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((23582576237771 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix169,
    observedFirstWeekMeanLoss169]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix171 :
    (∑ i ∈ Finset.range 171, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((23600194552527 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix170,
    observedFirstWeekMeanLoss170]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix172 :
    (∑ i ∈ Finset.range 172, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((23731379046163 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix171,
    observedFirstWeekMeanLoss171]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix173 :
    (∑ i ∈ Finset.range 173, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((23844160835063 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix172,
    observedFirstWeekMeanLoss172]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix174 :
    (∑ i ∈ Finset.range 174, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((749728359171 : Rat) / 31250000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix173,
    observedFirstWeekMeanLoss173]
  norm_num [ratToReal]

theorem observedFirstWeekMeanLossPrefix175 :
    (∑ i ∈ Finset.range 175, observedTrajectoryScore
        (monitorBrierScore firstWeekMean) i replayPath) =
      ratToReal ((24193342460761 : Rat) / 1000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanLossPrefix174,
    observedFirstWeekMeanLoss174]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor0 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 0 replayPath =
      ratToReal ((1 : Rat) / 2) := by
  norm_num [forwardPredictorProcess, forwardPredictor, ratToReal]

theorem observedFirstWeekMeanPredictor1 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 1 replayPath =
      ratToReal ((61945734321 : Rat) / 1000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix1]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor2 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 2 replayPath =
      ratToReal ((237397811221 : Rat) / 2000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix2]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor3 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 3 replayPath =
      ratToReal ((33954388883 : Rat) / 300000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix3]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor4 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 4 replayPath =
      ratToReal ((437524783191 : Rat) / 4000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix4]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor5 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 5 replayPath =
      ratToReal ((6327391463 : Rat) / 62500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix5]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor6 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 6 replayPath =
      ratToReal ((9237003611 : Rat) / 93750000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix6]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor7 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 7 replayPath =
      ratToReal ((10234300011 : Rat) / 109375000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix7]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor8 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 8 replayPath =
      ratToReal ((719823998929 : Rat) / 8000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix8]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor9 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 9 replayPath =
      ratToReal ((17885761993 : Rat) / 180000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix9]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor10 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 10 replayPath =
      ratToReal ((963185424939 : Rat) / 10000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix10]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor11 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 11 replayPath =
      ratToReal ((257319273457 : Rat) / 2750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix11]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor12 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 12 replayPath =
      ratToReal ((1537553408053 : Rat) / 12000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix12]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor13 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 13 replayPath =
      ratToReal ((1606365190453 : Rat) / 13000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix13]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor14 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 14 replayPath =
      ratToReal ((836851941731 : Rat) / 7000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix14]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor15 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 15 replayPath =
      ratToReal ((1943593484543 : Rat) / 15000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix15]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor16 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 16 replayPath =
      ratToReal ((64481903827 : Rat) / 500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix16]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor17 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 17 replayPath =
      ratToReal ((132621275183 : Rat) / 1062500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix17]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor18 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 18 replayPath =
      ratToReal ((190536970919 : Rat) / 1500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix18]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor19 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 19 replayPath =
      ratToReal ((292907035043 : Rat) / 2375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix19]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor20 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 20 replayPath =
      ratToReal ((657504668087 : Rat) / 5000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix20]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor21 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 21 replayPath =
      ratToReal ((949413751599 : Rat) / 7000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix21]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor22 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 22 replayPath =
      ratToReal ((1498746448179 : Rat) / 11000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix22]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor23 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 23 replayPath =
      ratToReal ((3014068686367 : Rat) / 23000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix23]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor24 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 24 replayPath =
      ratToReal ((50098973027 : Rat) / 375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix24]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor25 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 25 replayPath =
      ratToReal ((204702532733 : Rat) / 1562500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix25]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor26 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 26 replayPath =
      ratToReal ((64478112057 : Rat) / 500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix26]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor27 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 27 replayPath =
      ratToReal ((446571204983 : Rat) / 3375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix27]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor28 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 28 replayPath =
      ratToReal ((36188350687 : Rat) / 280000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix28]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor29 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 29 replayPath =
      ratToReal ((3747814453469 : Rat) / 29000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix29]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor30 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 30 replayPath =
      ratToReal ((643433042893 : Rat) / 5000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix30]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor31 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 31 replayPath =
      ratToReal ((2042996707961 : Rat) / 15500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix31]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor32 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 32 replayPath =
      ratToReal ((2105140343929 : Rat) / 16000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix32]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor33 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 33 replayPath =
      ratToReal ((4396720701227 : Rat) / 33000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix33]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor34 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 34 replayPath =
      ratToReal ((4664253780923 : Rat) / 34000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix34]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor35 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 35 replayPath =
      ratToReal ((1177016009601 : Rat) / 8750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix35]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor36 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 36 replayPath =
      ratToReal ((401905252567 : Rat) / 3000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix36]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor37 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 37 replayPath =
      ratToReal ((48760559953 : Rat) / 370000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix37]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor38 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 38 replayPath =
      ratToReal ((5007769099229 : Rat) / 38000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix38]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor39 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 39 replayPath =
      ratToReal ((2624187032227 : Rat) / 19500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix39]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor40 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 40 replayPath =
      ratToReal ((1071935140323 : Rat) / 8000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix40]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor41 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 41 replayPath =
      ratToReal ((1076605319543 : Rat) / 8200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix41]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor42 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 42 replayPath =
      ratToReal ((5392745797111 : Rat) / 42000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix42]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor43 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 43 replayPath =
      ratToReal ((5437369824647 : Rat) / 43000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix43]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor44 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 44 replayPath =
      ratToReal ((691950475197 : Rat) / 5500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix44]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor45 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 45 replayPath =
      ratToReal ((5667434518801 : Rat) / 45000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix45]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor46 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 46 replayPath =
      ratToReal ((5768469498401 : Rat) / 46000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix46]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor47 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 47 replayPath =
      ratToReal ((2907792053941 : Rat) / 23500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix47]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor48 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 48 replayPath =
      ratToReal ((2950169227879 : Rat) / 24000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix48]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor49 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 49 replayPath =
      ratToReal ((6222913609607 : Rat) / 49000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix49]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor50 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 50 replayPath =
      ratToReal ((395949052773 : Rat) / 3125000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix50]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor51 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 51 replayPath =
      ratToReal ((529513968471 : Rat) / 4250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix51]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor52 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 52 replayPath =
      ratToReal ((821000215967 : Rat) / 6500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix52]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor53 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 53 replayPath =
      ratToReal ((33161553151 : Rat) / 265000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix53]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor54 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 54 replayPath =
      ratToReal ((6797024041001 : Rat) / 54000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix54]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor55 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 55 replayPath =
      ratToReal ((3425361648681 : Rat) / 27500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix55]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor56 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 56 replayPath =
      ratToReal ((3442983300593 : Rat) / 28000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix56]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor57 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 57 replayPath =
      ratToReal ((1384049943167 : Rat) / 11400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix57]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor58 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 58 replayPath =
      ratToReal ((1786373956259 : Rat) / 14500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix58]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor59 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 59 replayPath =
      ratToReal ((358821620679 : Rat) / 2950000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix59]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor60 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 60 replayPath =
      ratToReal ((450766728799 : Rat) / 3750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix60]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor61 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 61 replayPath =
      ratToReal ((1450011726397 : Rat) / 12200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix61]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor62 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 62 replayPath =
      ratToReal ((3773809531533 : Rat) / 31000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix62]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor63 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 63 replayPath =
      ratToReal ((7600896473827 : Rat) / 63000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix63]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor64 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 64 replayPath =
      ratToReal ((1906730718689 : Rat) / 16000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix64]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor65 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 65 replayPath =
      ratToReal ((1544871724873 : Rat) / 13000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix65]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor66 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 66 replayPath =
      ratToReal ((2665715852543 : Rat) / 22000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix66]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor67 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 67 replayPath =
      ratToReal ((8161311907213 : Rat) / 67000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix67]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor68 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 68 replayPath =
      ratToReal ((8247050774557 : Rat) / 68000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix68]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor69 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 69 replayPath =
      ratToReal ((181111330373 : Rat) / 1500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix69]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor70 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 70 replayPath =
      ratToReal ((4254785840757 : Rat) / 35000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix70]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor71 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 71 replayPath =
      ratToReal ((8629159695739 : Rat) / 71000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix71]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor72 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 72 replayPath =
      ratToReal ((440079571387 : Rat) / 3600000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix72]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor73 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 73 replayPath =
      ratToReal ((276596051583 : Rat) / 2281250000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix73]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor74 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 74 replayPath =
      ratToReal ((17796813749 : Rat) / 148000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix74]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor75 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 75 replayPath =
      ratToReal ((1122588806437 : Rat) / 9375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix75]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor76 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 76 replayPath =
      ratToReal ((9099204055937 : Rat) / 76000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix76]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor77 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 77 replayPath =
      ratToReal ((9110423102337 : Rat) / 77000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix77]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor78 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 78 replayPath =
      ratToReal ((4594171958393 : Rat) / 39000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix78]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor79 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 79 replayPath =
      ratToReal ((74581135831 : Rat) / 632000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix79]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor80 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 80 replayPath =
      ratToReal ((2371398467451 : Rat) / 20000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix80]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor81 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 81 replayPath =
      ratToReal ((3180834437351 : Rat) / 27000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix81]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor82 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 82 replayPath =
      ratToReal ((9800557152153 : Rat) / 82000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix82]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor83 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 83 replayPath =
      ratToReal ((5064894336761 : Rat) / 41500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix83]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor84 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 84 replayPath =
      ratToReal ((10242920668723 : Rat) / 84000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix84]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor85 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 85 replayPath =
      ratToReal ((10311954027287 : Rat) / 85000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix85]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor86 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 86 replayPath =
      ratToReal ((162908361999 : Rat) / 1343750000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix86]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor87 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 87 replayPath =
      ratToReal ((667239703621 : Rat) / 5437500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix87]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor88 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 88 replayPath =
      ratToReal ((671322402437 : Rat) / 5500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix88]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor89 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 89 replayPath =
      ratToReal ((10868852458641 : Rat) / 89000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix89]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor90 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 90 replayPath =
      ratToReal ((5546141783933 : Rat) / 45000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix90]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor91 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 91 replayPath =
      ratToReal ((5650351604383 : Rat) / 45500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix91]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor92 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 92 replayPath =
      ratToReal ((2326186775283 : Rat) / 18400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix92]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor93 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 93 replayPath =
      ratToReal ((294712678711 : Rat) / 2325000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix93]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor94 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 94 replayPath =
      ratToReal ((1509462530707 : Rat) / 11750000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix94]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor95 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 95 replayPath =
      ratToReal ((1540383899269 : Rat) / 11875000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix95]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor96 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 96 replayPath =
      ratToReal ((4147640724059 : Rat) / 32000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix96]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor97 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 97 replayPath =
      ratToReal ((12605490799381 : Rat) / 97000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix97]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor98 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 98 replayPath =
      ratToReal ((13101058928537 : Rat) / 98000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix98]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor99 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 99 replayPath =
      ratToReal ((400426013341 : Rat) / 3000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix99]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor100 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 100 replayPath =
      ratToReal ((6686809770827 : Rat) / 50000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix100]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor101 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 101 replayPath =
      ratToReal ((6709440626579 : Rat) / 50500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix101]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor102 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 102 replayPath =
      ratToReal ((13642361524327 : Rat) / 102000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix102]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor103 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 103 replayPath =
      ratToReal ((13647960753911 : Rat) / 103000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix103]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor104 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 104 replayPath =
      ratToReal ((172007661871 : Rat) / 1300000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix104]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor105 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 105 replayPath =
      ratToReal ((57669308517 : Rat) / 437500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix105]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor106 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 106 replayPath =
      ratToReal ((13997626709809 : Rat) / 106000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix106]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor107 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 107 replayPath =
      ratToReal ((2829543573373 : Rat) / 21400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix107]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor108 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 108 replayPath =
      ratToReal ((1433821083389 : Rat) / 10800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix108]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor109 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 109 replayPath =
      ratToReal ((14458309815699 : Rat) / 109000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix109]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor110 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 110 replayPath =
      ratToReal ((3640232363337 : Rat) / 27500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix110]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor111 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 111 replayPath =
      ratToReal ((4883077641543 : Rat) / 37000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix111]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor112 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 112 replayPath =
      ratToReal ((14761344053529 : Rat) / 112000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix112]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor113 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 113 replayPath =
      ratToReal ((14918431034493 : Rat) / 113000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix113]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor114 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 114 replayPath =
      ratToReal ((7589437444031 : Rat) / 57000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix114]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor115 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 115 replayPath =
      ratToReal ((15217440385223 : Rat) / 115000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix115]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor116 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 116 replayPath =
      ratToReal ((1929514190731 : Rat) / 14500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix116]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor117 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 117 replayPath =
      ratToReal ((15562295484689 : Rat) / 117000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix117]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor118 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 118 replayPath =
      ratToReal ((15642422977313 : Rat) / 118000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix118]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor119 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 119 replayPath =
      ratToReal ((15713911833189 : Rat) / 119000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix119]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor120 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 120 replayPath =
      ratToReal ((5381359971191 : Rat) / 40000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix120]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor121 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 121 replayPath =
      ratToReal ((16256018336757 : Rat) / 121000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix121]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor122 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 122 replayPath =
      ratToReal ((8338719363659 : Rat) / 61000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix122]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor123 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 123 replayPath =
      ratToReal ((16787348879047 : Rat) / 123000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix123]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor124 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 124 replayPath =
      ratToReal ((17148763866731 : Rat) / 124000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix124]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor125 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 125 replayPath =
      ratToReal ((4299457747463 : Rat) / 31250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix125]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor126 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 126 replayPath =
      ratToReal ((17288268921293 : Rat) / 126000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix126]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor127 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 127 replayPath =
      ratToReal ((17675837423793 : Rat) / 127000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix127]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor128 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 128 replayPath =
      ratToReal ((8947685920409 : Rat) / 64000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix128]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor129 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 129 replayPath =
      ratToReal ((18362788815859 : Rat) / 129000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix129]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor130 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 130 replayPath =
      ratToReal ((931449093379 : Rat) / 6500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix130]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor131 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 131 replayPath =
      ratToReal ((18762730791669 : Rat) / 131000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix131]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor132 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 132 replayPath =
      ratToReal ((1906844136559 : Rat) / 13200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix132]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor133 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 133 replayPath =
      ratToReal ((19347792725959 : Rat) / 133000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix133]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor134 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 134 replayPath =
      ratToReal ((3890929436591 : Rat) / 26800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix134]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor135 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 135 replayPath =
      ratToReal ((19595522794511 : Rat) / 135000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix135]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor136 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 136 replayPath =
      ratToReal ((19705653854111 : Rat) / 136000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix136]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor137 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 137 replayPath =
      ratToReal ((1238856656021 : Rat) / 8562500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix137]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor138 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 138 replayPath =
      ratToReal ((1337184623407 : Rat) / 9200000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix138]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor139 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 139 replayPath =
      ratToReal ((20145056508241 : Rat) / 139000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix139]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor140 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 140 replayPath =
      ratToReal ((4043770263469 : Rat) / 28000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix140]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor141 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 141 replayPath =
      ratToReal ((20289207818849 : Rat) / 141000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix141]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor142 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 142 replayPath =
      ratToReal ((4068312000897 : Rat) / 28400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix142]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor143 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 143 replayPath =
      ratToReal ((20475627291589 : Rat) / 143000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix143]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor144 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 144 replayPath =
      ratToReal ((20490267807593 : Rat) / 144000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix144]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor145 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 145 replayPath =
      ratToReal ((20545705451897 : Rat) / 145000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix145]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor146 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 146 replayPath =
      ratToReal ((10354753888761 : Rat) / 73000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix146]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor147 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 147 replayPath =
      ratToReal ((20744305322203 : Rat) / 147000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix147]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor148 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 148 replayPath =
      ratToReal ((5202709462481 : Rat) / 37000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix148]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor149 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 149 replayPath =
      ratToReal ((4179340768953 : Rat) / 29800000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix149]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor150 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 150 replayPath =
      ratToReal ((21069325813249 : Rat) / 150000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix150]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor151 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 151 replayPath =
      ratToReal ((10651871748569 : Rat) / 75500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix151]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor152 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 152 replayPath =
      ratToReal ((21539887983947 : Rat) / 152000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix152]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor153 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 153 replayPath =
      ratToReal ((2400544980467 : Rat) / 17000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix153]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor154 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 154 replayPath =
      ratToReal ((21695781749967 : Rat) / 154000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix154]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor155 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 155 replayPath =
      ratToReal ((2723773884011 : Rat) / 19375000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix155]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor156 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 156 replayPath =
      ratToReal ((5494358984903 : Rat) / 39000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix156]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor157 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 157 replayPath =
      ratToReal ((5527934416599 : Rat) / 39250000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix157]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor158 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 158 replayPath =
      ratToReal ((5538185979099 : Rat) / 39500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix158]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor159 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 159 replayPath =
      ratToReal ((22245102165421 : Rat) / 159000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix159]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor160 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 160 replayPath =
      ratToReal ((2233716161399 : Rat) / 16000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix160]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor161 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 161 replayPath =
      ratToReal ((11257328494597 : Rat) / 80500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix161]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor162 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 162 replayPath =
      ratToReal ((7549059975521 : Rat) / 54000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix162]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor163 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 163 replayPath =
      ratToReal ((22945579914163 : Rat) / 163000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix163]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor164 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 164 replayPath =
      ratToReal ((5758712798813 : Rat) / 41000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix164]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor165 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 165 replayPath =
      ratToReal ((2097817492831 : Rat) / 15000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix165]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor166 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 166 replayPath =
      ratToReal ((23183635469241 : Rat) / 166000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix166]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor167 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 167 replayPath =
      ratToReal ((4640381171493 : Rat) / 33400000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix167]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor168 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 168 replayPath =
      ratToReal ((11612801844473 : Rat) / 84000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix168]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor169 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 169 replayPath =
      ratToReal ((11705492801273 : Rat) / 84500000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix169]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor170 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 170 replayPath =
      ratToReal ((23582576237771 : Rat) / 170000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix170]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor171 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 171 replayPath =
      ratToReal ((7866731517509 : Rat) / 57000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix171]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor172 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 172 replayPath =
      ratToReal ((23731379046163 : Rat) / 172000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix172]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor173 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 173 replayPath =
      ratToReal ((23844160835063 : Rat) / 173000000000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix173]
  norm_num [ratToReal]

theorem observedFirstWeekMeanPredictor174 :
    forwardPredictorProcess
        (observedTrajectoryScore
          (monitorBrierScore firstWeekMean)) 174 replayPath =
      ratToReal ((249909453057 : Rat) / 1812500000000) := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg (by norm_num),
    observedFirstWeekMeanLossPrefix174]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix0 :
    (∑ i ∈ Finset.range 0,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal 0 := by
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix1 :
    (∑ i ∈ Finset.range 1,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((191891539679567917331041 : Rat) / 1000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix0,
    observedFirstWeekMeanLoss0,
    observedFirstWeekMeanPredictor0]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix2 :
    (∑ i ∈ Finset.range 2,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((102387614742614612851141 : Rat) / 500000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix1,
    observedFirstWeekMeanLoss1,
    observedFirstWeekMeanPredictor1]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix3 :
    (∑ i ∈ Finset.range 3,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((820196902400305872745137 : Rat) / 4000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix2,
    observedFirstWeekMeanLoss2,
    observedFirstWeekMeanPredictor2]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix4 :
    (∑ i ∈ Finset.range 4,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((7390090001465073758018269 : Rat) / 36000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix3,
    observedFirstWeekMeanLoss3,
    observedFirstWeekMeanPredictor3]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix5 :
    (∑ i ∈ Finset.range 5,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((29799066458314837757331301 : Rat) / 144000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix4,
    observedFirstWeekMeanLoss4,
    observedFirstWeekMeanPredictor4]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix6 :
    (∑ i ∈ Finset.range 6,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((5967428918358610697299937 : Rat) / 28800000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix5,
    observedFirstWeekMeanLoss5,
    observedFirstWeekMeanPredictor5]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix7 :
    (∑ i ∈ Finset.range 7,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((30010544234289848020731749 : Rat) / 144000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix6,
    observedFirstWeekMeanLoss6,
    observedFirstWeekMeanPredictor6]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix8 :
    (∑ i ∈ Finset.range 8,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((295269124951000880172885601 : Rat) / 1411200000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix7,
    observedFirstWeekMeanLoss7,
    observedFirstWeekMeanPredictor7]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix9 :
    (∑ i ∈ Finset.range 9,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6106842623551736553906529181 : Rat) / 28224000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix8,
    observedFirstWeekMeanLoss8,
    observedFirstWeekMeanPredictor8]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix10 :
    (∑ i ∈ Finset.range 10,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((11039477342549179409397341633 : Rat) / 50803200000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix9,
    observedFirstWeekMeanLoss9,
    observedFirstWeekMeanPredictor9]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix11 :
    (∑ i ∈ Finset.range 11,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1385736798972536508855076689229 : Rat) / 6350400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix10,
    observedFirstWeekMeanLoss10,
    observedFirstWeekMeanPredictor10]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix12 :
    (∑ i ∈ Finset.range 12,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((299823918214236618751656585190309 : Rat) / 768398400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix11,
    observedFirstWeekMeanLoss11,
    observedFirstWeekMeanPredictor11]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix13 :
    (∑ i ∈ Finset.range 13,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((302527593889489879437910709015209 : Rat) / 768398400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix12,
    observedFirstWeekMeanLoss12,
    observedFirstWeekMeanPredictor12]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix14 :
    (∑ i ∈ Finset.range 14,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((51537723020416265359072333118136721 : Rat) / 129859329600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix13,
    observedFirstWeekMeanLoss13,
    observedFirstWeekMeanPredictor13]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix15 :
    (∑ i ∈ Finset.range 15,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((54472792192596760583110143019935121 : Rat) / 129859329600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix14,
    observedFirstWeekMeanLoss14,
    observedFirstWeekMeanPredictor14]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix16 :
    (∑ i ∈ Finset.range 16,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((10897025090800187848625747767402781 : Rat) / 25971865920000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix15,
    observedFirstWeekMeanLoss15,
    observedFirstWeekMeanPredictor15]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix17 :
    (∑ i ∈ Finset.range 17,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((11025907962215177390274293426314781 : Rat) / 25971865920000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix16,
    observedFirstWeekMeanLoss16,
    observedFirstWeekMeanPredictor16]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix18 :
    (∑ i ∈ Finset.range 18,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3198307330971591660931627557894156989 : Rat) / 7505869250880000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix17,
    observedFirstWeekMeanLoss17,
    observedFirstWeekMeanPredictor17]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix19 :
    (∑ i ∈ Finset.range 19,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3235309220777488299158173801667628989 : Rat) / 7505869250880000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix18,
    observedFirstWeekMeanLoss18,
    observedFirstWeekMeanPredictor18]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix20 :
    (∑ i ∈ Finset.range 20,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1240321584029165126775459360794247030149 : Rat) / 2709618799567680000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix19,
    observedFirstWeekMeanLoss19,
    observedFirstWeekMeanPredictor19]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix21 :
    (∑ i ∈ Finset.range 21,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6303498317077155004693455790362900407449 : Rat) / 13548093997838400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix20,
    observedFirstWeekMeanLoss20,
    observedFirstWeekMeanPredictor20]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix22 :
    (∑ i ∈ Finset.range 22,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6306011956170446043670969990172483101849 : Rat) / 13548093997838400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix21,
    observedFirstWeekMeanLoss21,
    observedFirstWeekMeanPredictor21]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix23 :
    (∑ i ∈ Finset.range 23,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6500045580594573773965451930883333661849 : Rat) / 13548093997838400000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix22,
    observedFirstWeekMeanLoss22,
    observedFirstWeekMeanPredictor22]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix24 :
    (∑ i ∈ Finset.range 24,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3465384240077408334313973003046351043604521 : Rat) / 7166941724856513600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix23,
    observedFirstWeekMeanLoss23,
    observedFirstWeekMeanPredictor23]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix25 :
    (∑ i ∈ Finset.range 25,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3495377367698463937188256015029594205306921 : Rat) / 7166941724856513600000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix24,
    observedFirstWeekMeanLoss24,
    observedFirstWeekMeanPredictor24]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix26 :
    (∑ i ∈ Finset.range 26,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((87895134776398768874116850284392585251358721 : Rat) / 179173543121412840000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix25,
    observedFirstWeekMeanLoss25,
    observedFirstWeekMeanPredictor25]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix27 :
    (∑ i ∈ Finset.range 27,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((89370781356891550629632358988225266391998721 : Rat) / 179173543121412840000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix26,
    observedFirstWeekMeanLoss26,
    observedFirstWeekMeanPredictor26]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix28 :
    (∑ i ∈ Finset.range 28,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((816277957401436168833835318930029033040948489 : Rat) / 1612561888092715560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix27,
    observedFirstWeekMeanLoss27,
    observedFirstWeekMeanPredictor27]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix29 :
    (∑ i ∈ Finset.range 29,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((816278070408538478533637918086423709101108489 : Rat) / 1612561888092715560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix28,
    observedFirstWeekMeanLoss28,
    observedFirstWeekMeanPredictor28]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix30 :
    (∑ i ∈ Finset.range 30,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((686856891259524728559295005711049006226464879249 : Rat) / 1356164547885973785960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix29,
    observedFirstWeekMeanLoss29,
    observedFirstWeekMeanPredictor29]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix31 :
    (∑ i ∈ Finset.range 31,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((699540479377027009602453462478213783225080112849 : Rat) / 1356164547885973785960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix30,
    observedFirstWeekMeanLoss30,
    observedFirstWeekMeanPredictor30]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix32 :
    (∑ i ∈ Finset.range 32,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((672332081113650669126959453633067398994241451007889 : Rat) / 1303274130518420808307560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix31,
    observedFirstWeekMeanLoss31,
    observedFirstWeekMeanPredictor31]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix33 :
    (∑ i ∈ Finset.range 33,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((2705022762507591207841834802872552550329595995047181 : Rat) / 5213096522073683233230240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix32,
    observedFirstWeekMeanLoss32,
    observedFirstWeekMeanPredictor32]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix34 :
    (∑ i ∈ Finset.range 34,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((2799047492265490384919577941634093488503633832007181 : Rat) / 5213096522073683233230240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix33,
    observedFirstWeekMeanLoss33,
    observedFirstWeekMeanPredictor33]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix35 :
    (∑ i ∈ Finset.range 35,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((2844498622912441071366919605828084167548843206447181 : Rat) / 5213096522073683233230240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix34,
    observedFirstWeekMeanLoss34,
    observedFirstWeekMeanPredictor34]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix36 :
    (∑ i ∈ Finset.range 36,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((2846525292062415790213354334743939186354968217493581 : Rat) / 5213096522073683233230240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix35,
    observedFirstWeekMeanLoss35,
    observedFirstWeekMeanPredictor35]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix37 :
    (∑ i ∈ Finset.range 37,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((2880539046417381906278787600602021001362481907253581 : Rat) / 5213096522073683233230240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix36,
    observedFirstWeekMeanLoss36,
    observedFirstWeekMeanPredictor36]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix38 :
    (∑ i ∈ Finset.range 38,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3943457991741058112924408197552564275684073518979112389 : Rat) / 7136729138718872346292198560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix37,
    observedFirstWeekMeanLoss37,
    observedFirstWeekMeanPredictor37]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix39 :
    (∑ i ∈ Finset.range 39,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4027972091919849214151313484459943813848475645431952389 : Rat) / 7136729138718872346292198560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix38,
    observedFirstWeekMeanLoss38,
    observedFirstWeekMeanPredictor38]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix40 :
    (∑ i ∈ Finset.range 40,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4031837263260158955340830940656971374231200258331952389 : Rat) / 7136729138718872346292198560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix39,
    observedFirstWeekMeanLoss39,
    observedFirstWeekMeanPredictor39]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix41 :
    (∑ i ∈ Finset.range 41,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4119201034106739271328300623800105200048533975533174889 : Rat) / 7136729138718872346292198560000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix40,
    observedFirstWeekMeanLoss40,
    observedFirstWeekMeanPredictor40]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix42 :
    (∑ i ∈ Finset.range 42,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((7101693493148937899551999444366264282871850584003631948409 : Rat) / 11996841682186424414117185779360000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix41,
    observedFirstWeekMeanLoss41,
    observedFirstWeekMeanPredictor41]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix43 :
    (∑ i ∈ Finset.range 43,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1026555670774127535471151181839571176945009636692760455487 : Rat) / 1713834526026632059159597968480000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix42,
    observedFirstWeekMeanLoss42,
    observedFirstWeekMeanPredictor42]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix44 :
    (∑ i ∈ Finset.range 44,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1900624402404044848662614463785564744578892068115901282195463 : Rat) / 3168880038623242677386096643719520000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix43,
    observedFirstWeekMeanLoss43,
    observedFirstWeekMeanPredictor43]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix45 :
    (∑ i ∈ Finset.range 45,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((172794482058602696269919221321956530631237400738551466774133 : Rat) / 288080003511203879762372422156320000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix44,
    observedFirstWeekMeanLoss44,
    observedFirstWeekMeanPredictor44]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix46 :
    (∑ i ∈ Finset.range 46,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((172973209470390852731928573825230384811725540827931308802933 : Rat) / 288080003511203879762372422156320000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix45,
    observedFirstWeekMeanLoss45,
    observedFirstWeekMeanPredictor45]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix47 :
    (∑ i ∈ Finset.range 47,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((174738805409015466554474871319191925901695785633292633802933 : Rat) / 288080003511203879762372422156320000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix46,
    observedFirstWeekMeanLoss46,
    observedFirstWeekMeanPredictor46]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix48 :
    (∑ i ∈ Finset.range 48,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((386965019137594061619607995570656268645111144541104329782678997 : Rat) / 636368727756249370395080680543310880000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix47,
    observedFirstWeekMeanLoss47,
    observedFirstWeekMeanPredictor47]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix49 :
    (∑ i ∈ Finset.range 49,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((412331119478221010568968423874659020071052455208117917399411497 : Rat) / 636368727756249370395080680543310880000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix48,
    observedFirstWeekMeanLoss48,
    observedFirstWeekMeanPredictor48]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix50 :
    (∑ i ∈ Finset.range 50,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((141476914351383167437257051672004571077763082171074113721642303471 : Rat) / 218274473620393534045512673426355631840000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix49,
    observedFirstWeekMeanLoss49,
    observedFirstWeekMeanPredictor49]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix51 :
    (∑ i ∈ Finset.range 51,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((28801945385765313695585572948687716114484606110627954673162720867 : Rat) / 43654894724078706809102534685271126368000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix50,
    observedFirstWeekMeanLoss50,
    observedFirstWeekMeanPredictor50]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix52 :
    (∑ i ∈ Finset.range 52,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((29149623392800627558228741811158505430370440761719829382787552867 : Rat) / 43654894724078706809102534685271126368000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix51,
    observedFirstWeekMeanLoss51,
    observedFirstWeekMeanPredictor51]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix53 :
    (∑ i ∈ Finset.range 53,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((29317426437211473460943481243748744431306299457824829668326240867 : Rat) / 43654894724078706809102534685271126368000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix52,
    observedFirstWeekMeanLoss52,
    observedFirstWeekMeanPredictor52]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix54 :
    (∑ i ∈ Finset.range 54,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((82544710870359822837164010923528383830594589034243410394001635907403 : Rat) / 122626599279937087426769019930926593967712000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix53,
    observedFirstWeekMeanLoss53,
    observedFirstWeekMeanPredictor53]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix55 :
    (∑ i ∈ Finset.range 55,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((83183440202336441565880501746539195347333812024098905653298474075403 : Rat) / 122626599279937087426769019930926593967712000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix54,
    observedFirstWeekMeanLoss54,
    observedFirstWeekMeanPredictor54]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix56 :
    (∑ i ∈ Finset.range 56,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((925778259366321529247792106735160396909658949663076346834553608792953 : Rat) / 1348892592079307961694459219240192533644832000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix55,
    observedFirstWeekMeanLoss55,
    observedFirstWeekMeanPredictor55]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix57 :
    (∑ i ∈ Finset.range 57,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((936386280274102519031369317284037713979768994242325337245307150410953 : Rat) / 1348892592079307961694459219240192533644832000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix56,
    observedFirstWeekMeanLoss56,
    observedFirstWeekMeanPredictor56]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix58 :
    (∑ i ∈ Finset.range 58,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((950930547140617156906450803203823730762556965724313626143169566922953 : Rat) / 1348892592079307961694459219240192533644832000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix57,
    observedFirstWeekMeanLoss57,
    observedFirstWeekMeanPredictor57]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix59 :
    (∑ i ∈ Finset.range 59,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((962412598303575507193030062781006772259503980453368433280765112650953 : Rat) / 1348892592079307961694459219240192533644832000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix58,
    observedFirstWeekMeanLoss58,
    observedFirstWeekMeanPredictor58]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix60 :
    (∑ i ∈ Finset.range 60,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3384724155133868324635237967486344622161801558858684944355412728988719393 : Rat) / 4695495113028071014658412542175110209617660192000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix59,
    observedFirstWeekMeanLoss59,
    observedFirstWeekMeanPredictor59]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix61 :
    (∑ i ∈ Finset.range 61,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3416615879540890060871316348427962834772792784318955178711141750586222113 : Rat) / 4695495113028071014658412542175110209617660192000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix60,
    observedFirstWeekMeanLoss60,
    observedFirstWeekMeanPredictor60]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix62 :
    (∑ i ∈ Finset.range 62,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((13271214897826391574030128783392950287541383227131356035395305515622520194473 : Rat) / 17471937315577452245543953069433585089987313574432000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix61,
    observedFirstWeekMeanLoss61,
    observedFirstWeekMeanPredictor61]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix63 :
    (∑ i ∈ Finset.range 63,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((13353098003407013062259064096165217694308819307656746947948949901069724162473 : Rat) / 17471937315577452245543953069433585089987313574432000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix62,
    observedFirstWeekMeanLoss62,
    observedFirstWeekMeanPredictor62]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix64 :
    (∑ i ∈ Finset.range 64,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((13509532377635501949876475385281371672531625264151417420129426604097244162473 : Rat) / 17471937315577452245543953069433585089987313574432000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix63,
    observedFirstWeekMeanLoss63,
    observedFirstWeekMeanPredictor63]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix65 :
    (∑ i ∈ Finset.range 65,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6758893119474188044581558610103975739432497476554452633979352498342471020299 : Rat) / 8735968657788726122771976534716792544993656787216000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix64,
    observedFirstWeekMeanLoss64,
    observedFirstWeekMeanPredictor64]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix66 :
    (∑ i ∈ Finset.range 66,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6965947959347296364280820033537595320431554278045094470376085319933297404299 : Rat) / 8735968657788726122771976534716792544993656787216000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix65,
    observedFirstWeekMeanLoss65,
    observedFirstWeekMeanPredictor65]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix67 :
    (∑ i ∈ Finset.range 67,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6982097345085225847874392791859348379939104632426878708285865018467697504299 : Rat) / 8735968657788726122771976534716792544993656787216000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix66,
    observedFirstWeekMeanLoss66,
    observedFirstWeekMeanPredictor66]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix68 :
    (∑ i ∈ Finset.range 68,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((31393661424869356430667052537168516281490507128928618497504981184579003652398211 : Rat) / 39215763304813591565123402664343681734476525317812624000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix67,
    observedFirstWeekMeanLoss67,
    observedFirstWeekMeanPredictor67]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix69 :
    (∑ i ∈ Finset.range 69,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((31447958176303375862200889555693912093059012141400093754078405378817685420119211 : Rat) / 39215763304813591565123402664343681734476525317812624000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix68,
    observedFirstWeekMeanLoss68,
    observedFirstWeekMeanPredictor68]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix70 :
    (∑ i ∈ Finset.range 70,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((31578562261737615621787038660547281226454585311324868394340206322049200315543211 : Rat) / 39215763304813591565123402664343681734476525317812624000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix69,
    observedFirstWeekMeanLoss69,
    observedFirstWeekMeanPredictor69]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix71 :
    (∑ i ∈ Finset.range 71,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((31578715583510838920078876866921685329989772562301095682952517567628616471808171 : Rat) / 39215763304813591565123402664343681734476525317812624000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix70,
    observedFirstWeekMeanLoss70,
    observedFirstWeekMeanPredictor70]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix72 :
    (∑ i ∈ Finset.range 72,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((159700358562606029952051961333565317076880968007878786455748818377503468409788766011 : Rat) / 197686662819565315079787072830956499623496164127093437584000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix71,
    observedFirstWeekMeanLoss71,
    observedFirstWeekMeanPredictor71]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix73 :
    (∑ i ∈ Finset.range 73,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((160746975718229198910817983041885569194867231471591824126964545263159944541292610011 : Rat) / 197686662819565315079787072830956499623496164127093437584000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix72,
    observedFirstWeekMeanLoss72,
    observedFirstWeekMeanPredictor72]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix74 :
    (∑ i ∈ Finset.range 74,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((862376102837911085193446953098465379241173144864666392084158983135859262522351001372619 : Rat) / 1053472226165463564060185311116167186493611058633280928885136000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix73,
    observedFirstWeekMeanLoss73,
    observedFirstWeekMeanPredictor73]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix75 :
    (∑ i ∈ Finset.range 75,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((863892929560918960380678859110602754600574184996653700230278775333024192586703731548619 : Rat) / 1053472226165463564060185311116167186493611058633280928885136000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix74,
    observedFirstWeekMeanLoss74,
    observedFirstWeekMeanPredictor74]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix76 :
    (∑ i ∈ Finset.range 76,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4319472867545789480925939897125702135772218159926844442901896615797964152562168477126007 : Rat) / 5267361130827317820300926555580835932468055293166404644425680000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix75,
    observedFirstWeekMeanLoss75,
    observedFirstWeekMeanPredictor75]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix77 :
    (∑ i ∈ Finset.range 77,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4381489929939110599297924264034565734489992981798916841305966990058988824438054138171007 : Rat) / 5267361130827317820300926555580835932468055293166404644425680000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix76,
    observedFirstWeekMeanLoss76,
    observedFirstWeekMeanPredictor76]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix78 :
    (∑ i ∈ Finset.range 78,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4390085560659734551701667557413649124569353697250183434650181743905399862733993682491007 : Rat) / 5267361130827317820300926555580835932468055293166404644425680000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix77,
    observedFirstWeekMeanLoss77,
    observedFirstWeekMeanPredictor77]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix79 :
    (∑ i ∈ Finset.range 79,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4391519387863467467018948478751086016304084258196440676961427772333495547796701625211007 : Rat) / 5267361130827317820300926555580835932468055293166404644425680000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix78,
    observedFirstWeekMeanLoss78,
    observedFirstWeekMeanPredictor78]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix80 :
    (∑ i ∈ Finset.range 80,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((27473875265904980009873223173826058008837795480122989158088862505965758426960278157835974687 : Rat) / 32873600817493290516498082633379997054533133084651531385860668880000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix79,
    observedFirstWeekMeanLoss79,
    observedFirstWeekMeanPredictor79]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix81 :
    (∑ i ∈ Finset.range 81,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((27598861187094440880299694921076839715282189110171657455291734058936054784992538547961294887 : Rat) / 32873600817493290516498082633379997054533133084651531385860668880000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix80,
    observedFirstWeekMeanLoss80,
    observedFirstWeekMeanPredictor80]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix82 :
    (∑ i ∈ Finset.range 82,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((9415147438397594541175742353304762588133264726920695295495499737423761399872327112264671629 : Rat) / 10957866939164430172166027544459999018177711028217177128620222960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix81,
    observedFirstWeekMeanLoss81,
    observedFirstWeekMeanPredictor81]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix83 :
    (∑ i ∈ Finset.range 83,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((9897067259450862341929203102316461022214202342013076805174823939452495647155852863918171629 : Rat) / 10957866939164430172166027544459999018177711028217177128620222960000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix82,
    observedFirstWeekMeanLoss82,
    observedFirstWeekMeanPredictor82]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix84 :
    (∑ i ∈ Finset.range 84,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((68186894171416884774217454132573240679061703520538456094460261468928599922646584490906990512181 : Rat) / 75488745343903759456051763753784933236226251273388133239064715971440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix83,
    observedFirstWeekMeanLoss83,
    observedFirstWeekMeanPredictor83]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix85 :
    (∑ i ∈ Finset.range 85,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((68398191937757076112348190210279530524836352797501772426472896160894662265922703698099705047181 : Rat) / 75488745343903759456051763753784933236226251273388133239064715971440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix84,
    observedFirstWeekMeanLoss84,
    observedFirstWeekMeanPredictor84]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix86 :
    (∑ i ∈ Finset.range 86,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((68402035975979119120533354102376355633451727723467490382479268113303931167117852763222370352781 : Rat) / 75488745343903759456051763753784933236226251273388133239064715971440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix85,
    observedFirstWeekMeanLoss85,
    observedFirstWeekMeanPredictor85]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix87 :
    (∑ i ∈ Finset.range 87,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((69647864704794094842563218469945512434461032805755357581959600877763341057268922544636319792781 : Rat) / 75488745343903759456051763753784933236226251273388133239064715971440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix86,
    observedFirstWeekMeanLoss86,
    observedFirstWeekMeanPredictor86]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix88 :
    (∑ i ∈ Finset.range 88,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((69896474286985654364746681556532605977081746698440467992871185480068561934281892930212808752781 : Rat) / 75488745343903759456051763753784933236226251273388133239064715971440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix87,
    observedFirstWeekMeanLoss87,
    observedFirstWeekMeanPredictor87]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix89 :
    (∑ i ∈ Finset.range 89,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((69898871639288184875329551758952088556831014347571498020936014432803103475997868597807102752781 : Rat) / 75488745343903759456051763753784933236226251273388133239064715971440000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix88,
    observedFirstWeekMeanLoss88,
    observedFirstWeekMeanPredictor88]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix90 :
    (∑ i ∈ Finset.range 90,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((559806013474652990470042837675055578409405547698845996314142355239984319674294462380119696601418301 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix89,
    observedFirstWeekMeanLoss89,
    observedFirstWeekMeanPredictor89]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix91 :
    (∑ i ∈ Finset.range 91,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((564143682162878790841995977581396005207263674011405054135817448861993230374093417944987965963680701 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix90,
    observedFirstWeekMeanLoss90,
    observedFirstWeekMeanPredictor90]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix92 :
    (∑ i ∈ Finset.range 92,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((589529742064818620591508701489049938958570897785265104325789765425989867131791547195860511482640701 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix91,
    observedFirstWeekMeanLoss91,
    observedFirstWeekMeanPredictor91]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix93 :
    (∑ i ∈ Finset.range 93,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((590109945758919881425092455106588730366114321807726507926148910133278744779927822785402969258015701 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix92,
    observedFirstWeekMeanLoss92,
    observedFirstWeekMeanPredictor92]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix94 :
    (∑ i ∈ Finset.range 94,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((605500711171701767986039828661192383399131027336041335819434130177459464700568878290843515393055701 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix93,
    observedFirstWeekMeanLoss93,
    observedFirstWeekMeanPredictor93]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix95 :
    (∑ i ∈ Finset.range 95,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((613954864920300087908345403940001043663797474497593820320240161845078552427108484684111781309215701 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix94,
    observedFirstWeekMeanLoss94,
    observedFirstWeekMeanPredictor94]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix96 :
    (∑ i ∈ Finset.range 96,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((614013062614842352136450520240442860746577922614050593876263225722768025473417109366929931596790101 : Rat) / 597946351869061678651386020693730456164148136336507403386631615209776240000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix95,
    observedFirstWeekMeanLoss95,
    observedFirstWeekMeanPredictor95]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix97 :
    (∑ i ∈ Finset.range 97,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((4917299566168070279698791562756817551382348543352352181323732544056260106146455341693905282235622683 : Rat) / 4783570814952493429211088165549843649313185090692059227093052921678209920000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix96,
    observedFirstWeekMeanLoss96,
    observedFirstWeekMeanPredictor96]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix98 :
    (∑ i ∈ Finset.range 98,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((52283355720587987303045852543263827833645169602088589336750735897327210219398873189867738781471583744347 : Rat) / 45008617797888010675447128549658478896387758518321585267718534940070277137280000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix97,
    observedFirstWeekMeanLoss97,
    observedFirstWeekMeanPredictor97]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix99 :
    (∑ i ∈ Finset.range 99,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((52302613081831484142404017618587752686368450315561892878962382368645668626907536239661324212404631264347 : Rat) / 45008617797888010675447128549658478896387758518321585267718534940070277137280000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix98,
    observedFirstWeekMeanLoss98,
    observedFirstWeekMeanPredictor98]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix100 :
    (∑ i ∈ Finset.range 100,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((52333239963824406670479821898693949344253156434861476383458703760350439577420418926239594783820395744347 : Rat) / 45008617797888010675447128549658478896387758518321585267718534940070277137280000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix99,
    observedFirstWeekMeanLoss99,
    observedFirstWeekMeanPredictor99]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix101 :
    (∑ i ∈ Finset.range 101,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((10537111093063623905332567383978507377442521890516040793426994293647705254868596511662852920600451960799 : Rat) / 9001723559577602135089425709931695779277551703664317053543706988014055427456000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix100,
    observedFirstWeekMeanLoss100,
    observedFirstWeekMeanPredictor100]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix102 :
    (∑ i ∈ Finset.range 102,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((108243149730391042360506709957485351019313063403269451087733458939998989456673864071318993492858915651086599 : Rat) / 91826582031251119380047231667013228644410304929079698263199354984731379415478656000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix101,
    observedFirstWeekMeanLoss101,
    observedFirstWeekMeanPredictor101]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix103 :
    (∑ i ∈ Finset.range 103,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((109751150837696414632603111517654472183106932386314052082457581982215904556312725082605024263532951471470599 : Rat) / 91826582031251119380047231667013228644410304929079698263199354984731379415478656000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix102,
    observedFirstWeekMeanLoss102,
    observedFirstWeekMeanPredictor102]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix104 :
    (∑ i ∈ Finset.range 104,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1164733899401301332204503295751789456720163178237870005210189642344285744643933730649773879626323297403075680791 : Rat) / 974188208769543125502921080755343342688548924992606518874281957033015204218813061504000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix103,
    observedFirstWeekMeanLoss103,
    observedFirstWeekMeanPredictor103]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix105 :
    (∑ i ∈ Finset.range 105,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1167397821620741485004850515263233383409538129565808123263059788735786054241035370888309834642631522062877280791 : Rat) / 974188208769543125502921080755343342688548924992606518874281957033015204218813061504000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix104,
    observedFirstWeekMeanLoss104,
    observedFirstWeekMeanPredictor104]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix106 :
    (∑ i ∈ Finset.range 106,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1168015346409651944149058043182925095928009489471144220718994587340281730932308659504191163379846674178362336791 : Rat) / 974188208769543125502921080755343342688548924992606518874281957033015204218813061504000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix105,
    observedFirstWeekMeanLoss105,
    observedFirstWeekMeanPredictor105]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix107 :
    (∑ i ∈ Finset.range 107,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1168332320117420595538206715612351257013182863308293828312708962237349855962097358013392940548663565660496192791 : Rat) / 974188208769543125502921080755343342688548924992606518874281957033015204218813061504000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix106,
    observedFirstWeekMeanLoss106,
    observedFirstWeekMeanPredictor106]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix108 :
    (∑ i ∈ Finset.range 108,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((13414108878476455788670978720466173441425800296574842805872772343404911464603335344021042063238001250946291605664159 : Rat) / 11153480802202499243882943453567925930441196642240352034591654126070991073101190741159296000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix107,
    observedFirstWeekMeanLoss107,
    observedFirstWeekMeanPredictor107]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix109 :
    (∑ i ∈ Finset.range 109,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((40247691417050315503454953432147477059661875126763201477502521787865195873226941851437711449484779098625118745600477 : Rat) / 33460442406607497731648830360703777791323589926721056103774962378212973219303572223477888000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix108,
    observedFirstWeekMeanLoss108,
    observedFirstWeekMeanPredictor108]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix110 :
    (∑ i ∈ Finset.range 110,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((478541217159312942148326394359387794502383098807467501555507821790703921931419740142560720452817632234782509766769699237 : Rat) / 397543516232903680549719753515521583938715571919372867568950328015548334818545741587140787328000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix109,
    observedFirstWeekMeanLoss109,
    observedFirstWeekMeanPredictor109]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix111 :
    (∑ i ∈ Finset.range 111,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((479313263681873546940925500367394529192102674558883091326788148599044896199201807390927984704163134431956706438178037157 : Rat) / 397543516232903680549719753515521583938715571919372867568950328015548334818545741587140787328000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix110,
    observedFirstWeekMeanLoss110,
    observedFirstWeekMeanPredictor110]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix112 :
    (∑ i ∈ Finset.range 112,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((479470124896362384061829036185774053371957207888090098357196925531512508598947772483596506632503063124266012898609525157 : Rat) / 397543516232903680549719753515521583938715571919372867568950328015548334818545741587140787328000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix111,
    observedFirstWeekMeanLoss111,
    observedFirstWeekMeanPredictor111]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix113 :
    (∑ i ∈ Finset.range 113,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((479724372653556383739481546954294172017679670061154999952585115303236480009480259347937910595564707242166370155292689657 : Rat) / 397543516232903680549719753515521583938715571919372867568950328015548334818545741587140787328000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix112,
    observedFirstWeekMeanLoss112,
    observedFirstWeekMeanPredictor112]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix114 :
    (∑ i ∈ Finset.range 114,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6209319261381991567677109271779436786480302809972738428328955247964242792652358843179284931071082708731054953382353002678233 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix113,
    observedFirstWeekMeanLoss113,
    observedFirstWeekMeanPredictor113]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix115 :
    (∑ i ∈ Finset.range 115,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6254730505316695186084906702419537804180270253543782649300440759441023543838114029372350085332648771805456019736963101366233 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix114,
    observedFirstWeekMeanLoss114,
    observedFirstWeekMeanPredictor114]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix116 :
    (∑ i ∈ Finset.range 116,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6292578408370617835174486675435395569443772607438099832943345124233624731198482880679229866728653312662559083195610903959513 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix115,
    observedFirstWeekMeanLoss115,
    observedFirstWeekMeanPredictor115]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix117 :
    (∑ i ∈ Finset.range 117,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6292819246913411893502989639202932257098024062238344318779142246196331061591642524323678982703832698951789338233931308567513 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix116,
    observedFirstWeekMeanLoss116,
    observedFirstWeekMeanPredictor116]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix118 :
    (∑ i ∈ Finset.range 118,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6307015811244385183402514237502809848614279917497214701517114549703057625467014130829244773457077940555425364242103094935513 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix117,
    observedFirstWeekMeanLoss117,
    observedFirstWeekMeanPredictor117]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix119 :
    (∑ i ∈ Finset.range 119,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6325950362302311345796939026034534126419565739913351686578666654764695481390483901145522738851200187858669185149359358135513 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix118,
    observedFirstWeekMeanLoss118,
    observedFirstWeekMeanPredictor118]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix120 :
    (∑ i ∈ Finset.range 120,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6777098457765655897299677724924103648373876308231746739611434438554747662322375421416836477031946598166421008459558490423513 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix119,
    observedFirstWeekMeanLoss119,
    observedFirstWeekMeanPredictor119]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix121 :
    (∑ i ∈ Finset.range 121,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((6779690179667206735456467308648076541592889736758688104354527939048072252936898146014819561822857514612607332159930708344233 : Rat) / 5076233158777947096939371532639695105313459137838472145987926738430536687298010574326200713391232000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix120,
    observedFirstWeekMeanLoss120,
    observedFirstWeekMeanPredictor120]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix122 :
    (∑ i ∈ Finset.range 122,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((870961332773684047089537040875804376685314747369381737244577065038164830905702483695455915664200243657921086939556434405844193 : Rat) / 614224212212131598729663955449403107742928555678455129664539135350094939163059279493470286320339072000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix121,
    observedFirstWeekMeanLoss121,
    observedFirstWeekMeanPredictor121]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix123 :
    (∑ i ∈ Finset.range 123,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((871402169462598276377876256855467310248833143448572770044203945911062283284307436721778749003336404545136777857748298841044193 : Rat) / 614224212212131598729663955449403107742928555678455129664539135350094939163059279493470286320339072000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix122,
    observedFirstWeekMeanLoss122,
    observedFirstWeekMeanPredictor122]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix124 :
    (∑ i ∈ Finset.range 124,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((902478609442806728969187272878688787796314710101852470868281888110917187136785538969456882899850368027835345292077349749844193 : Rat) / 614224212212131598729663955449403107742928555678455129664539135350094939163059279493470286320339072000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix123,
    observedFirstWeekMeanLoss123,
    observedFirstWeekMeanPredictor123]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix125 :
    (∑ i ∈ Finset.range 125,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((907368988070848962885986304862827115354669248188686960746585689314651078958370386536057514992917954545411947784018386643932193 : Rat) / 614224212212131598729663955449403107742928555678455129664539135350094939163059279493470286320339072000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix124,
    observedFirstWeekMeanLoss124,
    observedFirstWeekMeanPredictor124]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix126 :
    (∑ i ∈ Finset.range 126,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((113591772215688397917883896539310266978230589946796007538075598552555601981858525269239540781801332162364155649693176349115340829 : Rat) / 76778026526516449841207994431175388467866069459806891208067391918761867395382409936683785790042384000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix125,
    observedFirstWeekMeanLoss125,
    observedFirstWeekMeanPredictor125]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix127 :
    (∑ i ∈ Finset.range 127,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((118404229599154891707409744719029561985571971398250181226672706160137868661323570158219216977398971846294212016386983825631340829 : Rat) / 76778026526516449841207994431175388467866069459806891208067391918761867395382409936683785790042384000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix126,
    observedFirstWeekMeanLoss126,
    observedFirstWeekMeanPredictor126]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix128 :
    (∑ i ∈ Finset.range 128,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1917737690918800827344713154832360304296775319818335534964553192246132904170236909670145130957928578841750903305301521352738712230941 : Rat) / 1238352789846183819488843742180427840598211834317225348294918964257710159220122889868772781007593611536000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix127,
    observedFirstWeekMeanLoss127,
    observedFirstWeekMeanPredictor127]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix129 :
    (∑ i ∈ Finset.range 129,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((8202590018521504907262174231770790385426000742799581888554087762468344791455463534859959629919577812196916941980031560597779664939389 : Rat) / 4953411159384735277955374968721711362392847337268901393179675857030840636880491559475091124030374446144000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix128,
    observedFirstWeekMeanLoss128,
    observedFirstWeekMeanPredictor128]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix130 :
    (∑ i ∈ Finset.range 130,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((192524754028536296316794000498068236151486093138688688358151469281631064729977415926291559743328249978050643703778757448874875928823 : Rat) / 115195608357784541347799417877249101450996449703927939376271531558856758997220733941281188930938940608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix129,
    observedFirstWeekMeanLoss129,
    observedFirstWeekMeanPredictor129]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix131 :
    (∑ i ∈ Finset.range 131,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((192535262216477533751662895015580856287213570650917226527936978984569943429428464906241467890365392035547020267510013241666107928823 : Rat) / 115195608357784541347799417877249101450996449703927939376271531558856758997220733941281188930938940608000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix130,
    observedFirstWeekMeanLoss130,
    observedFirstWeekMeanPredictor130]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix132 :
    (∑ i ∈ Finset.range 132,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3356288884287259772394528801964175924994469040935546542284233987748726679297779511093683121386285349135189211359792594821948739158531503 : Rat) / 1976871835027940514069585810191471830000550073369107367636195753081540841151305015166326483243843159773888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix131,
    observedFirstWeekMeanLoss131,
    observedFirstWeekMeanPredictor131]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix133 :
    (∑ i ∈ Finset.range 133,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3392260535612238161307614639023074883849151791956694589396170543620626101160672717441186171314648428855651156517334404162415767046531503 : Rat) / 1976871835027940514069585810191471830000550073369107367636195753081540841151305015166326483243843159773888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix132,
    observedFirstWeekMeanLoss132,
    observedFirstWeekMeanPredictor132]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix134 :
    (∑ i ∈ Finset.range 134,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3395208692698251211154360933194182065944469090964034603320283084783025995697671674594943210072499841172984461189039570742850124998531503 : Rat) / 1976871835027940514069585810191471830000550073369107367636195753081540841151305015166326483243843159773888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix133,
    observedFirstWeekMeanLoss133,
    observedFirstWeekMeanPredictor133]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix135 :
    (∑ i ∈ Finset.range 135,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3395245386689515825241023324759147818516039738840296114531896609169237920179872965369349102034073572810307627952411044042338704246531503 : Rat) / 1976871835027940514069585810191471830000550073369107367636195753081540841151305015166326483243843159773888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix134,
    observedFirstWeekMeanLoss134,
    observedFirstWeekMeanPredictor134]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix136 :
    (∑ i ∈ Finset.range 136,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3397669956174585476371684860738589114702270236111384803149411880823133633830234825681737706234647540369845514274712071381743233099011503 : Rat) / 1976871835027940514069585810191471830000550073369107367636195753081540841151305015166326483243843159773888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix135,
    observedFirstWeekMeanLoss135,
    observedFirstWeekMeanPredictor135]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix137 :
    (∑ i ∈ Finset.range 137,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3399314424021184197125314788773498936288412869635627441164836466324144725556912240826062902100918074363448676325697300479495685862011503 : Rat) / 1976871835027940514069585810191471830000550073369107367636195753081540841151305015166326483243843159773888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix136,
    observedFirstWeekMeanLoss136,
    observedFirstWeekMeanPredictor136]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix138 :
    (∑ i ∈ Finset.range 138,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((64111553654808519346890014333456406507563665444509951458742445260117084401246368750772773648767771677624498322237585084073606483141725899807 : Rat) / 37103907471639415508572056071483734777280324327064776183163758089587440047568843829656781764003692265796103872000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix137,
    observedFirstWeekMeanLoss137,
    observedFirstWeekMeanPredictor137]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix139 :
    (∑ i ∈ Finset.range 139,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((64236625257427420563190428252234081473972892487788611667204366599792042098623351865233030591659706547015748315330036325754228501030797899807 : Rat) / 37103907471639415508572056071483734777280324327064776183163758089587440047568843829656781764003692265796103872000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix138,
    observedFirstWeekMeanLoss138,
    observedFirstWeekMeanPredictor138]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix140 :
    (∑ i ∈ Finset.range 140,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1244743270412977579243676347523220597067866266390710798655530571729991957065593463225238855673537884451494146648295609542689166901172249422171047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix139,
    observedFirstWeekMeanLoss139,
    observedFirstWeekMeanPredictor139]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix141 :
    (∑ i ∈ Finset.range 141,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1248675709398767437440472120326313375980761072264948607474628003444607219570536164733013562541792507845804621629152027461228125765218546554171047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix140,
    observedFirstWeekMeanLoss140,
    observedFirstWeekMeanPredictor140]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix142 :
    (∑ i ∈ Finset.range 142,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1254683276517784432794533009334382038457927788263795329429236139204654827568584051484856847136264378792294606285404177030685383940726344762171047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix141,
    observedFirstWeekMeanLoss141,
    observedFirstWeekMeanPredictor141]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix143 :
    (∑ i ∈ Finset.range 143,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1254743731379247079956843789685005497238965246780705059218580361349716364560094645593927175227545393514512906568405507315995786303474372074171047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix142,
    observedFirstWeekMeanLoss142,
    observedFirstWeekMeanPredictor142]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix144 :
    (∑ i ∈ Finset.range 144,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1266589528230670878913439859573053767745524211034413107545685232607341068757222227442589609662078479264621845816568855068088583144272308906171047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix143,
    observedFirstWeekMeanLoss143,
    observedFirstWeekMeanPredictor143]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix145 :
    (∑ i ∈ Finset.range 145,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1271997665667070296322074581531042442253653278609514637777510334027885859862173470902367388907898931433420982651138928836071064992745646162921047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix144,
    observedFirstWeekMeanLoss144,
    observedFirstWeekMeanPredictor144]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix146 :
    (∑ i ∈ Finset.range 146,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1272348046636431588389685325700611799646540456248875755541011559014779587475073184350152777238478768429069104163640517437519050335755369022441047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix145,
    observedFirstWeekMeanLoss145,
    observedFirstWeekMeanPredictor145]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix147 :
    (∑ i ∈ Finset.range 147,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1280563085108864741274426252360360283005398773067297793341588026188175521840606453314208425257760329996542207957630704275499977609066588734441047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix146,
    observedFirstWeekMeanLoss146,
    observedFirstWeekMeanPredictor146]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix148 :
    (∑ i ∈ Finset.range 148,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1284551079274840643198101948030885419197843924204527549364403594725530649838965034209836811761816778945857926139193581489384250313543969342441047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix147,
    observedFirstWeekMeanLoss147,
    observedFirstWeekMeanPredictor147]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix149 :
    (∑ i ∈ Finset.range 149,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((1286699810955093226609535829616354104025645470131118847591443595296130583050248082765092570211623808734886897840531510826178578767513957950441047 : Rat) / 716884596259545147041120695357137239631833146323218540634906970048918929159077631632798680462315338267446522910912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix148,
    observedFirstWeekMeanLoss148,
    observedFirstWeekMeanPredictor148]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix150 :
    (∑ i ∈ Finset.range 150,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((28582704896014541202220627935782665039956346583405610105390820233057877904355858418465669133671340406310975562148335521494236854225418898543053684447 : Rat) / 15915554921558161809459920557623803857066327681521774820635569642056049146260682499879763504943862824875580255145157312000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix149,
    observedFirstWeekMeanLoss149,
    observedFirstWeekMeanPredictor149]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix151 :
    (∑ i ∈ Finset.range 151,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((28723201656578101479623172533416067677707278362341989341170126376943801159092505705901825319743159469344882475089925731271597533892503245684485671647 : Rat) / 15915554921558161809459920557623803857066327681521774820635569642056049146260682499879763504943862824875580255145157312000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix150,
    observedFirstWeekMeanLoss150,
    observedFirstWeekMeanPredictor150]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix152 :
    (∑ i ∈ Finset.range 152,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((658196953006325992729795275462845632218185238267049732878067658809556804414556145775963567830176526470904495114373526600259697294356291798992476391223247 : Rat) / 362890567766447647417495648634380351744969337466377987685311623408519976583889821679758487676225016269988105397564731870912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix151,
    observedFirstWeekMeanLoss151,
    observedFirstWeekMeanPredictor151]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix153 :
    (∑ i ∈ Finset.range 153,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((660331405811883705324722114918980237698382036137649566839887234019063416867319883398008297193538893754093725069373881984442282544440406676801370066223247 : Rat) / 362890567766447647417495648634380351744969337466377987685311623408519976583889821679758487676225016269988105397564731870912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix152,
    observedFirstWeekMeanLoss152,
    observedFirstWeekMeanPredictor152]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix154 :
    (∑ i ∈ Finset.range 154,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((661250705676730420841646278162583332482536965807605985103639859580815426500404285628124409413112532482466330631371147295365600451546289124208526994223247 : Rat) / 362890567766447647417495648634380351744969337466377987685311623408519976583889821679758487676225016269988105397564731870912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix153,
    observedFirstWeekMeanLoss153,
    observedFirstWeekMeanPredictor153]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix155 :
    (∑ i ∈ Finset.range 155,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((662034433858737056151125376084905362778673253228603394241029277919972791245745734336028060197007235371480587219631858370637130372650330658869189442223247 : Rat) / 362890567766447647417495648634380351744969337466377987685311623408519976583889821679758487676225016269988105397564731870912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix154,
    observedFirstWeekMeanLoss154,
    observedFirstWeekMeanPredictor154]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix156 :
    (∑ i ∈ Finset.range 156,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((662824604337768088940478433731615699161131327787338311165444574661537935856601292861091527060776370915154312308493801243160819713738896285562971642543247 : Rat) / 362890567766447647417495648634380351744969337466377987685311623408519976583889821679758487676225016269988105397564731870912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix155,
    observedFirstWeekMeanLoss155,
    observedFirstWeekMeanPredictor155]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix157 :
    (∑ i ∈ Finset.range 157,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((662840312720430909614379344072085457172817396401463982278471182873500792005199496289965383226509054968277347622489544051041676978768826964581459130543247 : Rat) / 362890567766447647417495648634380351744969337466377987685311623408519976583889821679758487676225016269988105397564731870912000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix156,
    observedFirstWeekMeanLoss156,
    observedFirstWeekMeanPredictor156]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix158 :
    (∑ i ∈ Finset.range 158,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16427500974789541911771505825830163905724916218411243819899788273994002483809199527224698462657065787985828914432432889070582864652157767260079469508952495303 : Rat) / 8944889604875168061193850243188841290161749199208751018455246205396608902816300214584366962731270426038936809944573075886109888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix157,
    observedFirstWeekMeanLoss157,
    observedFirstWeekMeanPredictor157]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix159 :
    (∑ i ∈ Finset.range 159,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16447980531526892379888837735390204115450522227743309082688814120564996674166219356041305201595783578017422911606390569121505777097311572551300934720024495303 : Rat) / 8944889604875168061193850243188841290161749199208751018455246205396608902816300214584366962731270426038936809944573075886109888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix158,
    observedFirstWeekMeanLoss158,
    observedFirstWeekMeanPredictor158]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix160 :
    (∑ i ∈ Finset.range 160,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16468458259363756850532900537973000052626929956626279098699712998606415564762148768806358103036570033778983443540979328109490385328757472992213681440024495303 : Rat) / 8944889604875168061193850243188841290161749199208751018455246205396608902816300214584366962731270426038936809944573075886109888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix159,
    observedFirstWeekMeanLoss159,
    observedFirstWeekMeanPredictor159]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix161 :
    (∑ i ∈ Finset.range 161,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16481298731284615415537281662921904001847014265324658493037433260238345235222678023466065879052472587733703610017274799247502274035173535868525504122793245303 : Rat) / 8944889604875168061193850243188841290161749199208751018455246205396608902816300214584366962731270426038936809944573075886109888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix160,
    observedFirstWeekMeanLoss160,
    observedFirstWeekMeanPredictor160]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix162 :
    (∑ i ∈ Finset.range 162,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16481777974448726958889372301813029570033688847010671808284628006240493554211755669629217854744152377440445887079581444861229842171909395419491120319593245303 : Rat) / 8944889604875168061193850243188841290161749199208751018455246205396608902816300214584366962731270426038936809944573075886109888000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix161,
    observedFirstWeekMeanLoss161,
    observedFirstWeekMeanPredictor161]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix163 :
    (∑ i ∈ Finset.range 163,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((618769803405531998068798034792716997107664814876786809573743119600358088412514260944803005806955652339223532806135989313649742329383042029222004968306712789 : Rat) / 331292207587969187451624083081068195931916637007731519202046155755429959363566674614235813434491497260701363331280484292078144000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix162,
    observedFirstWeekMeanLoss162,
    observedFirstWeekMeanPredictor162]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix164 :
    (∑ i ∈ Finset.range 164,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16463439510887576479993798868503266762365087911375829246867800458595120694630909607704534348895286255809907618795368379486732612324500600519889826248205436090941 : Rat) / 8802102663404753341402200263380900897715093128658418733679164312266018590330602977825631327141004590719574522348791187156224207936000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix163,
    observedFirstWeekMeanLoss163,
    observedFirstWeekMeanPredictor163]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix165 :
    (∑ i ∈ Finset.range 165,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16550259101039222522319057079351491645544746233027428784206646205117008543854149349376394161132721673582151309197332282697844412943680184356254808805542012090941 : Rat) / 8802102663404753341402200263380900897715093128658418733679164312266018590330602977825631327141004590719574522348791187156224207936000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix164,
    observedFirstWeekMeanLoss164,
    observedFirstWeekMeanPredictor164]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix166 :
    (∑ i ∈ Finset.range 166,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16559391965619579559295296920622478370000831933805146435530892386402817149361872369792538197073073959649222200143124442153240225693728888371793939126626225850941 : Rat) / 8802102663404753341402200263380900897715093128658418733679164312266018590330602977825631327141004590719574522348791187156224207936000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix165,
    observedFirstWeekMeanLoss165,
    observedFirstWeekMeanPredictor165]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix167 :
    (∑ i ∈ Finset.range 167,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((16689095773880151520924381595494807399816225852028322670731960516682077593818716902381036786755256477415898701507720540226762043802228876176282964403778369850941 : Rat) / 8802102663404753341402200263380900897715093128658418733679164312266018590330602977825631327141004590719574522348791187156224207936000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix166,
    observedFirstWeekMeanLoss166,
    observedFirstWeekMeanPredictor166]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix168 :
    (∑ i ∈ Finset.range 168,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((468702012907671136658902352881487849729588304284509605019796322135969304589527538948232833479402281715053793470751950732881835934596201835486728639018438889956893549 : Rat) / 245481841179695165938365963145429945136376232265154640063578213504786992465730186448579032082635477030578213853785437418599936935127104000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix167,
    observedFirstWeekMeanLoss167,
    observedFirstWeekMeanPredictor167]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix169 :
    (∑ i ∈ Finset.range 169,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((469247385100127466699682016310657168132048780014507180455274197417422487434717094028340010950990139479492142899414034581656126349630744344185207707849796005192893549 : Rat) / 245481841179695165938365963145429945136376232265154640063578213504786992465730186448579032082635477030578213853785437418599936935127104000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix168,
    observedFirstWeekMeanLoss168,
    observedFirstWeekMeanPredictor168]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix170 :
    (∑ i ∈ Finset.range 170,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((79348162469749134709957182699083602376909981615034934478476476850501388727456525152254804936072895771151232724640720269979163674811784486269003478537256832060255009781 : Rat) / 41486431159368483043583847771577660728047583252811134170744718082309001726708401509809856421965395618167718141289738923743389342036480576000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix169,
    observedFirstWeekMeanLoss169,
    observedFirstWeekMeanPredictor169]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix171 :
    (∑ i ∈ Finset.range 171,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((79956597045216949607426020694848931927683643348301893750671260130599763051302850765649899134776504564441978386575677674398780299506714108560892331013807780751762849781 : Rat) / 41486431159368483043583847771577660728047583252811134170744718082309001726708401509809856421965395618167718141289738923743389342036480576000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix170,
    observedFirstWeekMeanLoss170,
    observedFirstWeekMeanPredictor170]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix172 :
    (∑ i ∈ Finset.range 172,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((79958531400982616005183599000233085718740930445729114240109316778627931804515745750411545658611162329079294585583480019703435784197220945020612298583548771139538849781 : Rat) / 41486431159368483043583847771577660728047583252811134170744718082309001726708401509809856421965395618167718141289738923743389342036480576000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix171,
    observedFirstWeekMeanLoss171,
    observedFirstWeekMeanPredictor171]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix173 :
    (∑ i ∈ Finset.range 173,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((3439348930577578333142735859674622439600371097589853273335914548221420035853061693565394892369862386492684250625800979192587832919017855441187650441845441293589558540583 : Rat) / 1783916539852844770874105454177839411306046079870878769342022877539287074248461264921823826144512011581211880075458773720965741707568664768000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix172,
    observedFirstWeekMeanLoss172,
    observedFirstWeekMeanPredictor172]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix174 :
    (∑ i ∈ Finset.range 174,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((102940910942891986965771520692908635556333555215073731523677482767136287069122675622784623480497266357651379676971676212158200788803312784930179848510032872246498994009108607 : Rat) / 53390838121255791147491102138088555740978653124455530687637402701873322845182197197845265292679099994614090358778405638694783683565822567841472000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix173,
    observedFirstWeekMeanLoss173,
    observedFirstWeekMeanPredictor173]
  norm_num [ratToReal]

theorem observedFirstWeekMeanQuadraticPrefix175 :
    (∑ i ∈ Finset.range 175,
      (observedTrajectoryScore
          (monitorBrierScore firstWeekMean) i replayPath -
        forwardPredictorProcess
          (observedTrajectoryScore
            (monitorBrierScore firstWeekMean)) i replayPath) ^ 2) =
      ratToReal ((103160652766924583881845251183779567698165965283795675676120359165417196450433776537693558947680037870920390038380907527266793910954865843697835715149506231483203498521108607 : Rat) / 53390838121255791147491102138088555740978653124455530687637402701873322845182197197845265292679099994614090358778405638694783683565822567841472000000000000000000000000000000) := by
  rw [Finset.sum_range_succ,
    observedFirstWeekMeanQuadraticPrefix174,
    observedFirstWeekMeanLoss174,
    observedFirstWeekMeanPredictor174]
  norm_num [ratToReal]

end

end FormalSLT.Applications.GJPBrierMonitorReplayPathData
