/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathDataConstantTrainBaseRate
import FormalSLT.Applications.GJPBrierMonitorReplayPathDataFirstWeekMean
import FormalSLT.Applications.GJPBrierMonitorReplayPathDataFinalConsensusMedian
import FormalSLT.Applications.GJPBrierMonitorReplayPathDataExtremizedFinalConsensus

/-!
# Generated GJP Brier replay path data

This aggregator exposes the exact finite proof ledgers for the four
predeclared GJP monitor models. The generator reads the hash-bound
175-observation stream and receipt, then emits small loss, prefix-sum,
forward-predictor, and quadratic-prefix recurrences in a serial import
chain so Lean elaborates one model ledger at a time.

The generated identities assume the supplied stream and receipt pass
the generator's schema, digest, and arithmetic checks. They establish
finite pathwise arithmetic only: they do not prove that the realized
path belongs to a confidence event or identify monitored conditional
risk with future, population, stationary, or deployment risk.
-/
