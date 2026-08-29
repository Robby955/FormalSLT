/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayReceipt
import Mathlib.Tactic

/-!
# Generated GJP pathwise Brier score

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

abbrev Model := GJPBrierMonitorReplayData.Model

def ratToReal (q : Rat) : Real := Rat.cast q

def boolValue : Bool → Real
  | false => 0
  | true => 1

def monitorPrediction (model : Model) (n : Nat) : Real :=
  max 0 (min 1 (ratToReal (monitorPredictionQ model n)))

theorem monitorPrediction_mem_Icc (model : Model) (n : Nat) :
    monitorPrediction model n ∈ Set.Icc (0 : Real) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

def monitorBrierScore (model : Model) : TrajectoryScore Bool :=
  fun n _prefix outcome =>
    (monitorPrediction model n - boolValue outcome) ^ 2

theorem monitorBrierScore_mem_Icc :
    ∀ model n u outcome,
      monitorBrierScore model n u outcome ∈ Set.Icc (0 : Real) 1 := by
  intro model n u outcome
  rcases monitorPrediction_mem_Icc model n with ⟨hp0, hp1⟩
  cases outcome <;> simp only [monitorBrierScore, boolValue] <;>
    constructor
  · positivity
  · nlinarith
  · positivity
  · nlinarith

end

end FormalSLT.Applications.GJPBrierMonitorReplayPathData
