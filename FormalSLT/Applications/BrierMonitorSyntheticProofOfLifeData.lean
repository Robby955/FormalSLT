/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Mathlib.Data.Rat.Defs

/-!
# Generated synthetic Brier-monitor arithmetic data

This module records deterministic rational outputs from the synthetic
proof-of-life pipeline.  It contains no statistical theorem, no proof that the
path belongs to a theorem-produced good event, and no real-data claim.
-/

namespace FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeData

abbrev inputSha256 : String := "7d2340608d575ac2ff4b1614758433b445c88f7537c57cfeb26fbe8e61d8f1f0"
abbrev receiptSha256 : String := "7073d4c14a2ab694e49f0838da2df7020c57b25ad1018b4f1be68f79d9014a44"
abbrev formalSLTCommit : String := "62d8fc08b00bd41b7f6927f566e622573affacd7"
abbrev horizon : Nat := 512
abbrev selectedWake : Nat := 0
abbrev selectedTiltAtom : Nat := 0
abbrev selectedTilt : ℚ := ((1 : ℚ) / 2)
abbrev posteriorEmpiricalBrierRisk : ℚ :=
  ((1 : ℚ) / 16)
abbrev suffixPredictorQuadraticVariation : ℚ :=
  ((49 : ℚ) / 256)
abbrev selectedBoundaryLower : ℚ :=
  ((45296064325083 : ℚ) / 500000000000000)
abbrev selectedBoundaryUpper : ℚ :=
  ((90592128650167 : ℚ) / 1000000000000000)
abbrev exactSelectionMarginLower : ℚ :=
  ((4210132193597 : ℚ) / 1000000000000000)

end FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeData
