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

abbrev inputSha256 : String := "130eea0a2eec8ddab25d075f2ef62794c5fdce5b6761be4f16feb12651574e5e"
abbrev receiptSha256 : String := "a8d178efe0dd1c11b5433b68224b589e9962152ef648419ad176f1e869da24ff"
abbrev formalSLTCommit : String := "c0b3a5691c3ea3ed6493e914bbccc447f66cbaed"
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
