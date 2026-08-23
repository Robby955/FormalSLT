/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueOPECatalog

/-!
# Canonical known-kernel controlled-queue selection

This lightweight module names the single target-policy/predictor atom used by
the known-kernel numerical receipt.  Keeping these indices outside the larger
invariant-risk module lets bounded arithmetic certificate modules reuse the
selection without importing its explicit invariant-law proof object.
-/

namespace FormalSLT.Applications.ControlledQueue

/-- Queue-threshold target-policy row in the generated target catalog. -/
def queueThresholdTargetIndex : TargetPolicyIndex := 1

/-- Nominal-model overload predictor row in the generated fixed catalog. -/
def nominalModelOverloadPredictorIndex : FixedPredictorIndex := 2

/-- The queue-threshold policy paired with the nominal-model overload
predictor inside the fixed twelve-atom OPE catalog. -/
def queueThresholdNominalModelHypothesis : QueueHypothesis :=
  (queueThresholdTargetIndex, nominalModelOverloadPredictorIndex)

end FormalSLT.Applications.ControlledQueue
