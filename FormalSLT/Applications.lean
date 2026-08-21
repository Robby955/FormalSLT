/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadModel
import FormalSLT.Applications.RandomRefreshLoadCertificate
import FormalSLT.Applications.RandomRefreshLoadPath
import FormalSLT.Applications.RandomRefreshLoadReceipt
import FormalSLT.Applications.RandomRefreshLoadAdaptiveSelection
import FormalSLT.Applications.RandomRefreshLoadBaselines
import FormalSLT.Applications.RandomRefreshLoadOracleCertificate
import FormalSLT.Applications.ControlledQueueData
import FormalSLT.Applications.ControlledQueueReindex
import FormalSLT.Applications.ControlledQueueTypedModel
import FormalSLT.Applications.ControlledQueueTargetPolicyScores
import FormalSLT.Applications.ControlledQueueContraction

/-!
# FormalSLT applications

Concrete, reproducible models used to exercise the library's statistical
certificates.  Application modules are public and checked, but they are not
part of the small v0.2 stable-endpoint promise.

`ControlledQueueData` is an opt-in generated preprocessing table,
`ControlledQueueReindex` connects its row order to controlled action--state
observations, and `ControlledQueueTypedModel` turns the exact rational kernel
and policy tables into typed PMFs.  `ControlledQueueTargetPolicyScores`
reconstructs fixed Brier scores from the generated forecast and outcome tables,
binds the generated control-cost table, and discharges the static overlap and
ratio-cap assumptions. `ControlledQueueContraction` certifies each candidate's
uniform minorization and target-policy contraction factor. These modules do
not identify a candidate with the true environment or make a theorem-produced
good-path claim.
-/
