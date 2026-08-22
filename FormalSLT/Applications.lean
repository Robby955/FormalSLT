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
import FormalSLT.Applications.ControlledQueuePersistenceConfidence
import FormalSLT.Applications.ControlledQueueTargetPolicyScores
import FormalSLT.Applications.ControlledQueueContraction
import FormalSLT.Applications.ControlledQueueOPECatalog
import FormalSLT.Applications.ControlledQueueStructuredOPE
import FormalSLT.Applications.ControlledQueueInvariantRisk
import FormalSLT.Applications.ControlledQueueKnownKernelReceipt
import FormalSLT.Applications.ControlledQueueRefreshSensitivity
import FormalSLT.Applications.ControlledQueueSharpStructuredOPE
import FormalSLT.Applications.ControlledQueueSharpStructuredReceiptCore

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
ratio-cap assumptions. It also supplies the universal centered row-risk
envelope `D = 1` for every generated fixed Brier score and every reference
PMF. `ControlledQueueContraction` certifies each candidate's uniform
minorization and target-policy contraction factor.
`ControlledQueuePersistenceConfidence` embeds the three candidates in an
arbitrary-parameter refresh family and gives one scalar time-uniform outer-mass
event whose hit-probability discrepancy is exactly every physical-row TV
discrepancy.
`ControlledQueueOPECatalog` combines the earlier deterministic receipts into a
twelve-atom, fixed-nominal-candidate event for any depth fixed before the event.
`ControlledQueueStructuredOPE` intersects preallocated candidate--depth OPE
events with the scalar persistence event. Its common outer-mass event permits
pathwise selection from all three candidates, seven generated depths, four
admissible risk tilts, four admissible persistence tilts, and arbitrary
twelve-hypothesis posterior PMFs.
`ControlledQueueInvariantRisk` supplies one explicit invariant PMF, identifies
it with the catalog's canonical witness by contraction uniqueness, and evaluates
one exact stationary Brier risk. `ControlledQueueKnownKernelReceipt` gives a
fixed-initial failure-mass theorem and an exact `< 0.07` selected-risk endpoint
conditional on both the aligned suffix-histogram premise and the
theorem-produced event inequality. `ControlledQueueRefreshSensitivity` proves
the exact affine drift identity for the queue refresh family, and
`ControlledQueueSharpStructuredOPE` combines it with the risk and persistence
events under the prospectively frozen constants.
`ControlledQueueSharpStructuredReceiptCore` reduces any matching physical
transition histogram to the preregistered affine-Bessel primary endpoint,
without containing future counts. These modules do not prove that any named
trace satisfies the good event or evaluate the prospective sharp endpoint on
fresh data.
-/
