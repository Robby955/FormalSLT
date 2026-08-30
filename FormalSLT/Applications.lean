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
import FormalSLT.Applications.ControlledQueueRefreshUniqueness
import FormalSLT.Applications.ControlledQueueOPECatalog
import FormalSLT.Applications.ControlledQueueStructuredOPE
import FormalSLT.Applications.ControlledQueueInvariantRisk
import FormalSLT.Applications.ControlledQueueKnownKernelReceipt
import FormalSLT.Applications.ControlledQueueRefreshSensitivity
import FormalSLT.Applications.ControlledQueueSharpStructuredOPE
import FormalSLT.Applications.ControlledQueueFixedRangePersistenceConfidence
import FormalSLT.Applications.ControlledQueueFixedRangeComparator
import FormalSLT.Applications.ControlledQueueSharpStructuredReceiptCore
import FormalSLT.Applications.ControlledQueueSharpStructuredRetrospectiveReceipt
import FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeReceipt
import FormalSLT.Applications.GJPBrierMonitorReplayReceipt
import FormalSLT.Applications.GJPBrierMonitorReplayPath
import FormalSLT.Applications.GJPBrierMonitorCountableStrategyCertificate

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
`ControlledQueueRefreshUniqueness` proves that every admissible member of this
family induces a target-policy kernel with Dobrushin coefficient at most its
persistence parameter and therefore has a unique invariant PMF.
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
For each fixed true refresh parameter and initial observation,
`ControlledQueueFixedRangePersistenceConfidence` keeps the matched
non-variance-adaptive persistence comparator outside the frozen primary source.
For those same fixed inputs, `ControlledQueueFixedRangeComparator` proves the
event theorem underlying the planned non-variance-adaptive row with the same
selected potential, tilts, and confidence allocation. Its numerical report
remains planned; trace evaluation and named-path event membership stay
separate.
`ControlledQueueSharpStructuredReceiptCore` reduces any matching physical
transition histogram to the preregistered affine-Bessel primary endpoint,
without containing future counts. These modules do not prove that any named
trace satisfies the good event or evaluate the prospective sharp endpoint on
fresh data. `ControlledQueueSharpStructuredRetrospectiveReceipt` separately
evaluates the existing `199999`-transition suffix histogram at a uniform
`1 / 20` event budget, without using the true persistence parameter or exact
stationary risk in the numerical reduction. For each fixed admissible true
parameter under the path law started at `(action = 1, state = 1)`, the
frozen-histogram/risk-failure set has outer mass at most `1 / 20`; this is not
histogram-conditioned or simultaneous-in-parameter coverage.

`BrierMonitorSyntheticProofOfLifeReceipt` reconstructs a synthetic two-segment
forecast stream, checks its Brier arithmetic and observable suffix variation,
and bounds the exact finite-prefix selector conditionally on the theorem's
good-event inequality. It does not prove named-path good-event membership or
make a real-data claim.

`GJPBrierMonitorReplayReceipt` checks the posterior and endpoint arithmetic for
a hash-bound 175-observation replay. `GJPBrierMonitorReplayPath` additionally
reconstructs every Brier loss and forward-predictor residual, instantiates the
finite trajectory theorem, and names an event with outer failure mass at most
`1 / 160` for every supplied history-dependent binary kernel. It does not
assert that the realized path belongs to that event. The preregistered replay
status remains `FAIL`, and the target is monitored-prefix conditional risk,
not future, population, stationary, or deployment risk.

`GJPBrierMonitorCountableStrategyCertificate` is a retrospective application
of the countable sleeping-strategy theorem to a different now-fixed catalog:
one half-tilt strategy at every integer wake, with the reporting posterior at
wake zero. It proves a `< 0.131` summary endpoint and an outer failure-mass
bound of `1 / 160` for that fixed catalog, while leaving the two raw-data
summary equalities as explicit premises. It is not the preregistered GJP
endpoint and does not account for retrospective selection among catalogs.
-/
