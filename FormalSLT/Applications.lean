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

/-!
# FormalSLT applications

Concrete, reproducible models used to exercise the library's statistical
certificates.  Application modules are public and checked, but they are not
part of the small v0.2 stable-endpoint promise.

`ControlledQueueData` is an opt-in generated preprocessing table.  It is not a
statistical certificate and makes no theorem-produced good-path claim.
-/
