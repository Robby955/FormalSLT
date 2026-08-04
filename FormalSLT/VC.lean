/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.VC.Dimension
import FormalSLT.VC.PACBridge
import FormalSLT.VC.SauerShelah
import FormalSLT.VC.Rademacher
import FormalSLT.VC.SampleComplexity
import FormalSLT.VC.BinaryVCBridge
import FormalSLT.VC.SampleComplexityBinary
import FormalSLT.VC.BinaryCapstone
import FormalSLT.VC.VCDimension
import FormalSLT.VC.VCRademacher
import FormalSLT.VC.VCSampleComplexity

/-!
# Stable VC imports

This declaration-free umbrella re-exports VC dimension, Sauer--Shelah,
Rademacher, binary classification, and sample-complexity results. The verbose
compatibility paths remain available for downstream code during migration.
-/
