/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Rademacher.HighProbability

/-!
# Compatibility import: high-probability Rademacher bounds

The implementation lives in `FormalSLT.Rademacher.HighProbability`. This alias
preserves the earlier verbose namespace and import path.
-/

namespace FormalSLT.Rademacher.HighProbRademacher

alias genGap_highProb_rademacher :=
  FormalSLT.Rademacher.HighProbability.genGap_highProb_rademacher

end FormalSLT.Rademacher.HighProbRademacher
