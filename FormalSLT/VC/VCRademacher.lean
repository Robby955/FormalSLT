/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.VC.Rademacher

/-!
# Compatibility import: VC-to-Rademacher bridge

The implementation lives in `FormalSLT.VC.Rademacher`. These aliases preserve
the earlier verbose namespace and import path.
-/

namespace FormalSLT.VC.VCRademacher

alias lossVector := FormalSLT.VC.Rademacher.lossVector
alias effectiveClass := FormalSLT.VC.Rademacher.effectiveClass
alias effectiveClass_nonempty := FormalSLT.VC.Rademacher.effectiveClass_nonempty
alias effectiveClass_card_le := FormalSLT.VC.Rademacher.effectiveClass_card_le
alias sup'_eq_sup'_effectiveClass := FormalSLT.VC.Rademacher.sup'_eq_sup'_effectiveClass
alias empiricalRademacherComplexity_le_massart_effective :=
  FormalSLT.VC.Rademacher.empiricalRademacherComplexity_le_massart_effective

end FormalSLT.VC.VCRademacher
