/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Rademacher.Contraction

/-!
# Compatibility import: Rademacher contraction

The implementation lives in `FormalSLT.Rademacher.Contraction`. These aliases
preserve the earlier verbose namespace and import path.
-/

namespace FormalSLT.Rademacher.RademacherContraction

alias comparison_lemma := FormalSLT.Rademacher.Contraction.comparison_lemma
alias comparison_lemma_scaled := FormalSLT.Rademacher.Contraction.comparison_lemma_scaled
alias sum_equiv_perm := FormalSLT.Rademacher.Contraction.sum_equiv_perm
alias one_step_contraction := FormalSLT.Rademacher.Contraction.one_step_contraction
alias contraction_1lip := FormalSLT.Rademacher.Contraction.contraction_1lip
alias finiteSampleScalarContraction_lipschitz :=
  FormalSLT.Rademacher.Contraction.finiteSampleScalarContraction_lipschitz
alias contraction_empirical := FormalSLT.Rademacher.Contraction.contraction_empirical
alias empiricalRademacherComplexity_contraction_lipschitz :=
  FormalSLT.Rademacher.Contraction.empiricalRademacherComplexity_contraction_lipschitz

end FormalSLT.Rademacher.RademacherContraction
