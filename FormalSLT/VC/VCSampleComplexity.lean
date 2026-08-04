/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.VC.SampleComplexity

/-!
# Compatibility import: VC sample complexity

The implementation lives in `FormalSLT.VC.SampleComplexity`. These aliases
preserve the five results exposed by the earlier verbose namespace and import
path. The canonical module additionally owns `vc_erm_sample_complexity`.
-/

namespace FormalSLT.VC.VCSampleComplexity

alias vcRademacher_pointwise := FormalSLT.VC.SampleComplexity.vcRademacher_pointwise
alias expected_rademacher_le_vc := FormalSLT.VC.SampleComplexity.expected_rademacher_le_vc
alias genGap_highProb_vcClass := FormalSLT.VC.SampleComplexity.genGap_highProb_vcClass
alias uniformDeviation_highProb_vcClass :=
  FormalSLT.VC.SampleComplexity.uniformDeviation_highProb_vcClass
alias vc_erm_excessRisk_tail := FormalSLT.VC.SampleComplexity.vc_erm_excessRisk_tail

end FormalSLT.VC.VCSampleComplexity
