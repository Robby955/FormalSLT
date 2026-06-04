/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesBernstein

/-!
# Tests for the finite PAC-Bayes Bernstein layer

This file checks the public theorem surface added by
`FormalSLT.PACBayesBernstein`. The module is intentionally abstract: it exposes
the finite PAC-Bayes Bernstein shell with a supplied variance proxy and a
normalized prior-moment certificate.
-/

namespace FormalSLT.PACBayesBernstein.Test

#check FormalSLT.PACBayesBernstein.posteriorMarginVarianceProxy
#check FormalSLT.PACBayesBernstein.priorBernsteinExpMoment
#check FormalSLT.PACBayesBernstein.expectedPriorBernsteinExpMoment
#check FormalSLT.PACBayesBernstein.priorBernsteinExpMomentTailMass
#check FormalSLT.PACBayesBernstein.priorBernsteinExpMoment_nonneg
#check FormalSLT.PACBayesBernstein.priorBernsteinExpMoment_tailMass_le_expected_div
#check FormalSLT.PACBayesBernstein.priorBernsteinExpMoment_tailMass_le_delta_of_expected_bound
#check FormalSLT.PACBayesBernstein.posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le
#check FormalSLT.PACBayesBernstein.finitePACBayesBernsteinFixedLambdaBadSamples
#check FormalSLT.PACBayesBernstein.finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
#check FormalSLT.PACBayesBernstein.finitePACBayesBernsteinPenaltyBadSamples
#check FormalSLT.PACBayesBernstein.finitePACBayesBernsteinPenalty_badEventMass_le_delta
#check FormalSLT.PACBayesBernstein.finitePACBayesBernsteinMargin_badEventMass_le_delta

end FormalSLT.PACBayesBernstein.Test
