import FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes

/-!
# Two-sided continuous-posterior singular-fraction LIL checks

One event controls the absolute posterior-averaged conditional-minus-observed
prefix gap at every reporting time and for every eligible posterior selected
from the path.  This checker also records the theorem's axiom surface.
-/

open FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes

#check exists_continuousTwoSidedSingularFractionBesselPACBayesLIL_event

#check (exists_continuousTwoSidedSingularFractionBesselPACBayesLIL_event
  (Theta := Real))

#print axioms exists_continuousTwoSidedSingularFractionBesselPACBayesLIL_event
