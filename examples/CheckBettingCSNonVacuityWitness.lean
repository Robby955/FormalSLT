import FormalSLT.AnytimeValid.BettingCS

/-!
# Non-vacuity witness for the betting confidence sequence

The witness must instantiate the betting/e-process confidence sequence with a
genuine nonzero Rademacher increment and a predictable nonzero betting fraction.
-/

open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.BettingNonVacuityWitness

#check bettingNonVacuityWitness
#check bettingWitness_positive_gain

#print axioms bettingNonVacuityWitness
#print axioms bettingWitness_positive_gain
