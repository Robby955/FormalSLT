import FormalSLT.AnytimeValid.BettingCS

/-!
# Axiom audit for betting/e-process confidence sequences

The public betting confidence-sequence theorems should report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open FormalSLT.AnytimeValid

#check @bettingWealthProcess
#check @bettingWealth_supermartingale
#check @bettingWealth_eProcess
#check @betting_time_uniform_confidence_sequence

#print axioms bettingWealth_supermartingale
#print axioms bettingWealth_eProcess
#print axioms betting_time_uniform_confidence_sequence
