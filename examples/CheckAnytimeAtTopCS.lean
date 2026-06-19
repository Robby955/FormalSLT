import FormalSLT.AnytimeValid.AtTopCS

/-!
# Axiom audit for countable-time anytime-valid confidence sequences

The public atTop theorems should report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open FormalSLT.AnytimeValid

#check @ville_atTop_maximal_ineq
#check @ville_atTop_subGamma_running_mean
#check @atTop_time_uniform_confidence_sequence_subGamma
#check @atTopSubGammaUpperFailure_zero_process_empty

#print axioms ville_atTop_maximal_ineq
#print axioms ville_atTop_subGamma_running_mean
#print axioms atTop_time_uniform_confidence_sequence_subGamma
#print axioms atTopSubGammaUpperFailure_zero_process_empty
