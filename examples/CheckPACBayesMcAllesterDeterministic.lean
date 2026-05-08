import FormalSLT.PACBayesMcAllester

/-!
# PAC-Bayes McAllester audit

This file checks that the deterministic core of the McAllester (1999)
PAC-Bayes generalization bound is fully machine-checked, with only the
standard kernel axioms `propext`, `Classical.choice`, `Quot.sound`.

The probabilistic shell — the "with probability ≥ 1-δ over `S ~ D^m`"
quantifier — is intentionally **not** included here: it requires
measure-theoretic infrastructure (Markov's inequality on a joint
distribution over samples) outside the finite, discrete scope of this
module. The deterministic core below is the algebraic content of
McAllester's proof.
-/

#check FormalSLT.PACBayesMcAllester.pacbayes_changeOfMeasure
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_changeOfMeasure

#check FormalSLT.PACBayesMcAllester.pacbayes_mcallester_deterministic
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_mcallester_deterministic

#check FormalSLT.PACBayesMcAllester.pacbayes_mcallester_subGaussian
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_mcallester_subGaussian

#check FormalSLT.PACBayesMcAllester.pacbayes_mcallester_sqrt
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_mcallester_sqrt
