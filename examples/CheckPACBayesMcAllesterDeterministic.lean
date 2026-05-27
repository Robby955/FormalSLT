import FormalSLT.PACBayesMcAllester

/-!
# PAC-Bayes McAllester audit

This file checks that the deterministic core of the McAllester (1999)
PAC-Bayes generalization bound is fully machine-checked, with only the
standard kernel axioms `propext`, `Classical.choice`, `Quot.sound`.

This audit is limited to the deterministic `PACBayesMcAllester` core.
Finite product-weight confidence wrappers live in `PACBayesBoundedLoss`;
all-real-`lambda`, infinite-hypothesis, and continuous-posterior variants
remain out of scope.
-/

#check FormalSLT.PACBayesMcAllester.pacbayes_changeOfMeasure
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_changeOfMeasure

#check FormalSLT.PACBayesMcAllester.pacbayes_mcallester_deterministic
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_mcallester_deterministic

#check FormalSLT.PACBayesMcAllester.pacbayes_mcallester_subGaussian
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_mcallester_subGaussian

#check FormalSLT.PACBayesMcAllester.pacbayes_mcallester_sqrt
#print axioms FormalSLT.PACBayesMcAllester.pacbayes_mcallester_sqrt
