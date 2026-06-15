import FormalSLT.PACBayes.McAllesterCompilerHighProbability

/-!
# Axiom audit for the McAllester compiler good-event theorem
-/

open FormalSLT.PACBayes

#check compiledMcAllesterGeneralGoodSamples_eq_compl
#print axioms compiledMcAllesterGeneralGoodSamples_eq_compl

#check mcAllesterGeneralWidth_goodEventMass_ge_one_sub_delta
#print axioms mcAllesterGeneralWidth_goodEventMass_ge_one_sub_delta

#check mcAllesterPointwiseRiskBound_of_mem_good
#print axioms mcAllesterPointwiseRiskBound_of_mem_good

example : True := trivial
