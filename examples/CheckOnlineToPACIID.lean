import FormalSLT.OnlineToPAC.IIDConcentration
import FormalSLT.TestTimeMeta.MainTheorem

/-!
# Axiom audit for iid-derived online-to-PAC concentration
-/

open FormalSLT.Probability.IIDConcentration
open FormalSLT.OnlineToPAC
open FormalSLT.TestTimeMeta

#print axioms iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid
#print axioms regretConversion_iid
#print axioms cesaBianchi_iid
#print axioms onlineToPACContribution_from_iidRegretConversion

#check @iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid
#check @regretConversion_iid
#check @cesaBianchi_iid
#check @onlineToPACContribution_from_iidRegretConversion

example : True := trivial
