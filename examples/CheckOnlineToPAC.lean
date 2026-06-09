import FormalSLT.OnlineToPAC.CesaBianchi

/-!
# Axiom audit for online-to-PAC conversion
-/

open FormalSLT.OnlineToPAC

#print axioms onlineToPAC_boundedLoss_iid_of_regret_and_deviation
#print axioms cesaBianchiConconiGentile2004_boundedLoss_iid_highProbability

#check @onlineToPAC_boundedLoss_iid_of_regret_and_deviation
#check @cesaBianchiConconiGentile2004_boundedLoss_iid_highProbability

example : True := trivial
