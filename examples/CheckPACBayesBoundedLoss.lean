import FormalSLT.PACBayesBoundedLoss

/-!
# PAC-Bayes bounded-loss audit

Checks the finite bounded-loss PAC-Bayes path:
one-coordinate MGF, sample/product MGF, prior-averaged MGF, finite Markov
confidence, and the finite Catoni-style posterior-risk bad-event theorem.
-/

#check FormalSLT.PACBayesBoundedLoss.oneCoordinate_boundedLoss_mgf
#print axioms FormalSLT.PACBayesBoundedLoss.oneCoordinate_boundedLoss_mgf

#check FormalSLT.PACBayesBoundedLoss.sampleAverage_boundedLoss_mgf
#print axioms FormalSLT.PACBayesBoundedLoss.sampleAverage_boundedLoss_mgf

#check FormalSLT.PACBayesBoundedLoss.priorAveraged_boundedLoss_mgf
#print axioms FormalSLT.PACBayesBoundedLoss.priorAveraged_boundedLoss_mgf

#check FormalSLT.PACBayesBoundedLoss.priorAveraged_boundedLoss_mgf_badEventMass_le_delta
#print axioms FormalSLT.PACBayesBoundedLoss.priorAveraged_boundedLoss_mgf_badEventMass_le_delta

#check FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le
#print axioms FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le

#check FormalSLT.PACBayesBoundedLoss.finiteCatoni_badEventMass_le_delta
#print axioms FormalSLT.PACBayesBoundedLoss.finiteCatoni_badEventMass_le_delta
