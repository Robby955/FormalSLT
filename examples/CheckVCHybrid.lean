import FormalSLT.PACBayes.VCHybrid

/-!
# VC / PAC-Bayes hybrid audit

Checks the T2 hybrid surface: a Sauer-Shelah/VC capacity term, a finite
union-bound hybrid bad-event mass theorem, and a posterior-risk inequality
whose right-hand side carries both the VC capacity and PAC-Bayes KL terms.
-/

#check FormalSLT.PACBayes.VCHybrid.vcCapacityTerm_nonneg
#print axioms FormalSLT.PACBayes.VCHybrid.vcCapacityTerm_nonneg

#check FormalSLT.PACBayes.VCHybrid.vcGood_from_pointwiseRademacher
#print axioms FormalSLT.PACBayes.VCHybrid.vcGood_from_pointwiseRademacher

#check FormalSLT.PACBayes.VCHybrid.vcPacBayesHybridBadEventMass_le
#print axioms FormalSLT.PACBayes.VCHybrid.vcPacBayesHybridBadEventMass_le

#check FormalSLT.PACBayes.VCHybrid.vcPacBayesBernsteinPosteriorRisk_bound
#print axioms FormalSLT.PACBayes.VCHybrid.vcPacBayesBernsteinPosteriorRisk_bound

#check FormalSLT.PACBayes.VCHybrid.vcPacBayesBernsteinPosteriorRisk_bound_from_vcRademacher
#print axioms FormalSLT.PACBayes.VCHybrid.vcPacBayesBernsteinPosteriorRisk_bound_from_vcRademacher
