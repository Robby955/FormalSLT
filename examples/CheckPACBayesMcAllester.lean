import FormalSLT.PACBayesBoundedLoss

/-!
# PAC-Bayes McAllester-style bounded-complexity audit

Checks the finite fixed-budget square-root corollary derived from the
fixed-`lambda` Catoni-style PAC-Bayes theorem.
-/

#check FormalSLT.PACBayesBoundedLoss.catoni_fixedLambda_budget_eq_sqrt
#print axioms FormalSLT.PACBayesBoundedLoss.catoni_fixedLambda_budget_eq_sqrt

#check FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le_complexity_sqrt
#print axioms FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le_complexity_sqrt

#check FormalSLT.PACBayesBoundedLoss.finiteMcAllesterBoundedComplexity_badEventMass_le_delta
#print axioms FormalSLT.PACBayesBoundedLoss.finiteMcAllesterBoundedComplexity_badEventMass_le_delta
