import FormalSLT.PACBayes.ChangeOfMeasure

/-!
# PAC-Bayes change-of-measure audit

Checks the finite Donsker-Varadhan, tight change-of-measure, Catoni, and
McAllester chain, plus a concrete two-point non-vacuity certificate.
-/

#check FormalSLT.PACBayes.ChangeOfMeasure.dv_variational_step
#print axioms FormalSLT.PACBayes.ChangeOfMeasure.dv_variational_step

#check FormalSLT.PACBayes.ChangeOfMeasure.tight_changeOfMeasure_bound
#print axioms FormalSLT.PACBayes.ChangeOfMeasure.tight_changeOfMeasure_bound

#check FormalSLT.PACBayes.ChangeOfMeasure.catoni_changeOfMeasure_bound
#print axioms FormalSLT.PACBayes.ChangeOfMeasure.catoni_changeOfMeasure_bound

#check FormalSLT.PACBayes.ChangeOfMeasure.mcallester_tight_bound
#print axioms FormalSLT.PACBayes.ChangeOfMeasure.mcallester_tight_bound

#check FormalSLT.PACBayes.ChangeOfMeasure.twoPointPrior
#check FormalSLT.PACBayes.ChangeOfMeasure.twoPointPosterior
#check FormalSLT.PACBayes.ChangeOfMeasure.twoPointDataLaw_isPMF
#check FormalSLT.PACBayes.ChangeOfMeasure.twoPointLoss_mem_unitInterval
#check FormalSLT.PACBayes.ChangeOfMeasure.twoPointLoss_nontrivial
#check FormalSLT.PACBayes.ChangeOfMeasure.twoPoint_mcallester_nonvacuous
#print axioms FormalSLT.PACBayes.ChangeOfMeasure.twoPoint_mcallester_nonvacuous
