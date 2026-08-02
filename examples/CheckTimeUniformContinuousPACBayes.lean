import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Time-uniform continuous PAC-Bayes audit

Checks the arbitrary measurable-hypothesis process bridge:

* fixed-hypothesis conditional supermartingale steps integrate under a prior;
* the continuous prior mixture is a nonnegative supermartingale;
* Ville controls its countable-time crossing event;
* continuous Donsker--Varadhan turns posterior failure into prior crossing;
* the end-to-end theorem combines those steps without a finite hypothesis class.

The result is process-level.  This audit does not claim an i.i.d. learning
specialization or identify the repository's analytic Gaussian expression with
mathlib's measure-theoretic `klDiv`.
-/

open FormalSLT.PACBayes.TimeUniformContinuous

#check @continuousPriorMixture_condExp_step_of_fixed_hypothesis_steps
#check @continuousPriorMixture_supermartingale
#check @continuousPriorMixture_crossing_bound
#check @timeUniformContinuousPACBayesUpperFailure_subset_crossing
#check @timeUniformContinuousPACBayes_bound

#print axioms continuousPriorMixture_condExp_step_of_fixed_hypothesis_steps
#print axioms continuousPriorMixture_supermartingale
#print axioms continuousPriorMixture_crossing_bound
#print axioms timeUniformContinuousPACBayesUpperFailure_subset_crossing
#print axioms timeUniformContinuousPACBayes_bound
