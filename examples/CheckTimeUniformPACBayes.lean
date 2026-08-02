import FormalSLT.PACBayes.TimeUniformPACBayes

/-!
# Time-uniform PAC-Bayes audit

Checks the finite fixed-tilt PAC-Bayes confidence sequence:

* the prior-mixture exponential process is a nonnegative supermartingale;
* Ville controls its countable-time crossing event;
* Donsker-Varadhan inverts the crossing event into a posterior-risk bound for
  every time `n >= 1` and every posterior PMF on one common good event;
* a concrete two-hypothesis Rademacher witness instantiates the result with a
  nonzero increment.

The lane-level source is Chugg-Wang-Ramdas for anytime PAC-Bayes; this file does
not make a theorem-name claim about first mechanization.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayes.TimeUniform

#check @pacBayesPriorMixture_supermartingale
#check @timeUniformPACBayes_crossing_bound
#check @timeUniformPACBayes_bound
#check @timeUniformPACBayesAnyPosteriorUpperFailure_subset_crossing
#check @timeUniformPACBayes_allPosteriors_bound
#check rademacher_timeUniformPACBayes_allPosteriors_witness
#check rademacher_timeUniformPACBayes_witness

#print axioms pacBayesPriorMixture_supermartingale
#print axioms timeUniformPACBayes_crossing_bound
#print axioms timeUniformPACBayes_bound
#print axioms timeUniformPACBayesAnyPosteriorUpperFailure_subset_crossing
#print axioms timeUniformPACBayes_allPosteriors_bound
#print axioms rademacher_timeUniformPACBayes_allPosteriors_witness
#print axioms rademacher_timeUniformPACBayes_witness

example :
    μBool.real
      (timeUniformPACBayesUpperFailure
        twoHypPrior twoHypPosterior rademacherHypGap 1 1 (1 / 2) (1 / 2))
      ≤ (1 / 2 : ℝ) :=
  rademacher_timeUniformPACBayes_witness
