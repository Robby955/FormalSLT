import FormalSLT.AnytimeValid.EmpiricalBernsteinCS

/-!
# Empirical-Bernstein confidence sequence audit

Checks the variance-adaptive anytime-valid surface:

* a conditional Bernstein MGF with a random predictable variance proxy;
* a fixed-lambda time-uniform confidence sequence;
* a uniform-prior mixture headline with no free product-measurability hypotheses;
* a rational arithmetic check of the closed-form boundary helper.

The genuine nonzero (`±1` Rademacher increment) non-vacuity witness for the
uniform-prior headline is in `CheckEmpiricalBernsteinNonVacuityWitness.lean`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

#check @condBernsteinMGF_of_bounded_centered_condVarianceProxy
#check @empiricalBernstein_exponential_supermartingale
#check @empiricalBernstein_time_uniform_confidence_sequence
#check @empiricalBernstein_confidence_sequence_uniformPrior
#check empiricalBernstein_rational_witness_nonvacuous

#print axioms condBernsteinMGF_of_bounded_centered_condVarianceProxy
#print axioms empiricalBernstein_exponential_supermartingale
#print axioms empiricalBernstein_time_uniform_confidence_sequence
#print axioms empiricalBernstein_confidence_sequence_uniformPrior
#print axioms empiricalBernstein_rational_witness_nonvacuous

example :
    empiricalBernsteinClosedFormBoundary 0 1 4 2 1 = 2 := by
  norm_num [empiricalBernsteinClosedFormBoundary]

example :
    empiricalBernstein_rational_witness_nonvacuous =
      empiricalBernstein_rational_witness_nonvacuous := rfl
