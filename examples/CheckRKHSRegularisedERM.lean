import FormalSLT.Stability.RKHSRegularisedERM

/-!
# Axiom audit for finite-dimensional RKHS regularised ERM stability
-/

#print axioms FormalSLT.Stability.RKHSRegularisedERM.rkhs_regularised_erm_uniform_stability
#print axioms FormalSLT.Stability.RKHSRegularisedERM.rkhs_regularised_erm_generalization_bound
#print axioms FormalSLT.Stability.RKHSRegularisedERM.rkhs_regularised_erm_sample_complexity

open FormalSLT.Stability.RKHSRegularisedERM

example :
    rkhsGeneralizationSlack 1 1 1 1 4 ((1 : ℝ) / 2)
      =
    (1 ^ 2 * 1 ^ 2) / (1 * 4) +
      (4 * 1 ^ 2 * 1 ^ 2 / 1 + 1) *
        Real.sqrt (Real.log (1 / ((1 : ℝ) / 2)) / (2 * (4 : ℝ))) := by
  rfl
