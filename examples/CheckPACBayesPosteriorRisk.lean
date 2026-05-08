import FormalSLT

/-!
# PAC-Bayes posterior-risk surface check

This example pins the finite, deterministic PAC-Bayes adapter layer:
posterior averages, posterior risks, posterior empirical risks, posterior
generalization gaps, and the Donsker-Varadhan change-of-measure theorem
specialized to posterior averages. It also checks the positive-λ risk-bound
rearrangements and finite Markov/confidence adapters that later
McAllester/Catoni sample-bound proofs will consume.
-/

#check FormalSLT.PACBayesKL.posteriorAverage
#check FormalSLT.PACBayesKL.posteriorRisk
#check FormalSLT.PACBayesKL.posteriorEmpiricalRisk
#check FormalSLT.PACBayesKL.posteriorGeneralizationGap
#check FormalSLT.PACBayesKL.posteriorGeneralizationGap_eq_sum
#check FormalSLT.PACBayesKL.posterior_change_of_measure
#check FormalSLT.PACBayesKL.posterior_generalization_gap_change_of_measure
#check FormalSLT.PACBayesKL.posterior_generalization_gap_le_complexity_div_lambda
#check FormalSLT.PACBayesKL.posterior_risk_le_empiricalRisk_plus_complexity_div_lambda
#check FormalSLT.PACBayesKL.posterior_generalization_gap_le_of_log_moment_bound
#check FormalSLT.PACBayesKL.posterior_risk_le_empiricalRisk_plus_of_log_moment_bound
#check FormalSLT.PACBayesKL.priorExpMoment
#check FormalSLT.PACBayesKL.expectedPriorExpMoment
#check FormalSLT.PACBayesKL.priorExpMomentTailMass
#check FormalSLT.PACBayesKL.priorExpMoment_tailMass_le_expected_div
#check FormalSLT.PACBayesKL.priorExpMoment_tailMass_le_delta_of_expected_bound
