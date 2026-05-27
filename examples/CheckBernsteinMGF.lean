import FormalSLT.Probability.BernsteinMGF
import FormalSLT.Rademacher.Localized

/-!
# Bennett / Bernstein MGF + localized Bernstein fast-rate audit

Checks the reusable variance-aware Bennett/Bernstein moment-generating-function
brick and its composition into the finite localized Bernstein high-confidence
theorem. Each `#print axioms` should report only
`[propext, Classical.choice, Quot.sound]`.

This file audits the local Bennett/Bernstein MGF layer used by FormalSLT's
localized Bernstein theorem.
-/

/-! ## Pointwise Bennett analysis -/

#check @FormalSLT.Probability.BernsteinMGF.one_add_add_sq_le_exp_of_nonneg
#print axioms FormalSLT.Probability.BernsteinMGF.one_add_add_sq_le_exp_of_nonneg

#check @FormalSLT.Probability.BernsteinMGF.exp_le_one_add_add_sq_of_nonpos
#print axioms FormalSLT.Probability.BernsteinMGF.exp_le_one_add_add_sq_of_nonpos

#check @FormalSLT.Probability.BernsteinMGF.exp_sub_one_sub_eq_tsum
#print axioms FormalSLT.Probability.BernsteinMGF.exp_sub_one_sub_eq_tsum

#check @FormalSLT.Probability.BernsteinMGF.exp_le_quadratic_of_le
#print axioms FormalSLT.Probability.BernsteinMGF.exp_le_quadratic_of_le

/-! ## Finite Bennett MGF and sub-Gamma simplification -/

#check @FormalSLT.Probability.BernsteinMGF.bennett_mgf
#print axioms FormalSLT.Probability.BernsteinMGF.bennett_mgf

#check @FormalSLT.Probability.BernsteinMGF.two_mul_three_pow_le_factorial
#print axioms FormalSLT.Probability.BernsteinMGF.two_mul_three_pow_le_factorial

#check @FormalSLT.Probability.BernsteinMGF.exp_sub_one_sub_le_sq_div
#print axioms FormalSLT.Probability.BernsteinMGF.exp_sub_one_sub_le_sq_div

#check @FormalSLT.Probability.BernsteinMGF.bennett_mgf_subgamma
#print axioms FormalSLT.Probability.BernsteinMGF.bennett_mgf_subgamma

/-! ## Markov/Chernoff tail and Bernstein tails -/

#check @FormalSLT.Probability.BernsteinMGF.weighted_upper_tail_le_mgf_div
#print axioms FormalSLT.Probability.BernsteinMGF.weighted_upper_tail_le_mgf_div

#check @FormalSLT.Probability.BernsteinMGF.bernstein_tail_mgf
#print axioms FormalSLT.Probability.BernsteinMGF.bernstein_tail_mgf

#check @FormalSLT.Probability.BernsteinMGF.bernstein_tail
#print axioms FormalSLT.Probability.BernsteinMGF.bernstein_tail

#check @FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail
#print axioms FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail

/-! ## Localized Bernstein fast-rate composition -/

#check @FormalSLT.Rademacher.Localized.centeredSecondMoment_le_of_bernstein_localized
#print axioms FormalSLT.Rademacher.Localized.centeredSecondMoment_le_of_bernstein_localized

#check @FormalSLT.Rademacher.Localized.localizedFiniteClassBernsteinHighConfidence_empirical_nonpos
#print axioms FormalSLT.Rademacher.Localized.localizedFiniteClassBernsteinHighConfidence_empirical_nonpos
