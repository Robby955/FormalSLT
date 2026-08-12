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

#check @FormalSLT.Probability.BernsteinMGF.bennett_mgf_le_one_add
#print axioms FormalSLT.Probability.BernsteinMGF.bennett_mgf_le_one_add

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

/-! ## Concrete retained-factor witness -/

namespace RetainedFactorBennettWitness

/-- Fair weights on a two-point sample space. -/
noncomputable def fairWeight (_z : Bool) : ℝ := 1 / 2

/-- A nonconstant centered observable with second moment `1/4`. -/
noncomputable def centeredSign : Bool → ℝ
  | false => -(1 / 2)
  | true => 1 / 2

/-- The retained-factor Bennett endpoint applies to a genuine nonconstant
two-point law at positive tilt, upper bound, and variance proxy. -/
theorem fairCenteredSign_retained :
    ∑ z : Bool, fairWeight z * Real.exp (1 * centeredSign z)
      ≤ 1 + (Real.exp (1 * (1 / 2)) - 1 - 1 * (1 / 2)) / (1 / 2) ^ 2 * (1 / 4) := by
  apply FormalSLT.Probability.BernsteinMGF.bennett_mgf_le_one_add
      (b := 1 / 2) (v := 1 / 4) (lam := 1)
  · norm_num
  · norm_num
  · intro z
    norm_num [fairWeight]
  · norm_num [fairWeight]
  · norm_num [fairWeight, centeredSign]
  · intro z
    cases z <;> norm_num [centeredSign]
  · norm_num [fairWeight, centeredSign]

theorem centeredSign_nonconstant : centeredSign false ≠ centeredSign true := by
  norm_num [centeredSign]

/-- At this witness the retained Bennett correction is genuinely positive. -/
theorem retainedBudget_pos :
    0 < (Real.exp (1 * (1 / 2)) - 1 - 1 * (1 / 2)) / (1 / 2) ^ 2 * (1 / 4) := by
  have h := Real.add_one_lt_exp (show (1 / 2 : ℝ) ≠ 0 by norm_num)
  norm_num at h ⊢
  linarith

/-- The retained affine factor is strictly below its exponential relaxation on
the concrete positive-budget witness. -/
theorem retained_strictly_sharper :
    1 + (Real.exp (1 * (1 / 2)) - 1 - 1 * (1 / 2)) / (1 / 2) ^ 2 * (1 / 4)
      < Real.exp ((Real.exp (1 * (1 / 2)) - 1 - 1 * (1 / 2)) /
          (1 / 2) ^ 2 * (1 / 4)) := by
  simpa [add_comm] using Real.add_one_lt_exp (ne_of_gt retainedBudget_pos)

#check fairCenteredSign_retained
#print axioms fairCenteredSign_retained

#check centeredSign_nonconstant
#print axioms centeredSign_nonconstant

#check retainedBudget_pos
#print axioms retainedBudget_pos

#check retained_strictly_sharper
#print axioms retained_strictly_sharper

end RetainedFactorBennettWitness
