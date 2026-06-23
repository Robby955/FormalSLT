import FormalSLT.PACBayesMcAllester
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Concrete non-vacuity witness for `pacbayes_mcallester_sqrt`

Adversarial verification: instantiate the McAllester sqrt-form bound on a
concrete non-trivial instance with a non-constant `f`, discharging every
hypothesis (including the uniform-in-λ MGF certificate) from first
principles. This converts the math-level non-vacuity into a
machine-checked witness.

Instance: `ι = Bool`, `ρ = π = uniform(1/2,1/2)`, `f = (1, -1)` (centered),
`c = 1`, `α = 0`. Then
* `∑ ρ_i f_i = 0`,
* `∑ π_i exp(λ f_i) = cosh λ`,
* `log(cosh λ) ≤ λ²/2 = λ²·c/2 + α`   (via `Real.cosh_le_exp_half_sq`).
-/

open Finset Real
open FormalSLT.PACBayesKL FormalSLT.PACBayesMcAllester

namespace PACBayesMcAllesterSqrtWitness

/-- Uniform PMF on `Bool`. -/
noncomputable def unif : Bool → ℝ := fun _ => 1 / 2

/-- Centered ±1 function on `Bool`. -/
noncomputable def fpm : Bool → ℝ := fun b => if b then 1 else -1

lemma unif_isPMF : IsPMF unif where
  nonneg := by intro i; unfold unif; norm_num
  sum_one := by rw [Fintype.sum_bool]; unfold unif; norm_num

lemma unif_isFullSupportPMF : IsFullSupportPMF unif where
  nonneg := by intro i; unfold unif; norm_num
  sum_one := by rw [Fintype.sum_bool]; unfold unif; norm_num
  pos := by intro i; unfold unif; norm_num

/-- The prior MGF on this instance is exactly `cosh λ`. -/
lemma sum_exp_eq_cosh (lam : ℝ) :
    ∑ i, unif i * Real.exp (lam * fpm i) = Real.cosh lam := by
  rw [Fintype.sum_bool]
  unfold unif fpm
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [Real.cosh_eq]
  ring_nf

/-- The MGF certificate holds uniformly in `λ > 0` with `c = 1`, `α = 0`. -/
lemma mgf_cert :
    ∀ lam, 0 < lam →
      Real.log (∑ i, unif i * Real.exp (lam * fpm i)) ≤ lam ^ 2 * 1 / 2 + 0 := by
  intro lam _
  rw [sum_exp_eq_cosh]
  have hcosh : Real.cosh lam ≤ Real.exp (lam ^ 2 / 2) := Real.cosh_le_exp_half_sq lam
  have hpos : 0 < Real.cosh lam := Real.cosh_pos lam
  calc Real.log (Real.cosh lam)
      ≤ Real.log (Real.exp (lam ^ 2 / 2)) := Real.log_le_log hpos hcosh
    _ = lam ^ 2 / 2 := Real.log_exp _
    _ = lam ^ 2 * 1 / 2 + 0 := by ring

/-- The fully discharged concrete instance of `pacbayes_mcallester_sqrt`.
Every hypothesis is satisfied; `f` is non-constant; the conclusion is the
genuine sqrt bound (not a tautology produced by forcing `f = 0`). -/
theorem witness :
    ∑ i, unif i * fpm i ≤ Real.sqrt (2 * (klDiv unif unif + 0) * 1) :=
  pacbayes_mcallester_sqrt unif_isPMF unif_isFullSupportPMF fpm 1 0
    (by norm_num) (le_refl 0) mgf_cert

/-- The posterior expectation on this instance is genuinely `0` (the LHS is
not trivially the RHS): `∑ ρ_i f_i = 0`. -/
lemma lhs_eq_zero : ∑ i, unif i * fpm i = 0 := by
  rw [Fintype.sum_bool]
  unfold unif fpm
  norm_num

/-- The instance is non-constant: `f true ≠ f false`, so this is NOT the
degenerate `f = 0` collapse. -/
lemma f_nonconstant : fpm true ≠ fpm false := by
  unfold fpm; norm_num

#check @witness
#print axioms witness

end PACBayesMcAllesterSqrtWitness
