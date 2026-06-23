import FormalSLT.PACBayesMcAllester
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Tutorial 2 — a PAC-Bayes bound on a concrete problem

**Goal.** You have a small hypothesis class, a prior `π` over it, and a posterior
`ρ` you chose after seeing data. You want McAllester's PAC-Bayes guarantee: the
posterior-averaged score `∑ ρ_i f_i` is controlled by the KL divergence to the
prior. This tutorial instantiates the sqrt-form bound

`∑ ρ_i · f_i ≤ √(2 · (KL(ρ‖π) + α) · c)`

on an explicit class and reads off the number.

This is a *tutorial*: it shows the call, the MGF certificate you must supply, and
the final bound. Copy the `worked_*` declarations and edit the class / prior /
score for your own problem.

Uses only:
* `FormalSLT.PACBayesMcAllester.pacbayes_mcallester_sqrt` — the bound.
* `FormalSLT.PACBayesKL.IsPMF` / `IsFullSupportPMF` / `klDiv` — the prior/posterior
  interface and the KL functional.

Everything is `[propext, Classical.choice, Quot.sound]`-clean.
-/

open Finset Real
open FormalSLT.PACBayesKL FormalSLT.PACBayesMcAllester

namespace FormalSLT.Tutorials.PACBayes

noncomputable section

/-! ## Step 0 — set up the class, prior, posterior, and score

Two hypotheses (`ι = Bool`). Prior `π` and posterior `ρ` are both uniform here so
the KL term is `0` and we see the pure sub-Gaussian width; the comment after the
bound explains how a non-uniform posterior enters. The score `f` is the centered
±1 function `f true = 1`, `f false = -1` — genuinely non-constant, so this is not
the degenerate `f = 0` collapse. -/

/-- Uniform prior/posterior on the two hypotheses. -/
def unif : Bool → ℝ := fun _ => 1 / 2

/-- The centered ±1 score: `f true = 1`, `f false = -1`. -/
def score : Bool → ℝ := fun b => if b then 1 else -1

/-- `unif` is a probability mass function. -/
lemma unif_isPMF : IsPMF unif where
  nonneg := by intro i; simp [unif]
  sum_one := by rw [Fintype.sum_bool]; simp [unif]; ring

/-- `unif` has full support (needed for the prior). -/
lemma unif_isFullSupportPMF : IsFullSupportPMF unif where
  nonneg := by intro i; simp [unif]
  sum_one := by rw [Fintype.sum_bool]; simp [unif]; ring
  pos := by intro i; simp [unif]

/-! ## Step 1 — supply the MGF certificate

`pacbayes_mcallester_sqrt` asks for a uniform-in-`λ` sub-Gaussian log-MGF bound on
the prior: `∀ λ > 0, log(∑ π_i exp(λ f_i)) ≤ λ²·c/2 + α`. For our ±1 score under
the uniform prior, `∑ π_i exp(λ f_i) = cosh λ`, and mathlib's
`Real.cosh_le_exp_half_sq` gives `cosh λ ≤ exp(λ²/2)`, i.e. the certificate holds
with `c = 1`, `α = 0`. This is the only piece of analysis the user provides; the
optimization over `λ` is inside the theorem. -/

/-- The prior MGF on this instance is exactly `cosh λ`. -/
lemma sum_exp_eq_cosh (lam : ℝ) :
    ∑ i, unif i * Real.exp (lam * score i) = Real.cosh lam := by
  rw [Fintype.sum_bool]
  simp only [unif, score, if_true, Bool.false_eq_true, if_false]
  rw [Real.cosh_eq]; ring_nf

/-- The MGF certificate with `c = 1`, `α = 0`. -/
lemma mgf_cert :
    ∀ lam, 0 < lam →
      Real.log (∑ i, unif i * Real.exp (lam * score i)) ≤ lam ^ 2 * 1 / 2 + 0 := by
  intro lam _
  rw [sum_exp_eq_cosh]
  have hcosh : Real.cosh lam ≤ Real.exp (lam ^ 2 / 2) := Real.cosh_le_exp_half_sq lam
  have hpos : 0 < Real.cosh lam := Real.cosh_pos lam
  calc Real.log (Real.cosh lam)
      ≤ Real.log (Real.exp (lam ^ 2 / 2)) := Real.log_le_log hpos hcosh
    _ = lam ^ 2 / 2 := Real.log_exp _
    _ = lam ^ 2 * 1 / 2 + 0 := by ring

/-! ## Step 2 — apply the bound -/

/-- **The worked PAC-Bayes bound.** With `c = 1`, `α = 0`, the posterior score is
bounded by `√(2 · (KL(ρ‖π) + 0) · 1)`. -/
theorem worked_pacbayes :
    ∑ i, unif i * score i ≤ Real.sqrt (2 * (klDiv unif unif + 0) * 1) :=
  pacbayes_mcallester_sqrt unif_isPMF unif_isFullSupportPMF score 1 0
    (by norm_num) (le_refl 0) mgf_cert

/-! ## Step 3 — read off the number

The posterior score is `∑ ρ_i f_i = (1/2)(1) + (1/2)(-1) = 0`, and with `ρ = π`
the KL term is `0`, so the bound reads `0 ≤ √0 = 0` — tight. The teaching point:
the left side is genuinely `0` (not forced by `f = 0`, which is non-constant), and
the bound is the sqrt of `2(KL + α)c`. With a *non-uniform* posterior `ρ ≠ π` the
KL term becomes strictly positive and the bound `√(2·KL·c)` is the price of moving
the posterior away from the prior — that is the content of PAC-Bayes. -/

/-- The posterior-averaged score on this instance is genuinely `0`. -/
theorem worked_lhs_eq_zero : ∑ i, unif i * score i = 0 := by
  rw [Fintype.sum_bool]; simp [unif, score]

/-- The score is non-constant — this is not the degenerate `f = 0` collapse. -/
theorem worked_score_nonconstant : score true ≠ score false := by
  simp only [score, if_true, Bool.false_eq_true, if_false]; norm_num

/-! ## How to adapt this to your problem

* **More hypotheses:** change `ι = Bool` to your finite class; redo `unif_isPMF`
  on your prior/posterior.
* **A non-uniform posterior:** keep the prior `π`, supply a different posterior
  `ρ` with its own `IsPMF`, and `klDiv ρ π` will be strictly positive — the bound
  then exposes the KL penalty.
* **A different score / sub-Gaussian scale:** supply the matching MGF certificate
  with your `c` and `α`; any sub-Gaussian summand satisfies the uniform-in-`λ`
  bound `log MGF ≤ λ²c/2`.
-/

end

end FormalSLT.Tutorials.PACBayes
