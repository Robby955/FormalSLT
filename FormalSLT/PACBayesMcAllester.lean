/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesKL
import Mathlib.Data.Real.Sqrt

/-!
# McAllester PAC-Bayes generalization bound (deterministic core)

Building on `donsker_varadhan` from `FormalSLT.PACBayesKL`, this module
proves the deterministic algebraic core of the McAllester (1999)
PAC-Bayes bound:

* `pacbayes_changeOfMeasure` — rescaled Donsker-Varadhan: for `λ > 0`,
  `∑ ρ_i · f_i ≤ KL(ρ‖π)/λ + log(∑ π_i · exp(λ f_i))/λ`.
* `pacbayes_mcallester_deterministic` — for any sample where the prior
  MGF satisfies `log(∑ π_i · exp(λ f_i)) ≤ B`, the posterior expectation
  is bounded by `(KL(ρ‖π) + B)/λ`.
* `pacbayes_mcallester_subGaussian` — sub-Gaussian instantiation:
  `∑ ρ_i · f_i ≤ KL(ρ‖π)/λ + λ·c/2 + α/λ` for any fixed `λ > 0`.
* `pacbayes_mcallester_sqrt` — sqrt-form bound: optimizing over `λ`,
  `∑ ρ_i · f_i ≤ √(2·(KL(ρ‖π) + α)·c)`.

## Scope and boundaries

This module formalizes the **deterministic, sample-conditional core** of
McAllester: given an MGF upper bound that is satisfied for a fixed sample
`S`, derive the PAC-Bayes generalization bound. The algebraic content
(rescaled Donsker-Varadhan + λ-optimization) is kept separate so it can
be reused by any probabilistic shell that supplies the MGF certificate.

The **finite probabilistic shell** — the "finite product-sample mass at
most δ" form — is closed in `FormalSLT.PACBayesBoundedLoss` for `[0,1]`
losses, finite data domain, and finite hypothesis class. Specifically:

* `finiteCatoni_badEventMass_le_delta` — finite Catoni-style sample bound
  `R(ρ) ≤ R̂_S(ρ) + (KL(ρ‖π) + log(1/δ))/λ + λ/(8n)` outside a bad event
  of finite product-sample mass at most `δ`.
* `finiteMcAllesterBoundedComplexity_badEventMass_le_delta` — fixed
  complexity-budget McAllester square-root form.
* `finiteMcAllesterGridPeeling_badEventMass_le_delta` — finite-grid
  peeling that removes the single fixed-budget restriction.
* `finiteMcAllesterGridOptimized_badEventMass_le_delta` — posterior-
  dependent penalty form under a finite bucket certificate.

Each is proved by combining `pacbayes_mcallester_deterministic` /
`pacbayes_mcallester_subGaussian` here with the finite Markov adapter
and the bounded-loss MGF bridge in `FormalSLT.PACBayesFiniteProductMGF`
and `FormalSLT.PACBayesBoundedLoss`.

What remains future work: exact all-real-`λ` optimization (the finite
shell uses fixed `λ` or finite-grid peeling), continuous posteriors, and
infinite hypothesis classes.

## References

* Donsker, M.D. & Varadhan, S.R.S. (1975). "Asymptotic evaluation of
  certain Markov process expectations for large time."
* McAllester, D.A. (1999). "PAC-Bayesian model averaging." COLT '99.
* McAllester, D.A. (2003). "PAC-Bayesian stochastic model selection."
  Machine Learning 51(1), 5–21.
* Catoni, O. (2007). *PAC-Bayesian Supervised Classification.* IMS
  Lecture Notes 56, §1.1.
-/

namespace FormalSLT.PACBayesMcAllester

open Finset Real BigOperators
open FormalSLT.PACBayesKL

variable {ι : Type*} [Fintype ι]

/-! ### Rescaled Donsker-Varadhan -/

/-- **Rescaled Donsker-Varadhan inequality.**
For any PMF `ρ`, full-support PMF `π`, function `f : ι → ℝ`, and `λ > 0`,
`∑ ρ_i · f_i  ≤  KL(ρ‖π)/λ  +  log(∑ π_i · exp(λ f_i)) / λ`.

This is the change-of-measure form used in PAC-Bayes bounds: bounding the
posterior expectation by the prior MGF and the KL-cost of moving from `π`
to `ρ`.

Source: Donsker & Varadhan (1975); Catoni (2007) §1.1. -/
theorem pacbayes_changeOfMeasure
    [Nonempty ι] {ρ π : ι → ℝ}
    (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    (lam : ℝ) (hlam : 0 < lam) (f : ι → ℝ) :
    ∑ i, ρ i * f i
      ≤ klDiv ρ π / lam
        + Real.log (∑ i, π i * Real.exp (lam * f i)) / lam := by
  have hDV := donsker_varadhan hρ hπ (fun i => lam * f i)
  -- hDV : ∑ ρ_i * (lam * f i) ≤ klDiv ρ π + log (∑ π_i * exp (lam * f i))
  have h_lhs : ∑ i, ρ i * (lam * f i) = lam * ∑ i, ρ i * f i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h_lhs] at hDV
  -- hDV : lam * (∑ ρ_i * f_i) ≤ klDiv ρ π + log(∑ π_i * exp (lam * f i))
  have h_div : ∑ i, ρ i * f i
      ≤ (klDiv ρ π + Real.log (∑ i, π i * Real.exp (lam * f i))) / lam := by
    rw [le_div_iff₀' hlam]
    exact hDV
  rw [add_div] at h_div
  exact h_div

/-! ### McAllester deterministic core -/

/-- **McAllester PAC-Bayes deterministic core.**
Given a sample `S` and any upper bound `B` on the prior log-MGF,
`log(∑ π_i · exp(λ f_i)) ≤ B`, the change-of-measure inequality yields
`∑ ρ_i · f_i ≤ (KL(ρ‖π) + B)/λ` for any posterior `ρ`.

The probabilistic McAllester (1999) bound is obtained by combining this
with Markov's inequality on the prior-averaged MGF over `S ~ D^m` to
produce, with probability ≥ 1-δ, an explicit `B = λ²·c/2 + log(1/δ)`.

Source: McAllester (1999); Catoni (2007) §1.1. -/
theorem pacbayes_mcallester_deterministic
    [Nonempty ι] {ρ π : ι → ℝ}
    (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    (f : ι → ℝ) (lam : ℝ) (hlam : 0 < lam) (B : ℝ)
    (hMGF : Real.log (∑ i, π i * Real.exp (lam * f i)) ≤ B) :
    ∑ i, ρ i * f i ≤ (klDiv ρ π + B) / lam := by
  have hCM := pacbayes_changeOfMeasure hρ hπ lam hlam f
  have hZ_le : Real.log (∑ i, π i * Real.exp (lam * f i)) / lam ≤ B / lam := by
    exact div_le_div_of_nonneg_right hMGF (le_of_lt hlam)
  rw [add_div]
  linarith

/-! ### Sub-Gaussian instantiation (linear-in-λ form) -/

/-- **McAllester PAC-Bayes bound — sub-Gaussian form, fixed `λ`.**
Given a sub-Gaussian-style log-MGF bound at a fixed `λ > 0`,
`log(∑ π_i · exp(λ f_i)) ≤ λ² · c / 2 + α`, the posterior expectation
satisfies `∑ ρ_i · f_i ≤ KL(ρ‖π)/λ + λ·c/2 + α/λ`.

Here `c` plays the role of the sub-Gaussian variance (e.g. `c = 1/(4(m-1))`
for `[0,1]`-bounded losses averaged over `m` iid samples), and `α` absorbs
an additive Markov term `log(1/δ)` from the probabilistic shell.

Source: McAllester (1999); Catoni (2007) §1.1. -/
theorem pacbayes_mcallester_subGaussian
    [Nonempty ι] {ρ π : ι → ℝ}
    (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    (f : ι → ℝ) (lam : ℝ) (hlam : 0 < lam) (c α : ℝ)
    (hMGF : Real.log (∑ i, π i * Real.exp (lam * f i))
              ≤ lam ^ 2 * c / 2 + α) :
    ∑ i, ρ i * f i ≤ klDiv ρ π / lam + lam * c / 2 + α / lam := by
  have hdet := pacbayes_mcallester_deterministic hρ hπ f lam hlam
                  (lam ^ 2 * c / 2 + α) hMGF
  -- hdet : ∑ ρ_i * f_i ≤ (klDiv ρ π + (lam^2 * c / 2 + α)) / lam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have h_eq : (klDiv ρ π + (lam ^ 2 * c / 2 + α)) / lam
      = klDiv ρ π / lam + lam * c / 2 + α / lam := by
    field_simp
    ring
  rw [h_eq] at hdet
  exact hdet

/-! ### Optimization over `λ` (sqrt-form bound) -/

/-- Helper: if `X ≤ K/λ + λ·c/2` for **all** `λ > 0`, with `K ≥ 0` and
`c > 0`, then `X ≤ √(2·K·c)`. The optimum is attained at `λ = √(2K/c)`.

This is the Cauchy-Schwarz / AM-GM optimization step underlying the
McAllester sqrt-form bound. -/
private lemma optimized_sqrt_bound
    {X K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (h : ∀ lam, 0 < lam → X ≤ K / lam + lam * c / 2) :
    X ≤ Real.sqrt (2 * K * c) := by
  rcases eq_or_lt_of_le hK with hK0 | hK_pos
  · -- Case K = 0: bound becomes X ≤ λ·c/2 for all λ > 0; take λ → 0.
    have hK_eq : K = 0 := hK0.symm
    have h_target : Real.sqrt (2 * K * c) = 0 := by
      rw [hK_eq, mul_zero, zero_mul, Real.sqrt_zero]
    rw [h_target]
    -- Show X ≤ 0 by contradiction: if X > 0, choose lam = X/c.
    by_contra hX_neg
    have hX : 0 < X := not_le.mp hX_neg
    have h_lam_pos : 0 < X / c := div_pos hX hc
    have hh := h (X / c) h_lam_pos
    rw [hK_eq, zero_div, zero_add] at hh
    -- hh : X ≤ X/c · c / 2
    have hcne : c ≠ 0 := ne_of_gt hc
    have h_simp : X / c * c / 2 = X / 2 := by
      rw [div_mul_cancel₀ X hcne]
    rw [h_simp] at hh
    linarith
  · -- Case K > 0: choose λ = √(2K/c).
    have h2K : 0 < 2 * K := by linarith
    have h2K_ne : 2 * K ≠ 0 := ne_of_gt h2K
    have h2Kc : 0 < 2 * K / c := div_pos h2K hc
    have h2Kc_nn : 0 ≤ 2 * K / c := le_of_lt h2Kc
    have hcne : c ≠ 0 := ne_of_gt hc
    set lam := Real.sqrt (2 * K / c) with hlam_def
    have hlam_pos : 0 < lam := Real.sqrt_pos.mpr h2Kc
    have hlam_nn : 0 ≤ lam := le_of_lt hlam_pos
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
    have hlam_sq : lam ^ 2 = 2 * K / c := Real.sq_sqrt h2Kc_nn
    have hX := h lam hlam_pos
    -- From lam^2 = 2K/c, derive lam^2 * c = 2K.
    have h_lam2_c : lam ^ 2 * c = 2 * K := by
      rw [hlam_sq, div_mul_cancel₀ _ hcne]
    -- Therefore lam * c = 2K / lam.
    have h_lam_c : lam * c = 2 * K / lam := by
      have h1 : (lam * c) * lam = 2 * K := by
        have h2 : (lam * c) * lam = lam ^ 2 * c := by ring
        rw [h2, h_lam2_c]
      rw [eq_div_iff hlam_ne]
      exact h1
    have h_sum : K / lam + lam * c / 2 = 2 * K / lam := by
      have h_half : lam * c / 2 = K / lam := by
        rw [h_lam_c]; ring
      rw [h_half]; ring
    rw [h_sum] at hX
    -- Show 2K/lam = √(2Kc).
    have h_2Klam_nn : 0 ≤ 2 * K / lam :=
      div_nonneg (le_of_lt h2K) hlam_nn
    have h_2Klam_sq : (2 * K / lam) ^ 2 = 2 * K * c := by
      rw [div_pow, hlam_sq]
      field_simp
    have h_eq : 2 * K / lam = Real.sqrt (2 * K * c) := by
      rw [show (2 * K * c) = (2 * K / lam) ^ 2 from h_2Klam_sq.symm]
      exact (Real.sqrt_sq h_2Klam_nn).symm
    linarith

/-- **McAllester PAC-Bayes sqrt-form bound (deterministic core).**
Assume a sub-Gaussian-style log-MGF bound holds **uniformly in `λ > 0`**:
`∀ λ > 0, log(∑ π_i · exp(λ f_i)) ≤ λ² · c / 2 + α`.
Then for any posterior `ρ`,
`∑ ρ_i · f_i ≤ √(2 · (KL(ρ‖π) + α) · c)`.

The optimization over `λ` is the Cauchy–Schwarz step in McAllester's
proof. The uniform-in-`λ` hypothesis matches the Hoeffding-style MGF
bound that holds for every `λ` for sub-Gaussian summands. The additive
constant `α` accommodates the `log(1/δ)` term that arises from Markov's
inequality in the probabilistic shell.

Source: McAllester (1999); Catoni (2007) §1.1. -/
theorem pacbayes_mcallester_sqrt
    [Nonempty ι] {ρ π : ι → ℝ}
    (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    (f : ι → ℝ) (c α : ℝ) (hc : 0 < c) (hα : 0 ≤ α)
    (hMGF : ∀ lam, 0 < lam →
      Real.log (∑ i, π i * Real.exp (lam * f i)) ≤ lam ^ 2 * c / 2 + α) :
    ∑ i, ρ i * f i ≤ Real.sqrt (2 * (klDiv ρ π + α) * c) := by
  set K := klDiv ρ π + α with hK_def
  have hKL_nn : 0 ≤ klDiv ρ π := klDiv_nonneg hρ hπ
  have hK_nn : 0 ≤ K := by rw [hK_def]; linarith
  have h_perlam : ∀ lam, 0 < lam → ∑ i, ρ i * f i ≤ K / lam + lam * c / 2 := by
    intro lam hlam
    have hdet := pacbayes_mcallester_subGaussian hρ hπ f lam hlam c α (hMGF lam hlam)
    -- hdet : ∑ ρ_i * f_i ≤ klDiv ρ π / lam + lam * c / 2 + α / lam
    have h_split : K / lam = klDiv ρ π / lam + α / lam := by
      rw [hK_def, add_div]
    linarith
  exact optimized_sqrt_bound hK_nn hc h_perlam

/-! ### Seeger KL-form (placeholder) -/

/-
The tighter Seeger (2002) PAC-Bayes bound in KL form:

  kl(𝔼_Q[L̂] ‖ 𝔼_Q[L]) ≤ (KL(Q‖P) + ln(2√m/δ)) / m,

where `kl(p ‖ q)` is the binary-KL function, requires the binary-KL
inversion lemma `kl(p+ε ‖ p) ≥ 2ε²` (which is Pinsker for the Bernoulli)
*and* a different change-of-measure step using the Bernoulli MGF rather
than the sub-Gaussian one. We do not formalize Seeger's KL-form here;
the sqrt-form `pacbayes_mcallester_sqrt` is the looser but most commonly
cited consequence.

Source: Seeger, M. (2002). "PAC-Bayesian generalisation error bounds for
Gaussian process classification." JMLR 3, 233–269.
-/

end FormalSLT.PACBayesMcAllester
