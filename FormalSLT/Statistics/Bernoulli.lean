/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Concentration.NamedTails

/-!
# Bernoulli distribution bridge

A user who wants "a tail bound for Bernoulli(p)" should not have to build the
finite distribution and discharge the centering / boundedness / variance
hypotheses of the concentration engine by hand. This file packages the
Bernoulli law as a concrete object on the two-atom type `Bool` and attaches the
facts the named tail corollaries need:

* `bernoulliPMF p` — the probability mass function `P(true) = p`, `P(false) = 1 - p`.
* `bernoulliMean p` / `bernoulliVariance p` — the textbook moments `p` and
  `p(1 - p)`, each proved equal to the corresponding pmf-weighted sum.
* `bernoulliCentered p` — the centered observable `1{·} - p`, with its centering,
  two-sided bound, and variance proxy discharged as named lemmas.
* `bernoulli_bernstein_tail` — the two-sided Bernstein tail for the centered
  Bernoulli observable, obtained by feeding those lemmas to
  `FormalSLT.Concentration.NamedTails.bernstein_tail`. This is the user-facing
  "Bernoulli tail" that was previously only reachable by hand-building the
  instance.

No new analytic content is introduced: everything is the Bernoulli specialization
of results already in the library, computed on the explicit two-atom support.
-/

open scoped BigOperators
open FormalSLT.Concentration.NamedTails

namespace FormalSLT.Statistics.Bernoulli

noncomputable section

/-- The Bernoulli probability mass function on `Bool`: `P(true) = p`,
`P(false) = 1 - p`. -/
def bernoulliPMF (p : ℝ) : Bool → ℝ := fun b => if b then p else 1 - p

/-- The Bernoulli indicator observable: `X true = 1`, `X false = 0`. -/
def bernoulliIndicator : Bool → ℝ := fun b => if b then 1 else 0

/-- The mean of Bernoulli(p), defined as the pmf-weighted sum of the indicator. -/
def bernoulliMean (p : ℝ) : ℝ := ∑ b, bernoulliPMF p b * bernoulliIndicator b

/-- The variance of Bernoulli(p), the pmf-weighted second moment of the
centered indicator. -/
def bernoulliVariance (p : ℝ) : ℝ :=
  ∑ b, bernoulliPMF p b * (bernoulliIndicator b - bernoulliMean p) ^ 2

/-- The centered Bernoulli observable `X - p`: value `1 - p` on `true`,
`-p` on `false`. -/
def bernoulliCentered (p : ℝ) : Bool → ℝ :=
  fun b => bernoulliIndicator b - p

/-! ### The pmf is a genuine probability mass function -/

/-- `bernoulliPMF p` is nonnegative when `0 ≤ p ≤ 1`. -/
theorem bernoulliPMF_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ b, 0 ≤ bernoulliPMF p b := by
  intro b; cases b <;> simp [bernoulliPMF] <;> linarith

/-- `bernoulliPMF p` sums to one. -/
theorem bernoulliPMF_sum (p : ℝ) : ∑ b, bernoulliPMF p b = 1 := by
  rw [Fintype.sum_bool]; simp only [bernoulliPMF, if_true, Bool.false_eq_true,
    if_false]; ring

/-! ### Mean and variance match the textbook values -/

/-- **The Bernoulli mean is `p`.** `E[X] = p`. -/
theorem bernoulliMean_eq (p : ℝ) : bernoulliMean p = p := by
  unfold bernoulliMean bernoulliPMF bernoulliIndicator
  rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]; ring

/-- **The Bernoulli variance is `p(1 - p)`.** `Var(X) = p(1 - p)`. -/
theorem bernoulliVariance_eq (p : ℝ) : bernoulliVariance p = p * (1 - p) := by
  unfold bernoulliVariance bernoulliPMF bernoulliIndicator
  rw [bernoulliMean_eq, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]; ring

/-! ### The centered observable satisfies the Bernstein hypotheses -/

/-- The centered Bernoulli observable is centered: `∑ p_b · (X_b - p) = 0`. -/
theorem bernoulliCentered_center (p : ℝ) :
    ∑ b, bernoulliPMF p b * bernoulliCentered p b = 0 := by
  unfold bernoulliCentered bernoulliPMF bernoulliIndicator
  rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]; ring

/-- The centered Bernoulli observable is two-sidedly bounded by `1`:
`|X_b - p| ≤ 1` for `0 ≤ p ≤ 1`. -/
theorem bernoulliCentered_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ b, |bernoulliCentered p b| ≤ 1 := by
  intro b; cases b <;> simp [bernoulliCentered, bernoulliIndicator, abs_le] <;>
    constructor <;> linarith

/-- The variance proxy of the centered Bernoulli observable equals the variance
`p(1 - p)`: `∑ p_b · (X_b - p)² = p(1 - p)`. -/
theorem bernoulliCentered_var (p : ℝ) :
    ∑ b, bernoulliPMF p b * bernoulliCentered p b ^ 2 = p * (1 - p) := by
  unfold bernoulliCentered bernoulliPMF bernoulliIndicator
  rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]; ring

/-! ### The user-facing Bernoulli tail -/

/-- **Two-sided Bernstein tail for Bernoulli(p).**

For `0 < p < 1` and a deviation level `0 ≤ ε`, the centered Bernoulli observable
`X - p` obeys the Bernstein tail

`P(|X - p| ≥ ε) ≤ 2 · exp(-ε² / (2 (p(1 - p) + ε / 3)))`.

This is the Bernoulli specialization of
`FormalSLT.Concentration.NamedTails.bernstein_tail` with bound `b = 1` and the
exact variance `v = p(1 - p)`; the centering, boundedness, and variance
hypotheses are discharged by `bernoulliCentered_center`, `bernoulliCentered_bound`,
and `bernoulliCentered_var`. A user gets a Bernoulli tail with one call instead
of rebuilding the finite distribution. -/
theorem bernoulli_bernstein_tail {p ε : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) :
    ∑ b ∈ Finset.univ.filter (fun b => ε ≤ |bernoulliCentered p b|), bernoulliPMF p b
      ≤ 2 * Real.exp (-(ε ^ 2) / (2 * (p * (1 - p) + 1 * ε / 3))) := by
  have hvar_pos : 0 < p * (1 - p) := by
    have : 0 < 1 - p := by linarith
    positivity
  have hvar_le : ∑ b, bernoulliPMF p b * bernoulliCentered p b ^ 2 ≤ p * (1 - p) :=
    le_of_eq (bernoulliCentered_var p)
  exact bernstein_tail (bernoulliPMF p) (bernoulliCentered p)
    (b := 1) (v := p * (1 - p)) (eps := ε)
    (by norm_num) hvar_pos hε
    (bernoulliPMF_nonneg hp0.le hp1.le) (bernoulliPMF_sum p)
    (bernoulliCentered_center p) (bernoulliCentered_bound hp0.le hp1.le) hvar_le

end

end FormalSLT.Statistics.Bernoulli
