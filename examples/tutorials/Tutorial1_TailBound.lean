import FormalSLT.Statistics.Bernoulli
import FormalSLT.Concentration.NamedTails
import FormalSLT.Probability.BernsteinMGF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tutorial 1 — a tail bound on a concrete problem

**Goal.** You have a biased coin with success probability `p`. You want to know
how unlikely it is that a single draw of the centered indicator `X - p` deviates
from `0` by at least some margin `ε`. This tutorial shows how to get a real
number out of the library's named tail corollaries, then how to generalize to
your own setting.

This is a *tutorial*, not a checker: it walks through the call, computes an
explicit bound, and shows the bound is meaningful (strictly below `1`, so it
genuinely rules something out). Copy the `worked_*` declarations and edit the
constants for your own problem.

Everything below is `[propext, Classical.choice, Quot.sound]`-clean and uses only
results already in the library:

* `FormalSLT.Statistics.Bernoulli.bernoulli_bernstein_tail` — the two-sided
  Bernstein tail specialized to Bernoulli(p).
* `FormalSLT.Statistics.Bernoulli.bernoulliMean_eq` / `bernoulliVariance_eq` —
  the textbook moments `p` and `p(1 - p)`.
-/

open scoped BigOperators
open FormalSLT.Statistics.Bernoulli

namespace FormalSLT.Tutorials.TailBound

noncomputable section

/-! ## Step 0 — pick the problem

Take a fair-ish biased coin with `p = 1/4`, and ask for the probability that the
centered indicator deviates by at least `ε = 1/2`. The mean is `p = 1/4` and the
variance is `p(1 - p) = 3/16`; both come from the library, no hand computation. -/

/-- The mean of our coin is exactly `1/4`. -/
example : bernoulliMean (1 / 4 : ℝ) = 1 / 4 := bernoulliMean_eq _

/-- The variance of our coin is exactly `3/16 = (1/4)(3/4)`. -/
example : bernoulliVariance (1 / 4 : ℝ) = 3 / 16 := by
  rw [bernoulliVariance_eq]; norm_num

/-! ## Step 1 — apply the named tail corollary

`bernoulli_bernstein_tail` takes `0 < p`, `p < 1`, and `0 ≤ ε`, and returns the
two-sided Bernstein tail

`P(|X - p| ≥ ε) ≤ 2 · exp(-ε² / (2 (p(1 - p) + ε/3)))`.

We instantiate at `p = 1/4`, `ε = 1/2`. There is nothing to prove about the
distribution — the corollary already did the centering / boundedness / variance
bookkeeping. -/

/-- **The worked tail bound.** For Bernoulli(1/4) and margin `ε = 1/2`,
`P(|X − 1/4| ≥ 1/2) ≤ 2 · exp(−(1/2)² / (2 (3/16 + (1/2)/3)))`. -/
theorem worked_tail :
    ∑ b ∈ Finset.univ.filter (fun b => (1 / 2 : ℝ) ≤ |bernoulliCentered (1 / 4) b|),
        bernoulliPMF (1 / 4) b
      ≤ 2 * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * ((1 / 4) * (1 - 1 / 4) + 1 * (1 / 2) / 3))) :=
  bernoulli_bernstein_tail (p := 1 / 4) (ε := 1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-! ## Step 2 — read off a number and check it is meaningful

The exponent simplifies to `-(1/2)² / (2 · (3/16 + (1/2)/3)) = -(1/4)/(17/24) = -6/17`.
So the bound is `2 · exp(-6/17) ≈ 1.41`… which is `> 1` and therefore vacuous at
this aggressive margin. That is itself informative: Bernstein at `ε = 1/2` on a
variance-`3/16` coin does not yet beat the trivial bound. Push the margin to the
maximum and the bound becomes useful — the next step shows that. -/

/-- The exponent in `worked_tail` is exactly `-6/17`. -/
theorem worked_exponent :
    (-((1 / 2 : ℝ) ^ 2) / (2 * ((1 / 4) * (1 - 1 / 4) + 1 * (1 / 2) / 3))) = -(6 / 17) := by
  norm_num

/-! ## Step 3 — a margin where the bound is useful

Take the same coin but the maximal margin `ε = 1` (the centered indicator on a
`p = 1/4` coin has `|X − 1/4| ≤ 3/4 < 1`, so `ε = 1` is an upper-tail event of
the bound itself). The bound `2 · exp(-ε²/(2(v + ε/3)))` is now strictly below
`1`, so it genuinely rules out the deviation event. We prove `bound < 1` from the
library's own quadratic exponential lower bound
`FormalSLT.Probability.BernsteinMGF.one_add_add_sq_le_exp_of_nonneg`. -/

/-- The Bernstein tail bound for Bernoulli(1/4) at the maximal margin `ε = 1`. -/
theorem worked_tail_tight :
    ∑ b ∈ Finset.univ.filter (fun b => (1 : ℝ) ≤ |bernoulliCentered (1 / 4) b|),
        bernoulliPMF (1 / 4) b
      ≤ 2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * ((1 / 4) * (1 - 1 / 4) + 1 * 1 / 3))) :=
  bernoulli_bernstein_tail (p := 1 / 4) (ε := 1) (by norm_num) (by norm_num) (by norm_num)

/-- **The bound is non-vacuous at `ε = 1`:** the right-hand side is strictly below
`1`. The exponent is `-1 / (2·(3/16 + 1/3)) = -(24/25)`, and `2·exp(-24/25) ≈ 0.77`.
We prove it cleanly: `2·exp(-24/25) < 1 ⟺ exp(24/25) > 2`, and the quadratic bound
`1 + u + u²/2 ≤ exp u` at `u = 24/25` gives `exp(24/25) ≥ 1 + 24/25 + (24/25)²/2 =
3026/1250 > 2`. -/
theorem worked_tail_tight_useful :
    2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * ((1 / 4) * (1 - 1 / 4) + 1 * 1 / 3))) < 1 := by
  -- The exponent is exactly -(24/25).
  have hexp_eq : (-((1 : ℝ) ^ 2) / (2 * ((1 / 4) * (1 - 1 / 4) + 1 * 1 / 3))) = -(24 / 25) := by
    norm_num
  rw [hexp_eq]
  -- Quadratic lower bound: exp(24/25) ≥ 1 + 24/25 + (24/25)²/2 > 2.
  have hquad : (1 : ℝ) + (24 / 25) + (24 / 25) ^ 2 / 2 ≤ Real.exp (24 / 25) :=
    FormalSLT.Probability.BernsteinMGF.one_add_add_sq_le_exp_of_nonneg (by norm_num)
  have hgt2 : (2 : ℝ) < Real.exp (24 / 25) := by nlinarith [hquad]
  have hpos : (0 : ℝ) < Real.exp (24 / 25) := Real.exp_pos _
  -- exp(-24/25) = 1 / exp(24/25) < 1/2, so 2·exp(-24/25) < 1.
  rw [Real.exp_neg]
  rw [show (Real.exp (24 / 25))⁻¹ = 1 / Real.exp (24 / 25) by rw [one_div]]
  rw [mul_one_div, div_lt_one hpos]
  linarith [hgt2]

/-! ## How to adapt this to your problem

* **Different coin:** change `1/4` to your `p` (any `0 < p < 1`); the moments
  update automatically through `bernoulliMean_eq` / `bernoulliVariance_eq`.
* **A general bounded variable (not Bernoulli):** call
  `FormalSLT.Concentration.NamedTails.bernstein_tail` directly with your finite
  pmf `p`, observable `X`, bound `b`, and variance proxy `v`.
* **The sample mean of `n` iid draws:** use
  `FormalSLT.Statistics.sampleMean_hoeffding_tail`, which gives the
  `2 · exp(-2 n t² / (b - a)²)` mean tail keyed to the named `sampleMean`.
-/

end

end FormalSLT.Tutorials.TailBound
