import FormalSLT.AnytimeValid.SubGaussianCS
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Tutorial 3 — an anytime-valid confidence sequence

**Goal.** You are estimating a mean `θ` and want a confidence interval you may
look at *at every sample size* `n` without inflating the error: with probability
`≥ 1 − δ`, `θ` lies in the running interval `x̄_n ± w_n` for *all* `n`
simultaneously. That is a confidence sequence (CS), the anytime-valid analogue of
a fixed-`n` confidence interval. This tutorial shows the sub-Gamma CS width the
library provides, that it shrinks as data accumulates, and where the validity
guarantee lives.

This is a *tutorial*: it computes the width on concrete numbers, proves the
shrinking property (the reason you may keep peeking), and points at the coverage
theorem. Copy `worked_*` and edit the scale `σ²`, range `b`, and confidence `δ`.

Uses only:
* `FormalSLT.AnytimeValid.subGammaWidth` — the one-sided CS width
  `√(2σ² log(1/δ)/n) + b log(1/δ)/(3n)`.
* `FormalSLT.AnytimeValid.anytime_valid_confidence_sequence_subGamma` — the
  coverage guarantee (referenced; its hypotheses are measure-theoretic).

Everything is `[propext, Classical.choice, Quot.sound]`-clean.
-/

open scoped BigOperators
open FormalSLT.AnytimeValid

namespace FormalSLT.Tutorials.AnytimeValidCS

noncomputable section

/-! ## Step 0 — pick the parameters

Sub-Gaussian scale `σ² = 1`, range bound `b = 1`, confidence `δ = 1/20` (a 95%
sequence). The half-width at sample size `n` is
`w_n = √(2 · 1 · log 20 / n) + 1 · log 20 / (3n)`. -/

/-- Our confidence level `δ = 1/20`. `log(1/δ) = log 20 > 0`, which drives both
width terms. -/
theorem logInvDelta_pos : 0 < Real.log (1 / (1 / 20 : ℝ)) := by
  rw [one_div_one_div]
  exact Real.log_pos (by norm_num)

/-! ## Step 1 — the width is a real positive number

`subGammaWidth σ² b n δ` is positive whenever `0 < n` and `log(1/δ) > 0`: a
genuine, non-degenerate interval half-width. -/

/-- The CS half-width at `n = 16` for our parameters is strictly positive. -/
theorem worked_width_pos :
    0 < subGammaWidth (1 : ℝ) 1 16 (1 / 20) := by
  unfold subGammaWidth
  have hlog : 0 < Real.log (1 / (1 / 20 : ℝ)) := logInvDelta_pos
  have hsqrt : 0 < Real.sqrt (2 * 1 * Real.log (1 / (1 / 20 : ℝ)) / (16 : ℝ)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hlin : 0 < (1 : ℝ) * Real.log (1 / (1 / 20 : ℝ)) / (3 * (16 : ℝ)) := by positivity
  linarith

/-! ## Step 2 — the width shrinks as data accumulates (why you may keep peeking)

The defining advantage of a CS over a fixed-`n` interval: the half-width is
monotone *decreasing* in `n`, so accumulating data only tightens the interval,
and the coverage holds for all `n` at once. We prove the general fact that for
`0 < σ²`, `0 ≤ b`, `log(1/δ) > 0`, and `0 < m ≤ n`, the width at `n` is at most
the width at `m`. -/

/-- **The width is monotone decreasing in the sample size.** For `0 < σ²`,
`0 ≤ b`, `0 < log(1/δ)`, and `0 < m ≤ n`, `w_n ≤ w_m`. Both the `√(·/n)` term and
the `·/n` term are decreasing in `n`. -/
theorem worked_width_antitone
    {sigma2 b delta : ℝ} (hσ : 0 < sigma2) (hb : 0 ≤ b)
    (hlog : 0 < Real.log (1 / delta)) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    subGammaWidth sigma2 b n delta ≤ subGammaWidth sigma2 b m delta := by
  unfold subGammaWidth
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le hmR (by exact_mod_cast hmn)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  -- The square-root term: argument is smaller at n, and sqrt is monotone.
  have hsqrt_arg : 2 * sigma2 * Real.log (1 / delta) / (n : ℝ)
      ≤ 2 * sigma2 * Real.log (1 / delta) / (m : ℝ) := by
    apply div_le_div_of_nonneg_left _ hmR hmnR
    positivity
  have hsqrt : Real.sqrt (2 * sigma2 * Real.log (1 / delta) / (n : ℝ))
      ≤ Real.sqrt (2 * sigma2 * Real.log (1 / delta) / (m : ℝ)) :=
    Real.sqrt_le_sqrt hsqrt_arg
  -- The linear term: also decreasing in n.
  have hlin : b * Real.log (1 / delta) / (3 * (n : ℝ))
      ≤ b * Real.log (1 / delta) / (3 * (m : ℝ)) := by
    apply div_le_div_of_nonneg_left _ (by positivity) (by linarith)
    positivity
  linarith

/-- **Concrete instance of shrinking:** with our parameters the width at `n = 64`
is at most the width at `n = 16`. (Numerically `0.32 ≤ 0.67`.) -/
theorem worked_width_shrinks :
    subGammaWidth (1 : ℝ) 1 64 (1 / 20) ≤ subGammaWidth (1 : ℝ) 1 16 (1 / 20) :=
  worked_width_antitone (by norm_num) (by norm_num) logInvDelta_pos (by norm_num)
    (by norm_num)

/-! ## Step 3 — where the coverage guarantee lives

The interval `[x̄_n − w_n, x̄_n + w_n]` is the sub-Gamma confidence sequence; its
endpoints are `subGammaConfidenceLower` / `subGammaConfidenceUpper`. The
anytime-valid coverage statement is

`anytimeValidConfidenceSequence μ X θ σ² b δ`,

i.e. the *first-failure* event `{∃ n > 0, θ ∉ interval_n}` has measure `≤ δ`. It
is discharged by `anytime_valid_confidence_sequence_subGamma` from a one-sided
upper/lower split, each at budget `δ/2` (a union bound over the two tails). We
restate its type to make the guarantee visible; instantiating it requires the
measure-theoretic supermartingale hypotheses, which is beyond a getting-started
walkthrough. -/

/-- The coverage guarantee we are buying, as a `Prop`: the running interval covers
`θ` at every `n` except on an event of measure `≤ δ`. -/
def coverageGoal {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (X : ℕ → Ω → ℝ) (theta sigma2 b delta : ℝ) : Prop :=
  anytimeValidConfidenceSequence μ X theta sigma2 b delta

/-! ## How to adapt this to your problem

* **Different confidence / scale / range:** edit `δ`, `σ²`, `b`; the width and the
  shrinking property follow from `worked_width_antitone` with your numbers.
* **Get the interval endpoints:** evaluate `subGammaConfidenceLower X σ² b δ n ω`
  and `subGammaConfidenceUpper …` on your running mean.
* **Prove coverage for your process:** supply the upper/lower failure split to
  `anytime_valid_confidence_sequence_subGamma`; the supermartingale obligation is
  produced by the conditional sub-Gamma extractor in
  `FormalSLT.Concentration.SubGamma`.
-/

end

end FormalSLT.Tutorials.AnytimeValidCS
