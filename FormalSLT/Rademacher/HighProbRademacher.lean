/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Rademacher.HighProbability

/-!
# Compatibility import: high-probability Rademacher bounds

The implementation lives in `FormalSLT.Rademacher.HighProbability`. The
compatibility theorem preserves the earlier verbose namespace, import path, and
Azuma-era statement while deriving it from the stronger canonical theorem.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory
open FormalSLT.GhostSample (genGap piMeasure)
open FormalSLT.Rademacher.FiniteSample (empiricalRademacherComplexity)

noncomputable section

namespace FormalSLT.Rademacher.HighProbRademacher

variable {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/--
Compatibility wrapper for the earlier Azuma-constant statement. The canonical
theorem has the sharper denominator `2 * B ^ 2`; this wrapper weakens that
bound to the historical denominator `8 * B ^ 2`.
-/
theorem genGap_highProb_rademacher {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 2 * ∫ S', empiricalRademacherComplexity ℓ S' ∂(piMeasure μ n)
              + ε ≤ genGap μ ℓ S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := by
  calc
    (piMeasure μ n).real
          {S | 2 * ∫ S', empiricalRademacherComplexity ℓ S' ∂(piMeasure μ n)
                + ε ≤ genGap μ ℓ S}
        ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) :=
      FormalSLT.Rademacher.HighProbability.genGap_highProb_rademacher
        hB hℓ_meas hℓ_bdd hn hε
    _ ≤ Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hnum : 0 ≤ ε ^ 2 * (n : ℝ) :=
        mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg n)
      have hden_pos : 0 < 2 * B ^ 2 := by positivity
      have hden_le : 2 * B ^ 2 ≤ 8 * B ^ 2 := by
        nlinarith [sq_nonneg B]
      have hfrac :
          ε ^ 2 * (n : ℝ) / (8 * B ^ 2) ≤
            ε ^ 2 * (n : ℝ) / (2 * B ^ 2) :=
        div_le_div_of_nonneg_left hnum hden_pos hden_le
      calc
        -ε ^ 2 * (n : ℝ) / (2 * B ^ 2) =
            -(ε ^ 2 * (n : ℝ) / (2 * B ^ 2)) := by ring
        _ ≤ -(ε ^ 2 * (n : ℝ) / (8 * B ^ 2)) := neg_le_neg hfrac
        _ = -ε ^ 2 * (n : ℝ) / (8 * B ^ 2) := by ring

end FormalSLT.Rademacher.HighProbRademacher
