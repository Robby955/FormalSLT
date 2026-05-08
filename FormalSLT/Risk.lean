import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Risk, empirical risk, and uniform deviation (finite hypothesis class)

This module provides the bookkeeping for ERM-style learning bounds with a
finite, nonempty index set `ι`. The definitions are intentionally narrow:

- `risk μ ℓ i = ∫ z, ℓ i z ∂μ` — the population risk of hypothesis `i` under
  measure `μ` and a real-valued loss `ℓ : ι → Z → ℝ`.
- `empiricalRisk z ℓ i = (1/n) * ∑ k, ℓ i (z k)` — the finite-sample average
  risk for a fixed sequence `z : Fin n → Z`. No probability is involved here:
  the sample is a deterministic function, not a random variable.
- `uniformDeviation μ ℓ z = sup_i |R̂(i) - R(i)|` — the worst-case absolute
  gap between empirical and population risk over the finite class.

What this module does NOT provide:

- No PAC abstraction (no failure probability, no `δ`-confidence rearrangement).
- No bounded-loss / Hoeffding / sub-Gaussian argument: the uniform deviation
  is taken as a given quantity, not derived from a tail bound.
- No iid or independence hypotheses on `z`. The sample is whatever the user
  supplies.
- No uncountable hypothesis classes; `ι` must be a `Fintype` with `Nonempty`.
- No public-facing manifest claim. The corresponding claim
  (`erm_excessRisk_le_two_uniformDeviation` in `ERM.lean`) is **not** yet
  attached to a `claim:learning-theory::*` entry; keep it out of claim ledgers
  until reviewed.
-/

open scoped BigOperators
open MeasureTheory

namespace FormalSLT.Risk

variable {ι Z : Type*}

/-- The population risk of hypothesis `i` is the expectation of the loss
`ℓ i` under measure `μ`. -/
noncomputable def risk [MeasurableSpace Z] (μ : Measure Z) (ℓ : ι → Z → ℝ)
    (i : ι) : ℝ :=
  ∫ z, ℓ i z ∂μ

/-- The empirical risk on a fixed sequence `z : Fin n → Z` is the arithmetic
mean of the per-sample losses. This is purely a deterministic real number
once `z`, `ℓ`, and `i` are fixed. -/
noncomputable def empiricalRisk {n : ℕ} (z : Fin n → Z) (ℓ : ι → Z → ℝ)
    (i : ι) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k, ℓ i (z k)

/-- The uniform deviation between empirical and population risk over a
finite, nonempty hypothesis class. Pure deterministic real-valued quantity. -/
noncomputable def uniformDeviation [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    (μ : Measure Z) (ℓ : ι → Z → ℝ) {n : ℕ} (z : Fin n → Z) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => |empiricalRisk z ℓ i - risk μ ℓ i|)

/-- Each hypothesis's empirical-population gap is dominated by the uniform
deviation. This is just `Finset.le_sup'` instantiated; no probability. -/
lemma abs_empiricalRisk_sub_risk_le_uniformDeviation
    [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    (μ : Measure Z) (ℓ : ι → Z → ℝ) {n : ℕ} (z : Fin n → Z) (i : ι) :
    |empiricalRisk z ℓ i - risk μ ℓ i| ≤ uniformDeviation μ ℓ z := by
  refine Finset.le_sup' (f := fun j => |empiricalRisk z ℓ j - risk μ ℓ j|)
    (s := (Finset.univ : Finset ι)) ?_
  exact Finset.mem_univ i

/-- Symmetric form of the previous lemma: `|risk - empiricalRisk|` is the
same as `|empiricalRisk - risk|`. Provided so callers can match either
orientation without juggling `abs_sub_comm`. -/
lemma abs_risk_sub_empiricalRisk_le_uniformDeviation
    [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    (μ : Measure Z) (ℓ : ι → Z → ℝ) {n : ℕ} (z : Fin n → Z) (i : ι) :
    |risk μ ℓ i - empiricalRisk z ℓ i| ≤ uniformDeviation μ ℓ z := by
  rw [abs_sub_comm]
  exact abs_empiricalRisk_sub_risk_le_uniformDeviation μ ℓ z i

end FormalSLT.Risk
