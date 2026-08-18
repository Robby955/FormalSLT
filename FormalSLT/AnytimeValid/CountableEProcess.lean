/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.DyadicEpochCS
import FormalSLT.AnytimeValid.EProcess

/-!
# Countable mixtures of e-processes

This module packages the countable supermartingale interchange theorem from
`DyadicEpochCS` as a reusable closure rule for e-processes.  The weights and
component processes are fixed before observing the path.  The theorem is
countable in the catalog index and countable in time; it does not permit a
data-dependent change of the mixing weights.

The explicit adaptedness, integrability, and set-integral summability package
is the exact analytic interface needed by
`countableWeightedSupermartingale_tsum`.  Concrete bounded-process modules can
discharge this package once and then reuse the closure theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ}

/-- A countable weighted series of real-valued processes. -/
def countableWeightedProcess
    (weight : ℕ → ℝ) (E : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑' j, weight j * E j n ω

/-- Pointwise nonnegativity of a countable weighted process series. -/
theorem countableWeightedProcess_nonneg
    {weight : ℕ → ℝ} {E : ℕ → ℕ → Ω → ℝ}
    (hweight : ∀ j, 0 ≤ weight j)
    (hE : ∀ j n ω, 0 ≤ E j n ω) :
    0 ≤ countableWeightedProcess weight E := by
  intro n ω
  exact tsum_nonneg fun j ↦ mul_nonneg (hweight j) (hE j n ω)

/-- A normalized countable mixture starts at one when every component does. -/
theorem countableWeightedProcess_zero
    {weight : ℕ → ℝ} {E : ℕ → ℕ → Ω → ℝ}
    (hweight : HasSum weight 1)
    (hE : ∀ j ω, E j 0 ω = 1) (ω : Ω) :
    countableWeightedProcess weight E 0 ω = 1 := by
  unfold countableWeightedProcess
  have hterm : (fun j ↦ weight j * E j 0 ω) = weight := by
    funext j
    rw [hE j ω, mul_one]
  rw [hterm, hweight.tsum_eq]

/--
A normalized countable mixture of e-processes is an e-process, provided the
countable series satisfies the adaptedness, integrability, and set-integral
summability conditions needed to interchange its sum with conditional
expectations.

Strict positivity of the weights is not required for closure.  It is required
only by downstream selected-atom bounds that divide by the selected weight.
-/
theorem countableWeightedProcess_eProcess
    [IsFiniteMeasure μ]
    {weight : ℕ → ℝ} {E : ℕ → ℕ → Ω → ℝ}
    (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    (hE : ∀ j, EProcess μ ℱ (E j))
    (hadapted : StronglyAdapted ℱ (countableWeightedProcess weight E))
    (hintegrable : ∀ n, Integrable (countableWeightedProcess weight E n) μ)
    (hsummable_integral_norm :
      ∀ n, ∀ s : Set Ω, MeasurableSet s →
        Summable fun j ↦ ∫ ω in s, ‖weight j * E j n ω‖ ∂μ) :
    EProcess μ ℱ (countableWeightedProcess weight E) := by
  refine
    { nonneg := countableWeightedProcess_nonneg hweight_nonneg
        (fun j n ω ↦ (hE j).nonneg n ω)
      start_one := countableWeightedProcess_zero hweight_sum_one
        (fun j ω ↦ (hE j).start_one ω)
      supermartingale := ?_ }
  unfold countableWeightedProcess at hadapted hintegrable ⊢
  exact countableWeightedSupermartingale_tsum
    hweight_nonneg (fun j ↦ (hE j).supermartingale)
    hadapted hintegrable hsummable_integral_norm

end

end FormalSLT.AnytimeValid
