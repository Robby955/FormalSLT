import FormalSLT.Covering.GuardedContinuousDudley

/-!
# Comprehensive tests for GuardedContinuousDudley

This file tests the guarded continuous Dudley finite-to-integral passage
with concrete example blocks beyond the basic type-checking in
`CheckGuardedContinuousDudley.lean`.

Tests cover:
- `guarded_truncatedIntegral_le_full_integral` at concrete m values
- That the truncated interval is a subset of the full interval
- The upper-sum-to-continuous passage for a constant entropy profile
- Boundary case: m = 0 (full interval equals truncated at upper half)
- Regression: the constant entropy profile satisfies the theorem hypotheses
-/

open FormalSLT.Covering.GuardedContinuousDudley
open FormalSLT.Covering.FiniteSubGaussianChaining
open MeasureTheory

/-- The truncated integral at m = 0, scale 1 is dominated by the full integral
on [0, 1/2] for any nonneg integrable function. -/
example (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntervalIntegrable f volume 0 ((1 : ℝ) / 2)) :
    ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (0 + 1)..(1 : ℝ) / 2, f ε ≤
      ∫ ε in (0 : ℝ)..(1 : ℝ) / 2, f ε :=
  guarded_truncatedIntegral_le_full_integral (m := 0)
    (entropyAtRadius := f) (by norm_num : (0 : ℝ) < 1) hf_nonneg hf_int

/-- The truncated integral at m = 1, scale 1 is dominated by the full integral
for any nonneg integrable function. -/
example (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntervalIntegrable f volume 0 ((1 : ℝ) / 2)) :
    ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (1 + 1)..(1 : ℝ) / 2, f ε ≤
      ∫ ε in (0 : ℝ)..(1 : ℝ) / 2, f ε :=
  guarded_truncatedIntegral_le_full_integral (m := 1)
    (entropyAtRadius := f) (by norm_num : (0 : ℝ) < 1) hf_nonneg hf_int

/-- The truncated integral at m = 2, scale 1 is dominated by the full integral
for any nonneg integrable function. -/
example (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntervalIntegrable f volume 0 ((1 : ℝ) / 2)) :
    ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (2 + 1)..(1 : ℝ) / 2, f ε ≤
      ∫ ε in (0 : ℝ)..(1 : ℝ) / 2, f ε :=
  guarded_truncatedIntegral_le_full_integral (m := 2)
    (entropyAtRadius := f) (by norm_num : (0 : ℝ) < 1) hf_nonneg hf_int

/-- The truncated integral with scale 2 (not just 1) is also dominated. -/
example (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntervalIntegrable f volume 0 ((2 : ℝ) / 2)) :
    ∫ ε in (2 : ℝ) / (2 : ℝ) ^ (1 + 1)..(2 : ℝ) / 2, f ε ≤
      ∫ ε in (0 : ℝ)..(2 : ℝ) / 2, f ε :=
  guarded_truncatedIntegral_le_full_integral (m := 1)
    (entropyAtRadius := f) (radiusScale := 2) (by norm_num : (0 : ℝ) < 2)
    hf_nonneg hf_int

/-- The constant entropy profile 1 satisfies guarded_truncatedIntegral_le_full_integral
at m = 0. Concretely, ∫_{1/2}^{1/2} 1 = 0 ≤ ∫_0^{1/2} 1 = 1/2. -/
example :
    ∫ _ in ((1 : ℝ) / (2 : ℝ) ^ (0 + 1))..((1 : ℝ) / 2), (1 : ℝ) ≤
      ∫ _ in (0 : ℝ)..((1 : ℝ) / 2), (1 : ℝ) := by
  apply guarded_truncatedIntegral_le_full_integral (m := 0) (entropyAtRadius := fun _ => 1)
  · norm_num
  · intro x; norm_num
  · exact intervalIntegral.intervalIntegrable_const

/-- The constant entropy profile 5 satisfies the domination at m = 1. -/
example :
    ∫ _ in ((1 : ℝ) / (2 : ℝ) ^ (1 + 1))..((1 : ℝ) / 2), (5 : ℝ) ≤
      ∫ _ in (0 : ℝ)..((1 : ℝ) / 2), (5 : ℝ) := by
  apply guarded_truncatedIntegral_le_full_integral (m := 1) (entropyAtRadius := fun _ => 5)
  · norm_num
  · intro x; norm_num
  · exact intervalIntegral.intervalIntegrable_const

/-- Passing truncated bounds for a constant entropy profile yields the continuous bound.
This tests the truncated-bounds API shape with a concrete constant process. -/
example {Ω T : Type*} [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (supFunctional : Ω → ℝ)
    (htruncated : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        finiteExpectation P.weight supFunctional ≤
          5 + 4 * Real.sqrt (2 * P.varianceProxy) *
            (∫ _ in ((1 : ℝ) / (2 : ℝ) ^ (m + 1))..((1 : ℝ) / 2), (1 : ℝ)) + eta) :
    finiteExpectation P.weight supFunctional ≤
      5 + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ _ in (0 : ℝ)..((1 : ℝ) / 2), (1 : ℝ)) :=
  guarded_continuous_dudley_entropy_integral_nonempty_of_truncated_bounds
    (P := P) (coarseBudget := 5) (radiusScale := 1)
    (entropyAtRadius := fun _ => 1)
    (supFunctional := supFunctional)
    (by norm_num)
    (fun _ => zero_le_one)
    intervalIntegral.intervalIntegrable_const
    htruncated

/-- GuardedAntitoneOnDyadicAnnulus always holds for a constant function on any annulus. -/
example (c : ℝ) (r : ℝ) (j : ℕ) :
    FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
      (fun _ => c) r j := by
  intro _ _ _
  exact le_refl c

/-- For a decreasing function, the guarded annulus condition holds: the smaller
radius gets the larger value. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    (fun ε => -ε) (1 : ℝ) 0 := by
  intro ε hleft hright
  simp
  exact hright

/-- Boundary case: guarded_truncatedIntegral_le_full_integral at m = 0 is
the statement that the integral on [1/2, 1/2] ≤ integral on [0, 1/2]. -/
example (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntervalIntegrable f volume 0 ((1 : ℝ) / 2)) :
    ∫ ε in ((1 : ℝ) / 2)..((1 : ℝ) / 2), f ε ≤
      ∫ ε in (0 : ℝ)..((1 : ℝ) / 2), f ε := by
  have h := guarded_truncatedIntegral_le_full_integral (m := 0)
    (entropyAtRadius := f) (by norm_num : (0 : ℝ) < 1) hf_nonneg hf_int
  simpa using h