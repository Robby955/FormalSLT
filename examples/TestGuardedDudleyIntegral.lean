import FormalSLT.Covering.GuardedDudleyIntegral

/-!
# Comprehensive tests for GuardedDudleyIntegral

This file tests the guarded positive-radius Dudley integral module with
concrete example blocks that go beyond the basic type-checking in
`CheckGuardedDudleyIntegral.lean`.

Tests cover:
- `GuardedAntitoneOnDyadicAnnulus` definition unfolding and instances
- `positiveRadiusReciprocalEntropy` concrete evaluation
- Witness profile global non-antitonicity
- Guarded property of the reciprocal witness at specific dyadic levels
- The truncated bridge for m = 0 (base case) and m = 1
- Negative case: global antitone does not hold for the reciprocal witness
-/

open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.FiniteSubGaussianChaining

/-- The reciprocal witness evaluates to the reciprocal on positive inputs. -/
example : positiveRadiusReciprocalEntropy 1 = 1 := by
  simp [positiveRadiusReciprocalEntropy]

/-- The reciprocal witness evaluates to zero at zero. -/
example : positiveRadiusReciprocalEntropy 0 = 0 := by
  simp [positiveRadiusReciprocalEntropy]

/-- The reciprocal witness evaluates to zero on negative inputs. -/
example : positiveRadiusReciprocalEntropy (-1) = 0 := by
  simp [positiveRadiusReciprocalEntropy]

/-- The reciprocal witness evaluates to 2 at 1/2 (positive radius). -/
example : positiveRadiusReciprocalEntropy ((1 : ℝ) / 2) = 2 := by
  norm_num [positiveRadiusReciprocalEntropy]

/-- The reciprocal witness at radius 1 is strictly greater than its value at
radius 2, demonstrating local monotone decrease (as a function of ε⁻¹, it
increases, meaning it decreases with ε). -/
example : positiveRadiusReciprocalEntropy 1 ≤ positiveRadiusReciprocalEntropy ((1 : ℝ) / 2) := by
  norm_num [positiveRadiusReciprocalEntropy]

/-- The reciprocal witness is NOT globally antitone: f(0) = 0 but f(1) = 1,
contradicting antitone ordering at `(0, 1)`. -/
example : ¬ Antitone (positiveRadiusReciprocalEntropy) :=
  not_globalAntitone_positiveRadiusReciprocalEntropy

/-- The guarded annulus property holds at j = 0, radiusScale = 1. -/
example : GuardedAntitoneOnDyadicAnnulus positiveRadiusReciprocalEntropy 1 0 :=
  positiveRadiusReciprocalEntropy_guarded (by norm_num : (0 : ℝ) < 1) 0

/-- The guarded annulus property holds at j = 1, radiusScale = 1. -/
example : GuardedAntitoneOnDyadicAnnulus positiveRadiusReciprocalEntropy 1 1 :=
  positiveRadiusReciprocalEntropy_guarded (by norm_num : (0 : ℝ) < 1) 1

/-- The guarded annulus property holds at j = 2, radiusScale = 2. -/
example : GuardedAntitoneOnDyadicAnnulus positiveRadiusReciprocalEntropy 2 2 :=
  positiveRadiusReciprocalEntropy_guarded (by norm_num : (0 : ℝ) < 2) 2

/-- The guarded annulus condition at j=0 for the reciprocal is verified manually:
on the annulus [1/4, 1/2], the function ε⁻¹ is decreasing. -/
example : ∀ ε : ℝ, (1 : ℝ) / 4 ≤ ε → ε ≤ (1 : ℝ) / 2 →
    positiveRadiusReciprocalEntropy ((1 : ℝ) / 2) ≤ positiveRadiusReciprocalEntropy ε := by
  intro ε hleft hright
  have hε_pos : 0 < ε := by linarith
  simp [positiveRadiusReciprocalEntropy, hε_pos, (by norm_num : (0 : ℝ) < 1 / 2)]
  exact one_div_le_one_div_of_le hε_pos hright

/-- The reciprocal witness is integrable on the dyadic annulus at j = 0, scale 1. -/
example : MeasureTheory.IntervalIntegrable positiveRadiusReciprocalEntropy
    MeasureTheory.volume ((1 : ℝ) / 4) ((1 : ℝ) / 2) := by
  have h := positiveRadiusReciprocalEntropy_intervalIntegrable_dyadic
    (by norm_num : (0 : ℝ) < 1) 0
  norm_num at h
  exact h

/-- The reciprocal witness is integrable on the dyadic annulus at j = 1, scale 1. -/
example : MeasureTheory.IntervalIntegrable positiveRadiusReciprocalEntropy
    MeasureTheory.volume ((1 : ℝ) / 8) ((1 : ℝ) / 4) := by
  have h := positiveRadiusReciprocalEntropy_intervalIntegrable_dyadic
    (by norm_num : (0 : ℝ) < 1) 1
  norm_num at h
  exact h

/-- GuardedAntitoneOnDyadicAnnulus unfolds to the expected quantified statement. -/
example (f : ℝ → ℝ) (r : ℝ) (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus f r j ↔
      ∀ ε : ℝ, r / (2 : ℝ) ^ (j + 2) ≤ ε → ε ≤ r / (2 : ℝ) ^ (j + 1) →
        f (r / (2 : ℝ) ^ (j + 1)) ≤ f ε := by
  rfl

/-- The truncated bridge applies for m = 0 and a constant entropy profile.
At m = 0, the sum is empty (= 0) and the degenerate integral is also 0. -/
example : FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum (1 : ℝ) 0
    (fun _ : ℝ => (1 : ℝ)) ≤
    2 * ∫ _ in (1 : ℝ) / (2 : ℝ) ^ (0 + 1)..(1 : ℝ) / 2,
      (1 : ℝ) := by
  have hlhs : FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum (1 : ℝ) 0
      (fun _ : ℝ => (1 : ℝ)) = 0 := by
    simp [FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum]
  rw [hlhs]
  positivity

/-- The truncated bridge for the reciprocal witness applies at m = 0, scale 1. -/
example : FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum (1 : ℝ) 0
    positiveRadiusReciprocalEntropy ≤
    2 * ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (0 + 1)..(1 : ℝ) / 2,
      positiveRadiusReciprocalEntropy ε :=
  positiveRadiusReciprocalEntropy_truncated_bridge 0 (by norm_num : (0 : ℝ) < 1)

/-- The truncated bridge for the reciprocal witness applies at m = 1, scale 1. -/
example : FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum (1 : ℝ) 1
    positiveRadiusReciprocalEntropy ≤
    2 * ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (1 + 1)..(1 : ℝ) / 2,
      positiveRadiusReciprocalEntropy ε :=
  positiveRadiusReciprocalEntropy_truncated_bridge 1 (by norm_num : (0 : ℝ) < 1)

/-- The truncated bridge for the reciprocal witness applies at m = 2, scale 1. -/
example : FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum (1 : ℝ) 2
    positiveRadiusReciprocalEntropy ≤
    2 * ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (2 + 1)..(1 : ℝ) / 2,
      positiveRadiusReciprocalEntropy ε :=
  positiveRadiusReciprocalEntropy_truncated_bridge 2 (by norm_num : (0 : ℝ) < 1)

/-- The shifted-annulus sum inequality holds for m = 1, reciprocal, scale 1. -/
example :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum (1 : ℝ) 1
        positiveRadiusReciprocalEntropy ≤
      2 * ∑ j ∈ Finset.range 1,
        ∫ ε in (1 : ℝ) / (2 : ℝ) ^ (j + 2)..(1 : ℝ) / (2 : ℝ) ^ (j + 1),
          positiveRadiusReciprocalEntropy ε :=
  finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum_guarded
    (m := 1) (radiusScale := 1) (entropyAtRadius := positiveRadiusReciprocalEntropy)
    (by norm_num)
    (fun j _ => positiveRadiusReciprocalEntropy_guarded (by norm_num) j)
    (fun j _ => positiveRadiusReciprocalEntropy_intervalIntegrable_dyadic (by norm_num) j)

/-- Boundary case: the guarded annulus at a large dyadic level holds. -/
example : GuardedAntitoneOnDyadicAnnulus positiveRadiusReciprocalEntropy 1 10 :=
  positiveRadiusReciprocalEntropy_guarded (by norm_num : (0 : ℝ) < 1) 10

/-- Regression: global antitonicity failure is witnessed at 0 and 1.
The function value at 0 is 0 (since we use `if 0 < ε then ε⁻¹ else 0`),
but value at 1 is 1. An antitone function at (0 ≤ 1) would require
f(1) ≤ f(0), i.e., 1 ≤ 0, which is false. -/
example : positiveRadiusReciprocalEntropy 1 = 1 ∧
    positiveRadiusReciprocalEntropy 0 = 0 ∧
    ¬ (positiveRadiusReciprocalEntropy 1 ≤ positiveRadiusReciprocalEntropy 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [positiveRadiusReciprocalEntropy]
  · simp [positiveRadiusReciprocalEntropy]
  · simp [positiveRadiusReciprocalEntropy]
    norm_num