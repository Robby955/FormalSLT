import FormalSLT.Covering.ContinuousDudleyUnitInterval

/-!
# Comprehensive tests for ContinuousDudleyUnitInterval

This file tests the guarded unit-interval Dudley capstone module with
concrete example blocks beyond the basic type-checking in
`CheckContinuousDudleyUnitInterval.lean`.

Tests cover:
- Concrete evaluation of `unitIntervalEntropyProfile` at specific radii
- Concrete evaluation of `unitIntervalDivergingEntropyProfile` at specific radii
- Nonnegativity at specific inputs
- Antitone property verified at specific pairs
- Nonconstancy and positive integral mass witnesses
- Profile dominance at specific dyadic indices
- Dyadic cover count profile dominates itself exactly (reflexivity)
-/

open FormalSLT.Covering.ContinuousDudleyUnitInterval
open FormalSLT.Covering.UnitIntervalDudley

/-- The bounded entropy profile at ε = 0 is 20 + exp(0) = 21. -/
example : unitIntervalEntropyProfile 0 = 20 + Real.exp 0 := by
  simp [unitIntervalEntropyProfile]

/-- The bounded entropy profile at ε = 0 simplifies to 21 (since exp 0 = 1). -/
example : unitIntervalEntropyProfile 0 = 21 := by
  simp [unitIntervalEntropyProfile]

/-- The bounded entropy profile is nonneg at ε = 0. -/
example : 0 ≤ unitIntervalEntropyProfile 0 :=
  unitIntervalEntropyProfile_nonneg 0

/-- The bounded entropy profile is nonneg at ε = 1. -/
example : 0 ≤ unitIntervalEntropyProfile 1 :=
  unitIntervalEntropyProfile_nonneg 1

/-- The bounded entropy profile is nonneg at a negative argument. -/
example : 0 ≤ unitIntervalEntropyProfile (-5) :=
  unitIntervalEntropyProfile_nonneg (-5)

/-- The bounded entropy profile is antitone: smaller ε gives larger value.
Concretely, profile at 0 ≥ profile at 1. -/
example : unitIntervalEntropyProfile 1 ≤ unitIntervalEntropyProfile 0 :=
  unitIntervalEntropyProfile_antitone (le_refl 0 |>.trans (by norm_num : (0 : ℝ) ≤ 1))

/-- The bounded profile is antitone: profile at 0.5 ≥ profile at 1. -/
example : unitIntervalEntropyProfile 1 ≤ unitIntervalEntropyProfile ((1 : ℝ) / 2) :=
  unitIntervalEntropyProfile_antitone (by norm_num : (1 : ℝ) / 2 ≤ 1)

/-- The guarded annulus property holds at j = 0 for the bounded profile. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalEntropyProfile 1 0 :=
  unitIntervalEntropyProfile_guarded 0

/-- The guarded annulus property holds at j = 3 for the bounded profile. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalEntropyProfile 1 3 :=
  unitIntervalEntropyProfile_guarded 3

/-- The bounded profile is interval integrable on [0, 1/2]. -/
example : MeasureTheory.IntervalIntegrable unitIntervalEntropyProfile
    MeasureTheory.volume 0 ((1 : ℝ) / 2) :=
  unitIntervalEntropyProfile_intervalIntegrable 0 ((1 : ℝ) / 2)

/-- The bounded profile is interval integrable on any compact interval. -/
example : MeasureTheory.IntervalIntegrable unitIntervalEntropyProfile
    MeasureTheory.volume (-3) 10 :=
  unitIntervalEntropyProfile_intervalIntegrable (-3) 10

/-- The bounded entropy profile at 0 is NOT equal to at 1: the profile is
strictly decreasing (since exp is strictly decreasing composed with neg). -/
example : unitIntervalEntropyProfile 0 ≠ unitIntervalEntropyProfile 1 :=
  unitInterval_entropyProfile_nonconstant

/-- The bounded entropy profile has positive integral mass on [0, 1/2]. -/
example : 0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε :=
  unitInterval_entropyProfile_integral_positive

/-- The diverging entropy profile evaluates to 0 at 0 (off positive radii). -/
example : unitIntervalDivergingEntropyProfile 0 = 0 := by
  simp [unitIntervalDivergingEntropyProfile]

/-- The diverging entropy profile evaluates to 0 at negative inputs. -/
example : unitIntervalDivergingEntropyProfile (-1) = 0 := by
  simp [unitIntervalDivergingEntropyProfile]

/-- The diverging entropy profile is nonneg at 0. -/
example : 0 ≤ unitIntervalDivergingEntropyProfile 0 :=
  unitIntervalDivergingEntropyProfile_nonneg 0

/-- The diverging entropy profile is nonneg at 1. -/
example : 0 ≤ unitIntervalDivergingEntropyProfile 1 :=
  unitIntervalDivergingEntropyProfile_nonneg 1

/-- The diverging entropy profile is nonneg at negative inputs. -/
example : 0 ≤ unitIntervalDivergingEntropyProfile (-10) :=
  unitIntervalDivergingEntropyProfile_nonneg (-10)

/-- The diverging entropy profile at positive ε evaluates to 20 * ε^(-1/2). -/
example : unitIntervalDivergingEntropyProfile 1 = 20 := by
  simp [unitIntervalDivergingEntropyProfile]

/-- The diverging entropy profile satisfies the guarded annulus property at j = 0. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalDivergingEntropyProfile 1 0 :=
  unitIntervalDivergingEntropyProfile_guarded 0

/-- The diverging entropy profile satisfies the guarded annulus property at j = 5. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalDivergingEntropyProfile 1 5 :=
  unitIntervalDivergingEntropyProfile_guarded 5

/-- The diverging profile is interval integrable on [0, 1/2]. -/
example : MeasureTheory.IntervalIntegrable unitIntervalDivergingEntropyProfile
    MeasureTheory.volume 0 ((1 : ℝ) / 2) :=
  unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half

/-- The diverging profile is integrable on the j = 0 dyadic annulus [1/4, 1/2]. -/
example : MeasureTheory.IntervalIntegrable unitIntervalDivergingEntropyProfile
    MeasureTheory.volume ((1 : ℝ) / 4) ((1 : ℝ) / 2) := by
  have h := unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic 0
  norm_num at h
  exact h

/-- The diverging profile is integrable on the j = 1 dyadic annulus [1/8, 1/4]. -/
example : MeasureTheory.IntervalIntegrable unitIntervalDivergingEntropyProfile
    MeasureTheory.volume ((1 : ℝ) / 8) ((1 : ℝ) / 4) := by
  have h := unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic 1
  norm_num at h
  exact h

/-- The diverging profile dominates the j = 0 rounded-dyadic entropy sample. -/
example :
    Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 0 : ℝ)) ≤
      unitIntervalDivergingEntropyProfile ((1 : ℝ) / (2 : ℝ) ^ 1) :=
  unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy 0

/-- The diverging profile dominates the j = 1 rounded-dyadic entropy sample. -/
example :
    Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 1 : ℝ)) ≤
      unitIntervalDivergingEntropyProfile ((1 : ℝ) / (2 : ℝ) ^ 2) :=
  unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy 1

/-- The diverging profile dominates the j = 3 rounded-dyadic entropy sample. -/
example :
    Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 3 : ℝ)) ≤
      unitIntervalDivergingEntropyProfile ((1 : ℝ) / (2 : ℝ) ^ 4) :=
  unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy 3

/-- The diverging entropy profile has positive integral mass on [0, 1/2]. -/
example : 0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
    unitIntervalDivergingEntropyProfile ε :=
  unitInterval_divergingEntropyProfile_integral_positive

/-- The cover profile dominates the rounded-grid cover count (trivially, by
reflexivity since unitIntervalCoverProfile IS the rounded-grid count). -/
example (j : ℕ) :
    unitIntervalRoundedDyadicGridCoverCount j ≤ unitIntervalCoverProfile j :=
  unitInterval_coveringNumber_profile_dominates j

/-- For j = 0, the cover profile is 15 (3 × 5). -/
example : unitIntervalCoverProfile 0 = 15 := by
  norm_num [unitIntervalCoverProfile, unitIntervalRoundedDyadicGridCoverCount]

/-- The guarded capstone bound holds for the bounded entropy profile. -/
example :
    FormalSLT.Covering.FiniteSubGaussianChaining.finiteExpectation
        unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε) :=
  continuous_dudley_entropy_integral_iSup_unitInterval

/-- The guarded capstone bound holds for the diverging entropy profile. -/
example :
    FormalSLT.Covering.FiniteSubGaussianChaining.finiteExpectation
        unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
          unitIntervalDivergingEntropyProfile ε) :=
  continuous_dudley_entropy_integral_iSup_unitInterval_diverging

/-- Regression: the two capstone results can be combined transitively —
both upper-bound the same finite expectation. -/
example :
    FormalSLT.Covering.FiniteSubGaussianChaining.finiteExpectation
        unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε) ∧
    FormalSLT.Covering.FiniteSubGaussianChaining.finiteExpectation
        unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalDivergingEntropyProfile ε) :=
  ⟨continuous_dudley_entropy_integral_iSup_unitInterval,
   continuous_dudley_entropy_integral_iSup_unitInterval_diverging⟩

/-- Boundary case: unitIntervalEntropyProfile is strictly greater at 0 than at
any positive radius (since exp is strictly decreasing). Verifying monotone
decrease is nontrivial and confirms the profile is load-bearing. -/
example : unitIntervalEntropyProfile 1 < unitIntervalEntropyProfile 0 := by
  simp [unitIntervalEntropyProfile]
  exact Real.exp_lt_one_iff.mpr (by norm_num : -(1 : ℝ) < 0)