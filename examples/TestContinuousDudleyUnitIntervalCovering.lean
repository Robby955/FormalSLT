import FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering

/-!
# Comprehensive tests for ContinuousDudleyUnitIntervalCovering

This file tests the genuine covering-number continuous Dudley capstone module
with concrete example blocks beyond the basic type-checking in
`CheckContinuousDudleyUnitIntervalCovering.lean`.

Tests cover:
- `unitIntervalCoveringNumber` at specific dyadic radii (j = 0, 1, 2)
- Staircase constancy on half-open dyadic annuli
- ENat conversion properties at specific values
- Entropy integrand evaluation at dyadic radii
- Nonconstancy and positive integral mass
- Guarded annulus property at specific j values
- The continuous capstone bound
- Boundary cases: radii at exact dyadic endpoints
- Regression: the `j = 0` sample equals 15 (the genuine 3×5 cover count)
-/

open FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering
open FormalSLT.Covering.UnitIntervalDudley
open FormalSLT.Covering.ContinuousDudleyUnitInterval

/-- The covering number at the j = 0 dyadic radius 1/2 equals the genuine
rounded-grid cover count for j = 0, which is (2+1)×(4+1) = 15. -/
example : unitIntervalCoveringNumber ((1 : ℝ) / 2) =
    unitIntervalRoundedDyadicGridCoverCount 0 :=
  unitIntervalCoveringNumber_dyadic 0

/-- The covering number at the j = 1 dyadic radius 1/4 equals the genuine
rounded-grid cover count for j = 1. -/
example : unitIntervalCoveringNumber ((1 : ℝ) / 4) =
    unitIntervalRoundedDyadicGridCoverCount 1 :=
  unitIntervalCoveringNumber_dyadic 1

/-- The covering number at the j = 2 dyadic radius 1/8 equals the genuine
rounded-grid cover count for j = 2. -/
example : unitIntervalCoveringNumber ((1 : ℝ) / 8) =
    unitIntervalRoundedDyadicGridCoverCount 2 :=
  unitIntervalCoveringNumber_dyadic 2

/-- The covering number at 1/2 is concretely 15. -/
example : unitIntervalCoveringNumber ((1 : ℝ) / 2) = 15 := by
  rw [unitIntervalCoveringNumber_dyadic 0]
  norm_num [unitIntervalRoundedDyadicGridCoverCount]

/-- The covering number ENat at 1/2 is not top. -/
example : unitIntervalCoveringNumberENat ((1 : ℝ) / 2) ≠ ⊤ :=
  unitIntervalCoveringNumberENat_ne_top ((1 : ℝ) / 2)

/-- The covering number ENat at 0 is not top. -/
example : unitIntervalCoveringNumberENat 0 ≠ ⊤ :=
  unitIntervalCoveringNumberENat_ne_top 0

/-- The covering number ENat at a negative radius is not top. -/
example : unitIntervalCoveringNumberENat (-1) ≠ ⊤ :=
  unitIntervalCoveringNumberENat_ne_top (-1)

/-- The ENat toReal conversion at 1/2 matches the ℕ cast. -/
example : ENNReal.toReal (ENat.toENNReal (unitIntervalCoveringNumberENat ((1 : ℝ) / 2))) =
    (unitIntervalCoveringNumber ((1 : ℝ) / 2) : ℝ) :=
  unitIntervalCoveringNumberENat_toReal ((1 : ℝ) / 2)

/-- The ENat toReal conversion at 1/8 matches the ℕ cast. -/
example : ENNReal.toReal (ENat.toENNReal (unitIntervalCoveringNumberENat ((1 : ℝ) / 8))) =
    (unitIntervalCoveringNumber ((1 : ℝ) / 8) : ℝ) :=
  unitIntervalCoveringNumberENat_toReal ((1 : ℝ) / 8)

/-- The entropy integrand is nonneg at 1/2. -/
example : 0 ≤ unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 2) :=
  unitIntervalCoveringEntropyAtRadius_nonneg ((1 : ℝ) / 2)

/-- The entropy integrand is nonneg at 0. -/
example : 0 ≤ unitIntervalCoveringEntropyAtRadius 0 :=
  unitIntervalCoveringEntropyAtRadius_nonneg 0

/-- The entropy integrand is nonneg at negative radii. -/
example : 0 ≤ unitIntervalCoveringEntropyAtRadius (-5) :=
  unitIntervalCoveringEntropyAtRadius_nonneg (-5)

/-- The entropy at the j = 0 dyadic radius equals sqrt(log(15)). -/
example :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 2) =
      Real.sqrt (Real.log 15) := by
  rw [unitIntervalCoveringEntropy_eq_genuine_count_sample 0]
  norm_num [unitIntervalRoundedDyadicGridCoverCount]

/-- The entropy at the j = 2 dyadic radius equals sqrt(log(153)). -/
example :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 8) =
      Real.sqrt (Real.log 153) := by
  rw [unitIntervalCoveringEntropy_eq_genuine_count_sample 2]
  norm_num [unitIntervalRoundedDyadicGridCoverCount]

/-- The staircase is constant on the j = 0 half-open annulus (1/4, 1/2].
For any ε in (1/4, 1/2], the covering number equals the j=0 count. -/
example (ε : ℝ) (hleft : (1 : ℝ) / 4 < ε) (hright : ε ≤ (1 : ℝ) / 2) :
    unitIntervalCoveringNumber ε = unitIntervalRoundedDyadicGridCoverCount 0 := by
  apply unitIntervalCoveringNumber_const_on_halfOpenAnnulus 0
  · simpa using hleft
  · simpa using hright

/-- The staircase is constant on the j = 1 half-open annulus (1/8, 1/4].
For ε = 0.2 ∈ (1/8, 1/4], the covering number equals the j=1 count. -/
example : unitIntervalCoveringNumber (0.2 : ℝ) = unitIntervalRoundedDyadicGridCoverCount 1 := by
  apply unitIntervalCoveringNumber_const_on_halfOpenAnnulus 1
  · norm_num
  · norm_num

/-- The entropy integrand is nonconstant: entropy at 1/2 ≠ entropy at 1/8. -/
example :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 2) ≠
      unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 8) :=
  unitInterval_coveringEntropy_nonconstant

/-- The entropy integrand has positive integral mass on [0, 1/2]. -/
example : 0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
    unitIntervalCoveringEntropyAtRadius ε :=
  unitInterval_coveringEntropy_integral_positive

/-- The entropy integrand is interval integrable on [0, 1/2]. -/
example : MeasureTheory.IntervalIntegrable unitIntervalCoveringEntropyAtRadius
    MeasureTheory.volume 0 ((1 : ℝ) / 2) :=
  unitIntervalCoveringEntropyAtRadius_intervalIntegrable_zero_half

/-- The guarded annulus property holds at j = 0 for the covering entropy. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalCoveringEntropyAtRadius 1 0 :=
  unitIntervalCoveringEntropyAtRadius_guarded 0

/-- The guarded annulus property holds at j = 1 for the covering entropy. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalCoveringEntropyAtRadius 1 1 :=
  unitIntervalCoveringEntropyAtRadius_guarded 1

/-- The guarded annulus property holds at j = 4 for the covering entropy. -/
example : FormalSLT.Covering.GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
    unitIntervalCoveringEntropyAtRadius 1 4 :=
  unitIntervalCoveringEntropyAtRadius_guarded 4

/-- The continuous capstone bound with genuine covering-number integrand holds. -/
example :
    FormalSLT.Covering.FiniteSubGaussianChaining.finiteExpectation
        unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
          unitIntervalCoveringEntropyAtRadius ε) :=
  continuous_dudley_entropy_integral_iSup_unitInterval_coveringNumber

/-- The entropy sample at j = 1 (radius 1/4) equals sqrt(log(count 1)). -/
example :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 4) =
      Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 1 : ℝ)) :=
  unitIntervalCoveringEntropy_eq_genuine_count_sample 1

/-- The entropy sample at j = 3 (radius 1/16) equals sqrt(log(count 3)). -/
example :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 16) =
      Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 3 : ℝ)) :=
  unitIntervalCoveringEntropy_eq_genuine_count_sample 3

/-- Regression: the genuine sample and the ENat surface agree at j = 0. -/
example :
    ENNReal.toReal (ENat.toENNReal (unitIntervalCoveringNumberENat ((1 : ℝ) / 2))) = 15 := by
  rw [unitIntervalCoveringNumberENat_toReal]
  rw [unitIntervalCoveringNumber_dyadic 0]
  norm_num [unitIntervalRoundedDyadicGridCoverCount]

/-- The staircase covering number is positive for any input (even off-interval). -/
example : 0 < unitIntervalCoveringNumber 0 := by
  unfold unitIntervalCoveringNumber unitIntervalRoundedDyadicGridCoverCount
  positivity

/-- The staircase covering number is positive at a negative radius. -/
example : 0 < unitIntervalCoveringNumber (-1) := by
  unfold unitIntervalCoveringNumber unitIntervalRoundedDyadicGridCoverCount
  positivity

/-- Boundary case: the covering entropy at 1/4 (the left endpoint of the
j = 0 half-open annulus) equals the sample from j = 1 (since the annulus
is half-open on the left, 1/4 is the right endpoint of the j=1 annulus). -/
example :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 4) =
      Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 1 : ℝ)) :=
  unitIntervalCoveringEntropy_eq_genuine_count_sample 1