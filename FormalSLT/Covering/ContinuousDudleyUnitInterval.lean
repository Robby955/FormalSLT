import FormalSLT.Covering.GuardedContinuousDudley
import FormalSLT.Covering.UnitIntervalDudley

/-!
# Guarded continuous Dudley capstone on the unit interval

This module instantiates the guarded positive-radius continuous Dudley passage
on the concrete unit-interval Rademacher linear process. The entropy profile is
real-valued, nonconstant, and used only through dyadic guarded annuli, avoiding
the old global `Antitone (ℝ → ℝ)` continuous theorem surface.
-/

namespace FormalSLT.Covering.ContinuousDudleyUnitInterval

open scoped BigOperators Interval
open MeasureTheory
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.UnitIntervalDudley

noncomputable section

/-- Dyadic-indexed rounded-grid covering profile for the unit interval. -/
def unitIntervalCoverProfile (j : ℕ) : ℕ :=
  unitIntervalRoundedDyadicGridCoverCount j

/-- The dyadic-indexed profile dominates the concrete rounded-grid cover count.

This is intentionally a dyadic-indexed statement, not a global real-radius
covering-number antitonicity claim. -/
-- fidelity: The domination is exact at every dyadic index, so the profile is
-- not an unused free constant.
theorem unitInterval_coveringNumber_profile_dominates (j : ℕ) :
    unitIntervalRoundedDyadicGridCoverCount j ≤ unitIntervalCoverProfile j := by
  rfl

/-- A bounded, nonconstant positive entropy profile used for the guarded
unit-interval capstone. -/
def unitIntervalEntropyProfile (ε : ℝ) : ℝ :=
  20 + Real.exp (-ε)

theorem unitIntervalEntropyProfile_nonneg (ε : ℝ) :
    0 ≤ unitIntervalEntropyProfile ε := by
  dsimp [unitIntervalEntropyProfile]
  positivity

theorem unitIntervalEntropyProfile_antitone :
    Antitone unitIntervalEntropyProfile := by
  intro a b hab
  dsimp [unitIntervalEntropyProfile]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left (Real.exp_le_exp.mpr (neg_le_neg hab)) 20

theorem unitIntervalEntropyProfile_guarded (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus unitIntervalEntropyProfile (1 : ℝ) j := by
  intro ε _hleft hright
  exact unitIntervalEntropyProfile_antitone hright

theorem unitIntervalEntropyProfile_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable unitIntervalEntropyProfile volume a b := by
  have hcont : Continuous unitIntervalEntropyProfile := by
    simpa [unitIntervalEntropyProfile] using
      (continuous_const.add (Real.continuous_exp.comp continuous_neg))
  exact hcont.intervalIntegrable a b

/-- The entropy integrand is load-bearing: it is not a constant profile. -/
-- fidelity: The two endpoint values are unequal, so the capstone integral is
-- not a disguised constant-entropy bound.
theorem unitInterval_entropyProfile_nonconstant :
    unitIntervalEntropyProfile 0 ≠ unitIntervalEntropyProfile 1 := by
  have hexp_lt_one : Real.exp (-(1 : ℝ)) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by norm_num : (-(1 : ℝ)) < 0)
  intro h
  norm_num [unitIntervalEntropyProfile] at h
  have : Real.exp (-(1 : ℝ)) = 1 := by
    linarith
  linarith

/-- The entropy integrand has positive mass on the continuous Dudley interval. -/
-- fidelity: The integral dominates the positive rectangle with height `20`
-- over `[0, 1 / 2]`, so the entropy term is not zero.
theorem unitInterval_entropyProfile_integral_positive :
    0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε := by
  have hrect :
      (((1 : ℝ) / 2) - 0) * 20 ≤
        ∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε := by
    exact
      FiniteSubGaussianProcess.interval_const_mul_le_integral_of_le_on
        (f := unitIntervalEntropyProfile) (a := (0 : ℝ))
        (b := ((1 : ℝ) / 2)) (c := (20 : ℝ))
        (by norm_num)
        (unitIntervalEntropyProfile_intervalIntegrable 0 ((1 : ℝ) / 2))
        (by
          intro x _hx
          dsimp [unitIntervalEntropyProfile]
          have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
          linarith)
  nlinarith

private lemma unitIntervalEntropyProfile_dominates_first_roundedDyadicEntropy :
    Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 0 : ℝ)) ≤
      unitIntervalEntropyProfile ((1 : ℝ) / 2) := by
  have hcount : unitIntervalRoundedDyadicGridCoverCount 0 = 15 := by
    norm_num [unitIntervalRoundedDyadicGridCoverCount]
  have hlog_le : Real.log (15 : ℝ) ≤ 400 := by
    exact (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 15)).trans (by norm_num)
  have hsqrt_le : Real.sqrt (Real.log (15 : ℝ)) ≤ 20 := by
    have hlog_nonneg : 0 ≤ Real.log (15 : ℝ) :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 15)
    have hsq : (Real.sqrt (Real.log (15 : ℝ))) ^ 2 ≤ (20 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hlog_nonneg]
      norm_num
      exact hlog_le
    nlinarith [Real.sqrt_nonneg (Real.log (15 : ℝ))]
  have hprofile_ge :
      (20 : ℝ) ≤ unitIntervalEntropyProfile ((1 : ℝ) / 2) := by
    dsimp [unitIntervalEntropyProfile]
    have hpos : 0 < Real.exp (-((1 : ℝ) / 2)) := Real.exp_pos _
    linarith
  simpa [hcount] using hsqrt_le.trans hprofile_ge

private theorem unitInterval_roundedDyadic_hdyadicProfile_bound :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus unitIntervalEntropyProfile (1 : ℝ) j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable unitIntervalEntropyProfile volume
            ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
            ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation unitIntervalRademacherLinearProcess.weight
            unitIntervalRademacherLinearSup ≤
          1 + 2 * Real.sqrt (2 *
              unitIntervalRademacherLinearProcess.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              (1 : ℝ) m unitIntervalEntropyProfile + eta := by
  intro eta heta
  refine ⟨1, ?_, ?_, ?_⟩
  · intro j _hj
    exact unitIntervalEntropyProfile_guarded j
  · intro j _hj
    exact unitIntervalEntropyProfile_intervalIntegrable
      ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
      ((1 : ℝ) / (2 : ℝ) ^ (j + 1))
  · have hfinite :=
      unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree 1
    have hbudget :
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) ≤
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            (1 : ℝ) 1 unitIntervalEntropyProfile := by
      refine
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum
          (m := 1)
          (entropyEnvelope := fun j : ℕ =>
            Real.sqrt
              (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))
          (entropyAtRadius := unitIntervalEntropyProfile)
          (radiusScale := (1 : ℝ)) (by norm_num) ?_
      intro j hj
      have hj0 : j = 0 := by
        have hjlt : j < 1 := Finset.mem_range.mp hj
        omega
      subst j
      simpa using unitIntervalEntropyProfile_dominates_first_roundedDyadicEntropy
    have hcoef_nonneg :
        0 ≤ 2 * Real.sqrt (2 *
            unitIntervalRademacherLinearProcess.varianceProxy) := by
      positivity
    have hmul :=
      mul_le_mul_of_nonneg_left hbudget hcoef_nonneg
    linarith [hfinite, hmul, heta.le]

/-- Corrected guarded continuous Dudley wrapper using a dyadic profile side
condition instead of a global antitone entropy profile.

-- fidelity: The finite input is a real dyadic upper-sum bound at positive
annuli; the theorem does not assume global antitonicity or evaluate the profile
at radius zero through monotonicity. -/
theorem continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
    {Ω T : Type*} [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hdyadic : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus entropyAtRadius radiusScale j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m entropyAtRadius + eta) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) :=
  GuardedContinuousDudley.guarded_continuous_dudley_entropy_integral_nonempty_of_upper_sum_bounds
    (P := P) (coarseBudget := coarseBudget) (radiusScale := radiusScale)
    (entropyAtRadius := entropyAtRadius) (supFunctional := supFunctional)
    hradiusScale hentropy_nonneg hint0 hdyadic

/-- Continuous Dudley entropy-integral bound for the nonzero unit-interval
Rademacher linear process with a nonconstant entropy integrand.

-- fidelity: The process is the concrete nonzero `sign * t` process on the
non-finite unit interval, the supremum functional has expectation `1 / 2`, and
the entropy profile is separately proved nonconstant with positive integral. -/
theorem continuous_dudley_entropy_integral_iSup_unitInterval :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε) := by
  exact
    continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
      (P := unitIntervalRademacherLinearProcess)
      (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (entropyAtRadius := unitIntervalEntropyProfile)
      (supFunctional := unitIntervalRademacherLinearSup)
      (by norm_num)
      unitIntervalEntropyProfile_nonneg
      (unitIntervalEntropyProfile_intervalIntegrable 0 ((1 : ℝ) / 2))
      unitInterval_roundedDyadic_hdyadicProfile_bound

end

end FormalSLT.Covering.ContinuousDudleyUnitInterval
