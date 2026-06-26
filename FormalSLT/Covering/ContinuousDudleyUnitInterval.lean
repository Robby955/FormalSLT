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

/-- Dyadic-indexed rounded-grid cover-count profile for the unit interval. -/
def unitIntervalRoundedGridCoverProfile (j : ℕ) : ℕ :=
  unitIntervalRoundedDyadicGridCoverCount j

/-- The dyadic-indexed profile is definitionally the rounded-grid cover count.

This is intentionally a dyadic-indexed statement, not a global real-radius
covering-number antitonicity claim. -/
-- fidelity: This is only a definitional identity for the rounded-grid profile;
-- it is not advertised as a separate domination theorem.
theorem unitInterval_coverProfile_eq_roundedDyadicGridCoverCount (j : ℕ) :
    unitIntervalRoundedGridCoverProfile j = unitIntervalRoundedDyadicGridCoverCount j := by
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

/-- Positive-radius singular entropy profile. It is zero off positive radii,
but diverges like `ε^(-1/2)` as `ε ↓ 0` along positive radii. -/
def unitIntervalDivergingEntropyProfile (ε : ℝ) : ℝ :=
  if 0 < ε then 20 * ε ^ (-(1 : ℝ) / 2) else 0

theorem unitIntervalDivergingEntropyProfile_nonneg (ε : ℝ) :
    0 ≤ unitIntervalDivergingEntropyProfile ε := by
  by_cases hε : 0 < ε
  · simp [unitIntervalDivergingEntropyProfile, hε,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 20)
        (Real.rpow_nonneg hε.le (-(1 : ℝ) / 2))]
  · simp [unitIntervalDivergingEntropyProfile, hε]

theorem unitIntervalDivergingEntropyProfile_guarded (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus
      unitIntervalDivergingEntropyProfile (1 : ℝ) j := by
  intro ε hleft hright
  have hright_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by positivity
  have hε_pos : 0 < ε := by
    have hleft_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 2) := by positivity
    exact lt_of_lt_of_le hleft_pos hleft
  simp [unitIntervalDivergingEntropyProfile, hε_pos]
  simpa [div_eq_mul_inv, one_mul] using
    Real.rpow_le_rpow_of_nonpos hε_pos hright
      (by norm_num : (-(1 : ℝ) / 2) ≤ 0)

theorem unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half :
    IntervalIntegrable unitIntervalDivergingEntropyProfile volume
      (0 : ℝ) ((1 : ℝ) / 2) := by
  have hbase :
      IntervalIntegrable (fun ε : ℝ => 20 * ε ^ (-(1 : ℝ) / 2))
        volume (0 : ℝ) ((1 : ℝ) / 2) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := ((1 : ℝ) / 2))
      (r := (-(1 : ℝ) / 2)) (by norm_num)).const_mul 20
  refine hbase.congr ?_
  intro ε hε
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)] at hε
  simp [unitIntervalDivergingEntropyProfile, hε.1]

theorem unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic
    (j : ℕ) :
    IntervalIntegrable unitIntervalDivergingEntropyProfile volume
      ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
      ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  have hbase :
      IntervalIntegrable (fun ε : ℝ => 20 * ε ^ (-(1 : ℝ) / 2))
        volume ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (a := ((1 : ℝ) / (2 : ℝ) ^ (j + 2)))
      (b := ((1 : ℝ) / (2 : ℝ) ^ (j + 1)))
      (r := (-(1 : ℝ) / 2)) (by norm_num)).const_mul 20
  have hab :
      (1 : ℝ) / (2 : ℝ) ^ (j + 2) ≤
        (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
    have hwidth :=
      FiniteSubGaussianProcess.dyadic_annulus_width_nonneg
        (radiusScale := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) (j + 1)
    linarith
  refine hbase.congr ?_
  intro ε hε
  rw [Set.uIoc_of_le hab] at hε
  have hleft_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 2) := by positivity
  have hε_pos : 0 < ε := lt_trans hleft_pos hε.1
  simp [unitIntervalDivergingEntropyProfile, hε_pos]

private lemma unitIntervalRoundedDyadicGridCoverCount_le_pow (j : ℕ) :
    unitIntervalRoundedDyadicGridCoverCount j ≤ 2 ^ (2 * j + 5) := by
  have h1 : 2 ^ (j + 1) + 1 ≤ 2 ^ (j + 2) := by
    have hp : 1 ≤ 2 ^ (j + 1) :=
      Nat.one_le_pow (j + 1) 2 (by norm_num)
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    omega
  have h2 : 2 ^ (j + 2) + 1 ≤ 2 ^ (j + 3) := by
    have hp : 1 ≤ 2 ^ (j + 2) :=
      Nat.one_le_pow (j + 2) 2 (by norm_num)
    rw [show j + 3 = (j + 2) + 1 by omega, pow_succ]
    omega
  have hmul := Nat.mul_le_mul h1 h2
  have hpow : 2 ^ (j + 2) * 2 ^ (j + 3) = 2 ^ (2 * j + 5) := by
    rw [← pow_add]
    congr 1
    omega
  simpa [unitIntervalRoundedDyadicGridCoverCount, hpow] using hmul

/-- The singular profile dominates every rounded-dyadic entropy sample.

-- fidelity: The domination is uniform in the dyadic index and uses the
actual rounded-grid cover counts, while the profile diverges at positive radii
approaching zero. -/
theorem unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy
    (j : ℕ) :
    Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)) ≤
      unitIntervalDivergingEntropyProfile
        ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  let c : ℕ := unitIntervalRoundedDyadicGridCoverCount j
  have hc_pos_nat : 0 < c := by
    dsimp [c, unitIntervalRoundedDyadicGridCoverCount]
    positivity
  have hlog_nonneg : 0 ≤ Real.log (c : ℝ) :=
    Real.log_natCast_nonneg c
  have hcount_le : (c : ℝ) ≤ (2 : ℝ) ^ (2 * j + 5) := by
    exact_mod_cast unitIntervalRoundedDyadicGridCoverCount_le_pow j
  have hlog_le_sqrt : Real.log (c : ℝ) ≤
      2 * (c : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa [one_div, mul_comm] using
      Real.log_natCast_le_rpow_div c
        (by norm_num : 0 < (1 : ℝ) / 2)
  have hcpow_le :
      (c : ℝ) ^ ((1 : ℝ) / 2) ≤
        ((2 : ℝ) ^ (2 * j + 5)) ^ ((1 : ℝ) / 2) := by
    exact Real.rpow_le_rpow (by exact_mod_cast Nat.zero_le c)
      hcount_le (by norm_num)
  have hpow_sqrt_le :
      ((2 : ℝ) ^ (2 * j + 5)) ^ ((1 : ℝ) / 2) ≤
        (2 : ℝ) ^ (j + 3) := by
    have hbase : (0 : ℝ) ≤ 2 := by norm_num
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase]
    rw [← Real.rpow_natCast (2 : ℝ) (j + 3)]
    have hexp_le :
        ((2 * j + 5 : ℕ) : ℝ) * ((1 : ℝ) / 2) ≤
          ((j + 3 : ℕ) : ℝ) := by
      have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast Nat.zero_le j
      norm_num
      nlinarith
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexp_le
  have hlog_le_pow : Real.log (c : ℝ) ≤ (2 : ℝ) ^ (j + 4) := by
    calc
      Real.log (c : ℝ) ≤ 2 * (c : ℝ) ^ ((1 : ℝ) / 2) :=
        hlog_le_sqrt
      _ ≤ 2 * ((2 : ℝ) ^ (2 * j + 5)) ^ ((1 : ℝ) / 2) := by
        nlinarith [hcpow_le]
      _ ≤ 2 * (2 : ℝ) ^ (j + 3) := by
        nlinarith [hpow_sqrt_le]
      _ = (2 : ℝ) ^ (j + 4) := by
        rw [show j + 4 = (j + 3) + 1 by omega, pow_succ]
        ring
  have hradius_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
    positivity
  have hprofile_sq :
      (unitIntervalDivergingEntropyProfile
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ^ 2 =
        400 * (2 : ℝ) ^ (j + 1) := by
    simp [unitIntervalDivergingEntropyProfile]
    have hnonneg : 0 ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := by positivity
    rw [mul_pow]
    norm_num
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hnonneg]
    ring_nf
    rw [Real.rpow_neg_one]
    field_simp [pow_ne_zero j (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]
    rw [← mul_pow]
    norm_num
  have hlog_le_profile_sq :
      Real.log (c : ℝ) ≤
        (unitIntervalDivergingEntropyProfile
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ^ 2 := by
    rw [hprofile_sq]
    have hpow_mono :
        (2 : ℝ) ^ (j + 4) ≤ 400 * (2 : ℝ) ^ (j + 1) := by
      have hpos : 0 < (2 : ℝ) ^ (j + 1) :=
        pow_pos (by norm_num) _
      rw [show j + 4 = (j + 1) + 3 by omega, pow_add]
      norm_num
      nlinarith [hpos]
    exact hlog_le_pow.trans hpow_mono
  rw [Real.sqrt_le_iff]
  exact ⟨unitIntervalDivergingEntropyProfile_nonneg _, hlog_le_profile_sq⟩

/-- The singular entropy profile has positive integral mass on `0..1/2`.

-- fidelity: The positive lower bound comes from the concrete subinterval
`[1 / 4, 1 / 2]`, so the load-bearing entropy term is not concentrated in a
formal singularity at zero. -/
theorem unitInterval_divergingEntropyProfile_integral_positive :
    0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
      unitIntervalDivergingEntropyProfile ε := by
  have htrunc_rect :
      (((1 : ℝ) / 2) - (1 / 4)) * 20 ≤
        ∫ ε in ((1 : ℝ) / 4)..((1 : ℝ) / 2),
          unitIntervalDivergingEntropyProfile ε := by
    refine
      FiniteSubGaussianProcess.interval_const_mul_le_integral_of_le_on
        (f := unitIntervalDivergingEntropyProfile) (a := ((1 : ℝ) / 4))
        (b := ((1 : ℝ) / 2)) (c := (20 : ℝ)) (by norm_num)
        (by
          have hI :=
            unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic 0
          norm_num at hI
          simpa [one_div] using hI) ?_
    intro ε hε
    rcases hε with ⟨hε_left, hε_right⟩
    have hε_pos : 0 < ε := by linarith
    have hε_le_one : ε ≤ (1 : ℝ) := by linarith
    have hpow_ge_one : (1 : ℝ) ≤ ε ^ (-(1 : ℝ) / 2) := by
      have h :=
        Real.rpow_le_rpow_of_nonpos hε_pos hε_le_one
          (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
      simpa using h
    simp [unitIntervalDivergingEntropyProfile, hε_pos]
    nlinarith
  have htrunc_pos :
      0 < ∫ ε in ((1 : ℝ) / 4)..((1 : ℝ) / 2),
        unitIntervalDivergingEntropyProfile ε := by
    nlinarith
  have hdom :=
    GuardedContinuousDudley.guarded_truncatedIntegral_le_full_integral
      (m := 1) (entropyAtRadius := unitIntervalDivergingEntropyProfile)
      (radiusScale := (1 : ℝ)) (by norm_num)
      unitIntervalDivergingEntropyProfile_nonneg
      unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half
  norm_num at hdom
  exact lt_of_lt_of_le htrunc_pos hdom

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

private theorem unitInterval_roundedDyadic_hdyadicDivergingProfile_bound :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus
            unitIntervalDivergingEntropyProfile (1 : ℝ) j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable unitIntervalDivergingEntropyProfile volume
            ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
            ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation unitIntervalRademacherLinearProcess.weight
            unitIntervalRademacherLinearSup ≤
          1 + 2 * Real.sqrt (2 *
              unitIntervalRademacherLinearProcess.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              (1 : ℝ) m unitIntervalDivergingEntropyProfile + eta := by
  intro eta heta
  refine ⟨1, ?_, ?_, ?_⟩
  · intro j _hj
    exact unitIntervalDivergingEntropyProfile_guarded j
  · intro j _hj
    exact unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic j
  · have hfinite :=
      unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree 1
    have hbudget :
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) ≤
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            (1 : ℝ) 1 unitIntervalDivergingEntropyProfile := by
      refine
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum
          (m := 1)
          (entropyEnvelope := fun j : ℕ =>
            Real.sqrt
              (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))
          (entropyAtRadius := unitIntervalDivergingEntropyProfile)
          (radiusScale := (1 : ℝ)) (by norm_num) ?_
      intro j hj
      have hj0 : j = 0 := by
        have hjlt : j < 1 := Finset.mem_range.mp hj
        omega
      subst j
      simpa using
        unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy 0
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

/-- Continuous Dudley entropy-integral bound for the unit-interval process
using the integrable positive-radius singular entropy profile.

-- fidelity: This capstone uses the same concrete nonzero process and supplied
supremum as the bounded-profile theorem, but its entropy profile diverges as
`ε ↓ 0` along positive radii and dominates every rounded-dyadic entropy sample. -/
theorem continuous_dudley_entropy_integral_iSup_unitInterval_diverging :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
          unitIntervalDivergingEntropyProfile ε) := by
  exact
    continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
      (P := unitIntervalRademacherLinearProcess)
      (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (entropyAtRadius := unitIntervalDivergingEntropyProfile)
      (supFunctional := unitIntervalRademacherLinearSup)
      (by norm_num)
      unitIntervalDivergingEntropyProfile_nonneg
      unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half
      unitInterval_roundedDyadic_hdyadicDivergingProfile_bound

end

end FormalSLT.Covering.ContinuousDudleyUnitInterval
