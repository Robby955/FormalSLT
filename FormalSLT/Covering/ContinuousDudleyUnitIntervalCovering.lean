import FormalSLT.Covering.ContinuousDudleyUnitInterval
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Genuine covering-number continuous Dudley capstone on `[0,1]`

This module instantiates the guarded continuous Dudley wrapper for the concrete
unit-interval Rademacher process using the real-radius staircase whose dyadic
samples are the rounded-grid covering-number products.
-/

namespace FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering

open scoped BigOperators Interval
open MeasureTheory
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.UnitIntervalDudley
open FormalSLT.Covering.ContinuousDudleyUnitInterval

noncomputable section

/-- Dyadic level selected by the half-open, right-closed annulus
`(1 / 2^(j+2), 1 / 2^(j+1)]`.

For positive radii this is `⌊log_2 (1 / ε)⌋ - 1`. Values outside the positive
Dudley interval are harmless default values for the surrounding concrete
capstone. -/
def unitIntervalCoveringIndex (ε : ℝ) : ℕ :=
  Nat.floor (Real.logb 2 ε⁻¹) - 1

/-- Real-radius covering staircase for the unit interval. At dyadic radius
`1 / 2^(j+1)` it is the genuine adjacent rounded-grid finite-cover product. -/
def unitIntervalCoveringNumber (ε : ℝ) : ℕ :=
  unitIntervalRoundedDyadicGridCoverCount (unitIntervalCoveringIndex ε)

/-- The same covering-number staircase as an `ℕ∞`-valued surface. -/
def unitIntervalCoveringNumberENat (ε : ℝ) : ℕ∞ :=
  (unitIntervalCoveringNumber ε : ℕ∞)

/-- Entropy integrand built from the genuine covering-number staircase. -/
def unitIntervalCoveringEntropyAtRadius (ε : ℝ) : ℝ :=
  Real.sqrt (Real.log (unitIntervalCoveringNumber ε : ℝ))

private lemma inv_dyadic_radius (j : ℕ) :
    (((1 : ℝ) / (2 : ℝ) ^ (j + 1))⁻¹) = (2 : ℝ) ^ (j + 1) := by
  field_simp [pow_ne_zero (j + 1) (by norm_num : (2 : ℝ) ≠ 0)]

private lemma logb_inv_dyadic_radius (j : ℕ) :
    Real.logb 2 (((1 : ℝ) / (2 : ℝ) ^ (j + 1))⁻¹) = (j + 1 : ℝ) := by
  rw [inv_dyadic_radius j, ← Real.rpow_natCast]
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hne : (2 : ℝ) ≠ 1 := by norm_num
  rw [Real.logb_rpow (b := (2 : ℝ))
    (x := ((j + 1 : ℕ) : ℝ)) hpos hne]
  simp [Nat.cast_add, Nat.cast_one]

private lemma unitIntervalCoveringIndex_dyadic (j : ℕ) :
    unitIntervalCoveringIndex ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) = j := by
  unfold unitIntervalCoveringIndex
  rw [logb_inv_dyadic_radius j]
  rw [show (j + 1 : ℝ) = ((j + 1 : ℕ) : ℝ) by simp]
  rw [Nat.floor_natCast]
  omega

/-- The real-radius staircase samples the genuine rounded-grid finite-cover
product at every dyadic Dudley radius. -/
theorem unitIntervalCoveringNumber_dyadic (j : ℕ) :
    unitIntervalCoveringNumber ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) =
      unitIntervalRoundedDyadicGridCoverCount j := by
  rw [unitIntervalCoveringNumber, unitIntervalCoveringIndex_dyadic]

private theorem unitIntervalCoveringNumber_dyadic_inv (j : ℕ) :
    unitIntervalCoveringNumber (((2 : ℝ) ^ (j + 1))⁻¹) =
      unitIntervalRoundedDyadicGridCoverCount j := by
  simpa [one_div] using unitIntervalCoveringNumber_dyadic j

private lemma dyadic_radius_pos (j : ℕ) :
    0 < (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
  positivity

private lemma dyadic_radius_le_of_le {i j : ℕ} (hij : i ≤ j) :
    (1 : ℝ) / (2 : ℝ) ^ (j + 1) ≤
      (1 : ℝ) / (2 : ℝ) ^ (i + 1) := by
  exact one_div_pow_le_one_div_pow_of_le
    (by norm_num : (1 : ℝ) ≤ 2) (Nat.add_le_add_right hij 1)

private lemma dyadic_radius_lt_of_lt {i j : ℕ} (hij : i < j) :
    (1 : ℝ) / (2 : ℝ) ^ (j + 1) <
      (1 : ℝ) / (2 : ℝ) ^ (i + 1) := by
  exact one_div_pow_lt_one_div_pow_of_lt
    (by norm_num : (1 : ℝ) < 2) (Nat.add_lt_add_right hij 1)

private lemma unitIntervalCoveringIndex_of_mem_halfOpenAnnulus
    {ε : ℝ} (j : ℕ)
    (hleft : (1 : ℝ) / (2 : ℝ) ^ (j + 2) < ε)
    (hright : ε ≤ (1 : ℝ) / (2 : ℝ) ^ (j + 1)) :
    unitIntervalCoveringIndex ε = j := by
  have hε_pos : 0 < ε := by
    exact lt_trans (by positivity : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (j + 2)) hleft
  have hinv_lower :
      (2 : ℝ) ^ (j + 1) ≤ ε⁻¹ := by
    have h := one_div_le_one_div_of_le hε_pos hright
    simpa [one_div, inv_dyadic_radius j] using h
  have hinv_upper :
      ε⁻¹ < (2 : ℝ) ^ (j + 2) := by
    have h := one_div_lt_one_div_of_lt
      (by positivity : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (j + 2)) hleft
    simpa [one_div, inv_dyadic_radius (j + 1), show j + 1 + 1 = j + 2 by omega] using h
  have hlog_lower :
      (j + 1 : ℝ) ≤ Real.logb 2 ε⁻¹ := by
    have hpos_left : 0 < (2 : ℝ) ^ (j + 1) := by positivity
    have hpos_right : 0 < ε⁻¹ := inv_pos.mpr hε_pos
    have h := (Real.logb_le_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2) hpos_left hpos_right).mpr hinv_lower
    simpa [← Real.rpow_natCast, Real.logb_rpow
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  have hlog_upper :
      Real.logb 2 ε⁻¹ < (j + 2 : ℝ) := by
    have hpos_inv : 0 < ε⁻¹ := inv_pos.mpr hε_pos
    have h := Real.logb_lt_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2) hpos_inv hinv_upper
    simpa [← Real.rpow_natCast, Real.logb_rpow
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  unfold unitIntervalCoveringIndex
  have hfloor : Nat.floor (Real.logb 2 ε⁻¹) = j + 1 := by
    rw [Nat.floor_eq_iff]
    · exact ⟨by simpa [Nat.cast_add, Nat.cast_one] using hlog_lower,
        by
          norm_num [Nat.cast_add, Nat.cast_one] at hlog_upper ⊢
          linarith⟩
    · exact le_trans (by exact_mod_cast Nat.zero_le (j + 1)) hlog_lower
  rw [hfloor]
  omega

/-- The staircase is constant on each half-open, right-closed dyadic annulus. -/
theorem unitIntervalCoveringNumber_const_on_halfOpenAnnulus
    {ε : ℝ} (j : ℕ)
    (hleft : (1 : ℝ) / (2 : ℝ) ^ (j + 2) < ε)
    (hright : ε ≤ (1 : ℝ) / (2 : ℝ) ^ (j + 1)) :
    unitIntervalCoveringNumber ε = unitIntervalRoundedDyadicGridCoverCount j := by
  simp [unitIntervalCoveringNumber,
    unitIntervalCoveringIndex_of_mem_halfOpenAnnulus j hleft hright]

theorem unitIntervalCoveringNumberENat_ne_top (ε : ℝ) :
    unitIntervalCoveringNumberENat ε ≠ ⊤ := by
  simp [unitIntervalCoveringNumberENat]

theorem unitIntervalCoveringNumberENat_toReal (ε : ℝ) :
    ENNReal.toReal (ENat.toENNReal (unitIntervalCoveringNumberENat ε)) =
      (unitIntervalCoveringNumber ε : ℝ) := by
  simp [unitIntervalCoveringNumberENat, ENNReal.toReal_natCast]

private lemma unitIntervalCoveringNumber_pos (ε : ℝ) :
    0 < unitIntervalCoveringNumber ε := by
  unfold unitIntervalCoveringNumber unitIntervalRoundedDyadicGridCoverCount
  positivity

theorem unitIntervalCoveringEntropyAtRadius_nonneg (ε : ℝ) :
    0 ≤ unitIntervalCoveringEntropyAtRadius ε := by
  simp [unitIntervalCoveringEntropyAtRadius]

private lemma unitIntervalCoveringEntropyAtRadius_measurable :
    Measurable unitIntervalCoveringEntropyAtRadius := by
  have hlogb : Measurable fun ε : ℝ => Real.logb 2 ε⁻¹ := by
    simpa [Real.logb] using ((measurable_id.inv).log.div_const (Real.log 2))
  have hidx : Measurable unitIntervalCoveringIndex := by
    unfold unitIntervalCoveringIndex
    measurability
  have hnum : Measurable fun ε : ℝ => (unitIntervalCoveringNumber ε : ℝ) := by
    unfold unitIntervalCoveringNumber
    measurability
  exact hnum.log.sqrt

private lemma unitIntervalCoveringEntropyAtRadius_dominated
    {ε : ℝ} (hε_mem : ε ∈ Set.Ioc (0 : ℝ) ((1 : ℝ) / 2)) :
    unitIntervalCoveringEntropyAtRadius ε ≤
      unitIntervalDivergingEntropyProfile ε := by
  have hε_pos : 0 < ε := hε_mem.1
  have hε_le : ε ≤ (1 : ℝ) / 2 := hε_mem.2
  let j := unitIntervalCoveringIndex ε
  have hlog_ge_one : (1 : ℝ) ≤ Real.logb 2 ε⁻¹ := by
    have hinv_ge : (2 : ℝ) ≤ ε⁻¹ := by
      have h := one_div_le_one_div_of_le hε_pos hε_le
      norm_num at h
      simpa [one_div] using h
    have h := (Real.logb_le_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      (inv_pos.mpr hε_pos)).mpr hinv_ge
    simpa using h
  have hfloor_ge : 1 ≤ Nat.floor (Real.logb 2 ε⁻¹) :=
    Nat.le_floor (by simpa using hlog_ge_one)
  have hfloor_eq : Nat.floor (Real.logb 2 ε⁻¹) = j + 1 := by
    unfold j unitIntervalCoveringIndex
    omega
  have hfloor_bounds :=
    (Nat.floor_eq_iff (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog_ge_one)).mp
      hfloor_eq
  have hright : ε ≤ (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
    have hlog_pow :
        Real.logb 2 ((2 : ℝ) ^ (j + 1)) = ((j + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)
    have hlog_le : Real.logb 2 ((2 : ℝ) ^ (j + 1)) ≤ Real.logb 2 ε⁻¹ := by
      simpa [hlog_pow] using hfloor_bounds.1
    have hinv_lower : (2 : ℝ) ^ (j + 1) ≤ ε⁻¹ := by
      exact (Real.logb_le_logb (b := 2)
        (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))
        (inv_pos.mpr hε_pos)).mp hlog_le
    have h := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1)) hinv_lower
    simpa [one_div, inv_inv, inv_dyadic_radius j] using h
  have hleft : (1 : ℝ) / (2 : ℝ) ^ (j + 2) < ε := by
    have hlog_pow :
        Real.logb 2 ((2 : ℝ) ^ (j + 2)) = ((j + 2 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)
    have hlog_le : Real.logb 2 ε⁻¹ ≤ Real.logb 2 ((2 : ℝ) ^ (j + 2)) := by
      rw [hlog_pow]
      norm_num [Nat.cast_add, Nat.cast_one] at hfloor_bounds ⊢
      linarith
    have hinv_le : ε⁻¹ ≤ (2 : ℝ) ^ (j + 2) := by
      exact (Real.logb_le_logb (b := 2)
        (by norm_num : (1 : ℝ) < 2)
        (inv_pos.mpr hε_pos)
        (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 2))).mp hlog_le
    have hinv_ne : ε⁻¹ ≠ (2 : ℝ) ^ (j + 2) := by
      intro heq
      have hcontr : Real.logb 2 ε⁻¹ = ((j + 2 : ℕ) : ℝ) := by
        simpa [heq] using hlog_pow
      have : ((j + 2 : ℕ) : ℝ) < ((j + 2 : ℕ) : ℝ) := by
        norm_num [hcontr, Nat.cast_add, Nat.cast_one] at hfloor_bounds ⊢
        linarith
      exact (lt_irrefl _ this)
    have hinv_lt : ε⁻¹ < (2 : ℝ) ^ (j + 2) :=
      lt_of_le_of_ne hinv_le hinv_ne
    have h := one_div_lt_one_div_of_lt (inv_pos.mpr hε_pos) hinv_lt
    simpa [one_div, inv_inv, inv_dyadic_radius (j + 1),
      show j + 1 + 1 = j + 2 by omega] using h
  have hsample :
      unitIntervalCoveringEntropyAtRadius ε =
        Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)) := by
    simp [unitIntervalCoveringEntropyAtRadius, unitIntervalCoveringNumber, j]
  have hdom_sample :=
    unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy j
  have hprofile_mono :
      unitIntervalDivergingEntropyProfile
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) ≤
        unitIntervalDivergingEntropyProfile ε :=
    unitIntervalDivergingEntropyProfile_guarded j ε (le_of_lt hleft) hright
  rw [hsample]
  exact hdom_sample.trans hprofile_mono

theorem unitIntervalCoveringEntropyAtRadius_intervalIntegrable_zero_half :
    IntervalIntegrable unitIntervalCoveringEntropyAtRadius volume
      (0 : ℝ) ((1 : ℝ) / 2) := by
  refine IntervalIntegrable.mono_fun'
    (g := unitIntervalDivergingEntropyProfile)
    unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half
    ?_ ?_
  · exact unitIntervalCoveringEntropyAtRadius_measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with ε hε
    rw [Real.norm_of_nonneg (unitIntervalCoveringEntropyAtRadius_nonneg ε)]
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)] at hε
    exact unitIntervalCoveringEntropyAtRadius_dominated hε

theorem unitIntervalCoveringEntropyAtRadius_guarded (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus unitIntervalCoveringEntropyAtRadius (1 : ℝ) j := by
  intro ε hleft hright
  by_cases hstrict : (1 : ℝ) / (2 : ℝ) ^ (j + 2) < ε
  · rw [unitIntervalCoveringEntropyAtRadius, unitIntervalCoveringEntropyAtRadius,
      unitIntervalCoveringNumber_const_on_halfOpenAnnulus j hstrict hright,
      unitIntervalCoveringNumber_dyadic j]
  · have hε_eq : ε = (1 : ℝ) / (2 : ℝ) ^ (j + 2) := by linarith
    subst ε
    rw [unitIntervalCoveringEntropyAtRadius, unitIntervalCoveringEntropyAtRadius,
      unitIntervalCoveringNumber_dyadic (j + 1),
      unitIntervalCoveringNumber_dyadic j]
    exact monotone_unitIntervalRoundedDyadicGridEntropy
      (Nat.le_add_right j 1)

/-- The integrand samples the genuine rounded-grid covering-number product. -/
-- fidelity: the integrand IS the genuine covering number at dyadic radii,
-- namely the rounded-grid finite-cover product `unitIntervalRoundedDyadicGridCoverCount`.
theorem unitIntervalCoveringEntropy_eq_genuine_count_sample (j : ℕ) :
    unitIntervalCoveringEntropyAtRadius
        ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) =
      Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)) := by
  rw [unitIntervalCoveringEntropyAtRadius, unitIntervalCoveringNumber_dyadic]

/-- The genuine covering-number integrand is not a disguised constant profile. -/
-- fidelity: the samples at `1 / 2` and `1 / 8` use different genuine
-- rounded-grid covering-number products.
theorem unitInterval_coveringEntropy_nonconstant :
    unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 2) ≠
      unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 8) := by
  have h0 :
      unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 2) =
        Real.sqrt (Real.log (15 : ℝ)) := by
    have hsample := unitIntervalCoveringEntropy_eq_genuine_count_sample 0
    norm_num [unitIntervalRoundedDyadicGridCoverCount] at hsample ⊢
    exact hsample
  have h2 :
      unitIntervalCoveringEntropyAtRadius ((1 : ℝ) / 8) =
        Real.sqrt (Real.log (153 : ℝ)) := by
    have hsample := unitIntervalCoveringEntropy_eq_genuine_count_sample 2
    norm_num [unitIntervalRoundedDyadicGridCoverCount] at hsample ⊢
    exact hsample
  intro h
  have hsqrt_eq : Real.sqrt (Real.log (15 : ℝ)) =
      Real.sqrt (Real.log (153 : ℝ)) := by
    exact h0.symm.trans (h.trans h2)
  have hsq := congrArg (fun x : ℝ => x ^ 2) hsqrt_eq
  have hlog_nonneg_15 : 0 ≤ Real.log (15 : ℝ) :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 15)
  have hlog_nonneg_153 : 0 ≤ Real.log (153 : ℝ) :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 153)
  change (Real.sqrt (Real.log (15 : ℝ))) ^ 2 =
    (Real.sqrt (Real.log (153 : ℝ))) ^ 2 at hsq
  rw [Real.sq_sqrt hlog_nonneg_15, Real.sq_sqrt hlog_nonneg_153] at hsq
  have hlog_lt : Real.log (15 : ℝ) < Real.log (153 : ℝ) :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 15)
      (by norm_num : (15 : ℝ) < 153)
  exact (ne_of_lt hlog_lt) hsq

/-- The genuine covering-number entropy integral has positive mass. -/
-- fidelity: positivity comes from the concrete `j = 0` sample on the
-- positive-width subinterval `(1 / 4, 1 / 2]`.
theorem unitInterval_coveringEntropy_integral_positive :
    0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
      unitIntervalCoveringEntropyAtRadius ε := by
  have hsample_pos :
      0 < Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 0 : ℝ)) := by
    have hcount : unitIntervalRoundedDyadicGridCoverCount 0 = 15 := by
      norm_num [unitIntervalRoundedDyadicGridCoverCount]
    rw [hcount]
    exact Real.sqrt_pos.mpr
      (Real.log_pos (by norm_num : (1 : ℝ) < 15))
  have hrect :
      (((1 : ℝ) / 2) - (1 / 4)) *
          Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 0 : ℝ)) ≤
        ∫ ε in ((1 : ℝ) / 4)..((1 : ℝ) / 2),
          unitIntervalCoveringEntropyAtRadius ε := by
    refine FiniteSubGaussianProcess.interval_const_mul_le_integral_of_le_on
      (f := unitIntervalCoveringEntropyAtRadius)
      (a := ((1 : ℝ) / 4)) (b := ((1 : ℝ) / 2))
      (c := Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount 0 : ℝ)))
      (by norm_num)
      (unitIntervalCoveringEntropyAtRadius_intervalIntegrable_zero_half.mono_set' ?_)
      ?_
    · intro x hx
      rw [Set.uIoc_of_le (by norm_num : ((1 : ℝ) / 4) ≤ (1 : ℝ) / 2)] at hx
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
      exact ⟨by linarith [hx.1], hx.2⟩
    · intro ε hε
      rcases hε with ⟨hleft, hright⟩
      by_cases hstrict : (1 : ℝ) / 4 < ε
      · have hconst :=
          unitIntervalCoveringNumber_const_on_halfOpenAnnulus
            (ε := ε) 0 (by norm_num; exact hstrict) (by simpa using hright)
        simp [unitIntervalCoveringEntropyAtRadius, hconst]
      · have hε_eq : ε = (1 : ℝ) / 4 := by linarith
        subst ε
        have hsample1 := unitIntervalCoveringEntropy_eq_genuine_count_sample 1
        norm_num at hsample1
        rw [hsample1]
        have hmono := monotone_unitIntervalRoundedDyadicGridEntropy
          (show 0 ≤ 1 by omega)
        simpa using hmono
  have htrunc_pos :
      0 < ∫ ε in ((1 : ℝ) / 4)..((1 : ℝ) / 2),
        unitIntervalCoveringEntropyAtRadius ε := by
    nlinarith [hsample_pos]
  have hdom :=
    GuardedContinuousDudley.guarded_truncatedIntegral_le_full_integral
      (m := 1) (entropyAtRadius := unitIntervalCoveringEntropyAtRadius)
      (radiusScale := (1 : ℝ)) (by norm_num)
      unitIntervalCoveringEntropyAtRadius_nonneg
      unitIntervalCoveringEntropyAtRadius_intervalIntegrable_zero_half
  norm_num at hdom
  exact lt_of_lt_of_le htrunc_pos hdom

private theorem unitInterval_roundedDyadic_hdyadicCoveringNumber_bound :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus unitIntervalCoveringEntropyAtRadius (1 : ℝ) j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable unitIntervalCoveringEntropyAtRadius volume
            ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
            ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation unitIntervalRademacherLinearProcess.weight
            unitIntervalRademacherLinearSup ≤
          1 + 2 * Real.sqrt (2 *
              unitIntervalRademacherLinearProcess.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              (1 : ℝ) m unitIntervalCoveringEntropyAtRadius + eta := by
  intro eta heta
  refine ⟨1, ?_, ?_, ?_⟩
  · intro j _hj
    exact unitIntervalCoveringEntropyAtRadius_guarded j
  · intro j _hj
    refine unitIntervalCoveringEntropyAtRadius_intervalIntegrable_zero_half.mono_set' ?_
    intro x hx
    rw [Set.uIoc_of_le (by
      have hwidth := FiniteSubGaussianProcess.dyadic_annulus_width_nonneg
        (radiusScale := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) (j + 1)
      linarith)] at hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    have hleft_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 2) := by positivity
    have hright_le_half :
        (1 : ℝ) / (2 : ℝ) ^ (j + 1) ≤ (1 : ℝ) / 2 := by
      simpa using dyadic_radius_le_of_le (i := 0) (j := j) (Nat.zero_le j)
    exact ⟨lt_trans hleft_pos hx.1, hx.2.trans hright_le_half⟩
  · have hfinite :=
      unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree 1
    have hbudget :
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) ≤
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            (1 : ℝ) 1 unitIntervalCoveringEntropyAtRadius := by
      refine
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum
          (m := 1)
          (entropyEnvelope := fun j : ℕ =>
            Real.sqrt
              (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))
          (entropyAtRadius := unitIntervalCoveringEntropyAtRadius)
          (radiusScale := (1 : ℝ)) (by norm_num) ?_
      intro j hj
      have hj0 : j = 0 := by
        have hjlt : j < 1 := Finset.mem_range.mp hj
        omega
      subst j
      rw [unitIntervalCoveringEntropy_eq_genuine_count_sample]
    have hcoef_nonneg :
        0 ≤ 2 * Real.sqrt (2 *
            unitIntervalRademacherLinearProcess.varianceProxy) := by
      positivity
    have hmul :=
      mul_le_mul_of_nonneg_left hbudget hcoef_nonneg
    linarith [hfinite, hmul, heta.le]

/-- Continuous Dudley entropy-integral bound for the unit-interval process
using the genuine real-radius covering-number staircase. -/
-- fidelity: the entropy integrand is `sqrt (log (unitIntervalCoveringNumber ε))`,
-- with dyadic samples equal to the genuine rounded-grid finite-cover products.
theorem continuous_dudley_entropy_integral_iSup_unitInterval_coveringNumber :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
          unitIntervalCoveringEntropyAtRadius ε) := by
  exact
    continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
      (P := unitIntervalRademacherLinearProcess)
      (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (entropyAtRadius := unitIntervalCoveringEntropyAtRadius)
      (supFunctional := unitIntervalRademacherLinearSup)
      (by norm_num)
      unitIntervalCoveringEntropyAtRadius_nonneg
      unitIntervalCoveringEntropyAtRadius_intervalIntegrable_zero_half
      unitInterval_roundedDyadic_hdyadicCoveringNumber_bound

end

end FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering
