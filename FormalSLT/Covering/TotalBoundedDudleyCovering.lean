import FormalSLT.Covering.GuardedDudleyIntegral
import FormalSLT.Covering.TotalBoundedDudley
import FormalSLT.Covering.UnitIntervalDudley
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Function.Floor

/-!
# Total-bounded dyadic covering-number staircase

This module adds the generic dyadic selected-cover-count staircase used by the
total-bounded Dudley lane. It does not assert minimal metric covering numbers:
the counts are the adjacent products selected by the existing
`TotalBoundedDudley` finite-net schedule, then wrapped in a monotone finite
prefix envelope so the closed guarded annulus condition is available.
-/

namespace FormalSLT.Covering.TotalBoundedDudleyCovering

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.TotalBoundedDudley

noncomputable section

universe u

variable {T : Type u}

/-- Dyadic level selected by the half-open, right-closed annulus
`(radiusScale / 2^(j+2), radiusScale / 2^(j+1)]`.

For positive radii in the Dudley interval this is
`⌊log_2 (radiusScale / ε)⌋ - 1`. -/
def totalBoundedCoveringIndex (radiusScale ε : ℝ) : ℕ :=
  Nat.floor (Real.logb 2 (radiusScale / ε)) - 1

/-- Monotone prefix envelope of the selected adjacent dyadic cover-count
products produced by total boundedness. -/
def totalBoundedDyadicCoverCountEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : ℕ :=
  (Finset.range (j + 1)).sup' (by simp)
    (fun k => dyadicChainingCoverCount (T := T) hT hradiusScale k)

/-- Real-radius selected-cover-count staircase for a totally bounded index
space. -/
def totalBoundedCoveringNumberAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) : ℕ :=
  totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale
    (totalBoundedCoveringIndex radiusScale ε)

/-- `ℕ∞` surface for the same selected-cover-count staircase. -/
def totalBoundedCoveringNumberAtRadiusENat
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) : ℕ∞ :=
  (totalBoundedCoveringNumberAtRadius (T := T) hT hradiusScale ε : ℕ∞)

/-- Entropy profile induced by the selected-cover-count staircase. -/
def totalBoundedCoveringEntropyAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) : ℝ :=
  Real.sqrt
    (Real.log
      (totalBoundedCoveringNumberAtRadius (T := T) hT hradiusScale ε : ℝ))

private lemma div_dyadic_radius
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    radiusScale / (radiusScale / (2 : ℝ) ^ (j + 1)) =
      (2 : ℝ) ^ (j + 1) := by
  field_simp [hradiusScale.ne', pow_ne_zero (j + 1) (by norm_num : (2 : ℝ) ≠ 0)]

private lemma logb_div_dyadic_radius
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Real.logb 2 (radiusScale / (radiusScale / (2 : ℝ) ^ (j + 1))) =
      (j + 1 : ℝ) := by
  rw [div_dyadic_radius hradiusScale j, ← Real.rpow_natCast]
  simp [Nat.cast_add, Nat.cast_one]

private lemma totalBoundedCoveringIndex_dyadic
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    totalBoundedCoveringIndex radiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) = j := by
  unfold totalBoundedCoveringIndex
  rw [logb_div_dyadic_radius hradiusScale j]
  rw [show (j + 1 : ℝ) = ((j + 1 : ℕ) : ℝ) by simp]
  rw [Nat.floor_natCast]
  omega

private lemma totalBoundedCoveringIndex_of_mem_halfOpenAnnulus
    {radiusScale ε : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ)
    (hleft : radiusScale / (2 : ℝ) ^ (j + 2) < ε)
    (hright : ε ≤ radiusScale / (2 : ℝ) ^ (j + 1)) :
    totalBoundedCoveringIndex radiusScale ε = j := by
  have hleft_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 2) := by positivity
  have hε_pos : 0 < ε := lt_trans hleft_pos hleft
  have hratio_lower :
      (2 : ℝ) ^ (j + 1) ≤ radiusScale / ε := by
    have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
    have hmul :
        (2 : ℝ) ^ (j + 1) * ε ≤ radiusScale := by
      calc
        (2 : ℝ) ^ (j + 1) * ε
            ≤ (2 : ℝ) ^ (j + 1) *
                (radiusScale / (2 : ℝ) ^ (j + 1)) := by
              exact mul_le_mul_of_nonneg_left hright hp.le
        _ = radiusScale := by
              field_simp [pow_ne_zero (j + 1)
                (by norm_num : (2 : ℝ) ≠ 0)]
    exact (le_div_iff₀ hε_pos).mpr hmul
  have hratio_upper :
      radiusScale / ε < (2 : ℝ) ^ (j + 2) := by
    have hp : 0 < (2 : ℝ) ^ (j + 2) := by positivity
    have hmul :
        radiusScale < (2 : ℝ) ^ (j + 2) * ε := by
      calc
        radiusScale =
            (2 : ℝ) ^ (j + 2) *
              (radiusScale / (2 : ℝ) ^ (j + 2)) := by
                field_simp [pow_ne_zero (j + 2)
                  (by norm_num : (2 : ℝ) ≠ 0)]
        _ < (2 : ℝ) ^ (j + 2) * ε := by
              exact mul_lt_mul_of_pos_left hleft hp
    exact (div_lt_iff₀ hε_pos).mpr hmul
  have hlog_lower :
      (j + 1 : ℝ) ≤ Real.logb 2 (radiusScale / ε) := by
    have hratio_pos : 0 < radiusScale / ε := div_pos hradiusScale hε_pos
    have h := (Real.logb_le_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))
      hratio_pos).mpr hratio_lower
    simpa [← Real.rpow_natCast, Real.logb_rpow
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  have hlog_upper :
      Real.logb 2 (radiusScale / ε) < (j + 2 : ℝ) := by
    have hratio_pos : 0 < radiusScale / ε := div_pos hradiusScale hε_pos
    have h := Real.logb_lt_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2) hratio_pos hratio_upper
    simpa [← Real.rpow_natCast, Real.logb_rpow
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  unfold totalBoundedCoveringIndex
  have hfloor : Nat.floor (Real.logb 2 (radiusScale / ε)) = j + 1 := by
    rw [Nat.floor_eq_iff]
    · exact ⟨by simpa [Nat.cast_add, Nat.cast_one] using hlog_lower,
        by
          norm_num [Nat.cast_add, Nat.cast_one] at hlog_upper ⊢
          linarith⟩
    · exact le_trans (by exact_mod_cast Nat.zero_le (j + 1)) hlog_lower
  rw [hfloor]
  omega

lemma dyadicChainingCoverCount_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < dyadicChainingCoverCount (T := T) hT hradiusScale j := by
  unfold dyadicChainingCoverCount
  exact Nat.mul_pos
    (FiniteNet.coveringNumber_pos
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net))
    (FiniteNet.coveringNumber_pos
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net))

lemma dyadicChainingCoverCount_le_envelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    dyadicChainingCoverCount (T := T) hT hradiusScale j ≤
      totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  unfold totalBoundedDyadicCoverCountEnvelope
  exact Finset.le_sup' _ (by simp)

lemma totalBoundedDyadicCoverCountEnvelope_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j :=
  lt_of_lt_of_le (dyadicChainingCoverCount_pos (T := T) hT hradiusScale j)
    (dyadicChainingCoverCount_le_envelope (T := T) hT hradiusScale j)

lemma monotone_totalBoundedDyadicCoverCountEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) :
    Monotone (totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale) := by
  intro i j hij
  unfold totalBoundedDyadicCoverCountEnvelope
  have hsubset : Finset.range (i + 1) ⊆ Finset.range (j + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ hij)
  have hnonempty : (Finset.range (i + 1)).Nonempty := by simp
  simpa using Finset.sup'_mono
    (f := fun k => dyadicChainingCoverCount (T := T) hT hradiusScale k)
    hsubset hnonempty

lemma monotone_totalBoundedCoveringEntropyAtScale
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) :
    Monotone
      (fun j : ℕ =>
        Real.sqrt (Real.log
          (totalBoundedDyadicCoverCountEnvelope
            (T := T) hT hradiusScale j : ℝ))) := by
  intro i j hij
  apply Real.sqrt_le_sqrt
  have hpos :
      (0 : ℝ) <
        (totalBoundedDyadicCoverCountEnvelope
          (T := T) hT hradiusScale i : ℝ) := by
    exact_mod_cast totalBoundedDyadicCoverCountEnvelope_pos
      (T := T) hT hradiusScale i
  have hle :
      (totalBoundedDyadicCoverCountEnvelope
          (T := T) hT hradiusScale i : ℝ) ≤
        (totalBoundedDyadicCoverCountEnvelope
          (T := T) hT hradiusScale j : ℝ) := by
    exact_mod_cast
      (monotone_totalBoundedDyadicCoverCountEnvelope
        (T := T) hT hradiusScale hij)
  exact Real.log_le_log hpos hle

/-- The real-radius staircase samples the dyadic selected-cover-count envelope
at every dyadic radius. -/
theorem totalBoundedCoveringNumberAtRadius_dyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    totalBoundedCoveringNumberAtRadius (T := T) hT hradiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) =
      totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  rw [totalBoundedCoveringNumberAtRadius, totalBoundedCoveringIndex_dyadic hradiusScale j]

/-- The selected-cover-count staircase is constant on each half-open,
right-closed dyadic annulus. -/
theorem totalBoundedCoveringNumberAtRadius_const_on_halfOpenAnnulus
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale ε : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ)
    (hleft : radiusScale / (2 : ℝ) ^ (j + 2) < ε)
    (hright : ε ≤ radiusScale / (2 : ℝ) ^ (j + 1)) :
    totalBoundedCoveringNumberAtRadius (T := T) hT hradiusScale ε =
      totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  simp [totalBoundedCoveringNumberAtRadius,
    totalBoundedCoveringIndex_of_mem_halfOpenAnnulus hradiusScale j hleft hright]

theorem totalBoundedCoveringNumberAtRadiusENat_ne_top
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) :
    totalBoundedCoveringNumberAtRadiusENat (T := T) hT hradiusScale ε ≠ ⊤ := by
  simp [totalBoundedCoveringNumberAtRadiusENat]

theorem totalBoundedCoveringNumberAtRadiusENat_toReal
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) :
    ENNReal.toReal
        (ENat.toENNReal
          (totalBoundedCoveringNumberAtRadiusENat
            (T := T) hT hradiusScale ε)) =
      (totalBoundedCoveringNumberAtRadius
        (T := T) hT hradiusScale ε : ℝ) := by
  simp [totalBoundedCoveringNumberAtRadiusENat, ENNReal.toReal_natCast]

theorem totalBoundedCoveringEntropyAtRadius_nonneg
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) :
    0 ≤ totalBoundedCoveringEntropyAtRadius (T := T) hT hradiusScale ε := by
  simp [totalBoundedCoveringEntropyAtRadius]

private lemma totalBoundedCoveringEntropyAtRadius_dyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    totalBoundedCoveringEntropyAtRadius (T := T) hT hradiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) =
      Real.sqrt
        (Real.log
          (totalBoundedDyadicCoverCountEnvelope
            (T := T) hT hradiusScale j : ℝ)) := by
  simp [totalBoundedCoveringEntropyAtRadius,
    totalBoundedCoveringNumberAtRadius_dyadic]

/-- The selected-cover-count entropy staircase satisfies the guarded closed
annulus condition. At the shared left endpoint the next prefix envelope is at
least the current one. -/
theorem totalBoundedCoveringEntropyAtRadius_guarded
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus
      (totalBoundedCoveringEntropyAtRadius
        (T := T) hT hradiusScale) radiusScale j := by
  intro ε hleft hright
  by_cases hstrict : radiusScale / (2 : ℝ) ^ (j + 2) < ε
  · rw [totalBoundedCoveringEntropyAtRadius_dyadic]
    have hconst :=
      totalBoundedCoveringNumberAtRadius_const_on_halfOpenAnnulus
        (T := T) hT hradiusScale j hstrict hright
    simp [totalBoundedCoveringEntropyAtRadius, hconst]
  · have hε_left : ε = radiusScale / (2 : ℝ) ^ (j + 2) := by
      exact le_antisymm (le_of_not_gt hstrict) hleft
    have hleft_dyadic :
        totalBoundedCoveringEntropyAtRadius (T := T) hT hradiusScale
            (radiusScale / (2 : ℝ) ^ (j + 2)) =
          Real.sqrt
            (Real.log
              (totalBoundedDyadicCoverCountEnvelope
                (T := T) hT hradiusScale (j + 1) : ℝ)) := by
      simpa [show j + 1 + 1 = j + 2 by omega] using
        totalBoundedCoveringEntropyAtRadius_dyadic
          (T := T) hT hradiusScale (j + 1)
    rw [hε_left, totalBoundedCoveringEntropyAtRadius_dyadic, hleft_dyadic]
    exact monotone_totalBoundedCoveringEntropyAtScale
      (T := T) hT hradiusScale (Nat.le_succ j)

/-- At a dyadic radius the selected-cover-count entropy dominates the finite
dyadic entropy envelope used by the total-bounded finite wrappers. -/
-- fidelity: the right side is built from the selected adjacent dyadic cover
-- counts produced by `TotalBoundedDudley`, not from a free real envelope.
theorem totalBoundedCoveringEntropy_dominates_dyadicEnvelope_sample
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    FiniteSubGaussianProcess.finitePrefixSupEnvelope
        (fun k => Real.sqrt
          (Real.log (dyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ))) j ≤
      totalBoundedCoveringEntropyAtRadius (T := T) hT hradiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) := by
  unfold FiniteSubGaussianProcess.finitePrefixSupEnvelope
  rw [totalBoundedCoveringEntropyAtRadius_dyadic]
  refine Finset.sup'_le _ _ ?_
  intro k hk
  apply Real.sqrt_le_sqrt
  have hpos :
      (0 : ℝ) < (dyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ) := by
    exact_mod_cast dyadicChainingCoverCount_pos (T := T) hT hradiusScale k
  have hk_le_j : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hcount_le :
      dyadicChainingCoverCount (T := T) hT hradiusScale k ≤
        totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
    have hkj :
        totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale k ≤
          totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j :=
      monotone_totalBoundedDyadicCoverCountEnvelope
        (T := T) hT hradiusScale hk_le_j
    exact (dyadicChainingCoverCount_le_envelope
      (T := T) hT hradiusScale k).trans hkj
  have hcount_le_real :
      (dyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ) ≤
        (totalBoundedDyadicCoverCountEnvelope
          (T := T) hT hradiusScale j : ℝ) := by
    exact_mod_cast hcount_le
  exact Real.log_le_log hpos hcount_le_real

/-- Concrete non-vacuity witness: on the unit interval, the generic
total-bounded selected-cover-count surface has a positive dyadic sample. -/
-- fidelity: this instantiates the generic total-bounded staircase on the
-- previously mechanized unit-interval total-bounded witness.
theorem unitInterval_totalBoundedCoveringNumber_sample_positive :
    0 <
      totalBoundedCoveringNumberAtRadius
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        (by norm_num : (0 : ℝ) < 1) ((1 : ℝ) / 2) := by
  have hsample :=
    totalBoundedCoveringNumberAtRadius_dyadic
      (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
      FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
      (by norm_num : (0 : ℝ) < 1) 0
  norm_num at hsample
  rw [hsample]
  exact totalBoundedDyadicCoverCountEnvelope_pos
    (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
    FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
    (by norm_num : (0 : ℝ) < 1) 0

end

end FormalSLT.Covering.TotalBoundedDudleyCovering
