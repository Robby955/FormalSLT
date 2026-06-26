import FormalSLT.Covering.TotalBoundedDudleyMinimalCapstone
import FormalSLT.Covering.GuardedContinuousDudley

/-!
# Shifted one-radius minimal-cover entropy bridge

This module records the tractable part of the pure minimal-cover route. The
same-radius comparison is false: the finite projected-chain wrapper samples a
larger radius than the two cardinal-minimal covers used by one adjacent
projection pair. The valid comparison is shifted by two dyadic steps.

The public bridge below bounds the adjacent-product entropy at level `j` by
`sqrt 2` times the single-radius genuine minimal-cover entropy at the next
dyadic net radius. This is not yet the final pure integral capstone; the
remaining analytic step is a finite dyadic summation or interval-integral shift
comparison that absorbs the radius shift into constants.
-/

namespace FormalSLT.Covering.TotalBoundedDudleyMinimalShift

open scoped BigOperators Interval
open MeasureTheory
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Covering.TotalBoundedMinimalCovering
open FormalSLT.Covering.TotalBoundedDudleyMinimalCapstone

noncomputable section

universe u

variable {T : Type u}

/-- The genuine minimal metric covering number is antitone in the radius on
positive radii. -/
theorem minimalMetricCoveringNumber_antitone
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hεδ : ε ≤ δ) :
    minimalMetricCoveringNumber (T := T) hT hδ ≤
      minimalMetricCoveringNumber (T := T) hT hε := by
  rcases minimalMetricCoveringNumber_spec (T := T) hT hε with
    ⟨C, hcard, hcover⟩
  exact minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
    (T := T) hT hδ
    ⟨C, hcard, by
      intro t
      rcases hcover t with ⟨c, hc, hdist⟩
      exact ⟨c, hc, hdist.trans hεδ⟩⟩

private theorem dyadicChainingNetRadius_antitone
    {radiusScale : ℝ} (hradiusScale_nonneg : 0 ≤ radiusScale) :
    Antitone (dyadicChainingNetRadius radiusScale) := by
  intro i j hij
  unfold dyadicChainingNetRadius
  have hpow_pos : 0 < (2 : ℝ) ^ (i + 2) := by positivity
  have hpow_le : (2 : ℝ) ^ (i + 2) ≤ (2 : ℝ) ^ (j + 2) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.add_le_add_right hij 2)
  exact div_le_div_of_nonneg_left hradiusScale_nonneg hpow_pos hpow_le

/-- Adjacent cardinal-minimal dyadic cover counts are bounded by the square of
the next smaller-radius genuine minimal covering number. -/
theorem minimalDyadicChainingCoverCount_le_next_minimalMetricCoveringNumber_sq
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalDyadicChainingCoverCount (T := T) hT hradiusScale j ≤
      (minimalMetricCoveringNumber
        (T := T) hT (dyadicChainingNetRadius_pos hradiusScale (j + 1))) ^ 2 := by
  rw [minimalDyadicChainingCoverCount_eq_minimalMetricCoveringNumber_mul]
  have hradius_le :
      dyadicChainingNetRadius radiusScale (j + 1) ≤
        dyadicChainingNetRadius radiusScale j :=
    dyadicChainingNetRadius_antitone hradiusScale.le (Nat.le_succ j)
  have hcount_le :
      minimalMetricCoveringNumber (T := T) hT
          (dyadicChainingNetRadius_pos hradiusScale j) ≤
        minimalMetricCoveringNumber (T := T) hT
          (dyadicChainingNetRadius_pos hradiusScale (j + 1)) :=
    minimalMetricCoveringNumber_antitone
      (T := T) hT
      (dyadicChainingNetRadius_pos hradiusScale (j + 1))
      (dyadicChainingNetRadius_pos hradiusScale j)
      hradius_le
  simpa [pow_two] using
    Nat.mul_le_mul_right
      (minimalMetricCoveringNumber
        (T := T) hT (dyadicChainingNetRadius_pos hradiusScale (j + 1)))
      hcount_le

/-- Genuine minimal-cover entropy at one dyadic net radius. -/
def minimalMetricCoveringEntropyAtDyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : ℝ :=
  Real.sqrt
    (Real.log
      (minimalMetricCoveringNumber
        (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j) : ℝ))

private theorem minimalMetricCoveringEntropyAtDyadic_nonneg
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 ≤ minimalMetricCoveringEntropyAtDyadic (T := T) hT hradiusScale j := by
  simp [minimalMetricCoveringEntropyAtDyadic]

private theorem monotone_minimalMetricCoveringEntropyAtDyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) :
    Monotone (minimalMetricCoveringEntropyAtDyadic (T := T) hT hradiusScale) := by
  intro i j hij
  apply Real.sqrt_le_sqrt
  have hradius_le :
      dyadicChainingNetRadius radiusScale j ≤
        dyadicChainingNetRadius radiusScale i :=
    dyadicChainingNetRadius_antitone hradiusScale.le hij
  have hcount_le :
      minimalMetricCoveringNumber (T := T) hT
          (dyadicChainingNetRadius_pos hradiusScale i) ≤
        minimalMetricCoveringNumber (T := T) hT
          (dyadicChainingNetRadius_pos hradiusScale j) :=
    minimalMetricCoveringNumber_antitone
      (T := T) hT
      (dyadicChainingNetRadius_pos hradiusScale j)
      (dyadicChainingNetRadius_pos hradiusScale i)
      hradius_le
  have hpos :
      (0 : ℝ) <
        (minimalMetricCoveringNumber
          (T := T) hT (dyadicChainingNetRadius_pos hradiusScale i) : ℝ) := by
    exact_mod_cast minimalMetricCoveringNumber_pos
      (T := T) hT (dyadicChainingNetRadius_pos hradiusScale i)
  have hle :
      (minimalMetricCoveringNumber
          (T := T) hT (dyadicChainingNetRadius_pos hradiusScale i) : ℝ) ≤
        (minimalMetricCoveringNumber
          (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j) : ℝ) := by
    exact_mod_cast hcount_le
  exact Real.log_le_log hpos hle

/-- Adjacent-product entropy is bounded by `sqrt 2` times the next
single-radius genuine minimal-cover entropy. -/
theorem minimalDyadicChainingCoverCount_entropy_le_sqrt_two_mul_next_minimalMetricCoveringEntropy
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Real.sqrt
        (Real.log
          (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ)) ≤
      Real.sqrt 2 *
        minimalMetricCoveringEntropyAtDyadic
          (T := T) hT hradiusScale (j + 1) := by
  let N : ℕ :=
    minimalMetricCoveringNumber
      (T := T) hT (dyadicChainingNetRadius_pos hradiusScale (j + 1))
  have hcount_pos :
      (0 : ℝ) <
        (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ) := by
    exact_mod_cast minimalDyadicChainingCoverCount_pos
      (T := T) hT hradiusScale j
  have hcount_le_sq_nat :
      minimalDyadicChainingCoverCount (T := T) hT hradiusScale j ≤ N ^ 2 := by
    simpa [N] using
      minimalDyadicChainingCoverCount_le_next_minimalMetricCoveringNumber_sq
        (T := T) hT hradiusScale j
  have hcount_le_sq_real :
      (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ) ≤
        (N : ℝ) ^ 2 := by
    have hcast :
        (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ) ≤
          ((N ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hcount_le_sq_nat
    simpa using hcast
  have hlog_le :
      Real.log
          (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ) ≤
        2 * Real.log (N : ℝ) := by
    calc
      Real.log
          (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ)
          ≤ Real.log ((N : ℝ) ^ 2) :=
            Real.log_le_log hcount_pos hcount_le_sq_real
      _ = 2 * Real.log (N : ℝ) := by
            rw [Real.log_pow]
            norm_num
  have hsqrt_le :
      Real.sqrt
          (Real.log
            (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ)) ≤
        Real.sqrt (2 * Real.log (N : ℝ)) :=
    Real.sqrt_le_sqrt (by simpa [mul_comm] using hlog_le)
  have hsqrt_eq :
      Real.sqrt (2 * Real.log (N : ℝ)) =
        Real.sqrt 2 * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.log (N : ℝ))]
  simpa [minimalMetricCoveringEntropyAtDyadic, N, hsqrt_eq] using hsqrt_le

/-- Minimal covering number as a total real-radius profile. Nonpositive radii
are assigned the harmless value `1`; all dyadic samples used below are
positive. -/
def minimalMetricCoveringNumberAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) : ℕ :=
  if hε : 0 < ε then minimalMetricCoveringNumber (T := T) hT hε else 1

private theorem minimalMetricCoveringNumberAtRadius_of_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {ε : ℝ} (hε : 0 < ε) :
    minimalMetricCoveringNumberAtRadius (T := T) hT ε =
      minimalMetricCoveringNumber (T := T) hT hε := by
  simp [minimalMetricCoveringNumberAtRadius, hε]

/-- One-radius genuine minimal-cover entropy as a real-radius profile. -/
def minimalMetricCoveringEntropyAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) : ℝ :=
  Real.sqrt
    (Real.log (minimalMetricCoveringNumberAtRadius (T := T) hT ε : ℝ))

/-- Shifted one-radius profile that dominates the adjacent-product entropy at
the dyadic samples used by the finite wrapper. -/
def shiftedMinimalMetricCoveringEntropyAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) : ℝ :=
  Real.sqrt 2 * minimalMetricCoveringEntropyAtRadius (T := T) hT (ε / 4)

private theorem shiftedMinimalMetricCoveringEntropyAtRadius_dyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    shiftedMinimalMetricCoveringEntropyAtRadius (T := T) hT
        (radiusScale / (2 : ℝ) ^ (j + 1)) =
      Real.sqrt 2 *
        minimalMetricCoveringEntropyAtDyadic
          (T := T) hT hradiusScale (j + 1) := by
  have hpos :
      0 < radiusScale / (2 : ℝ) ^ (j + 1) / 4 := by positivity
  have hshift :
      radiusScale / (2 : ℝ) ^ (j + 1) / 4 =
        dyadicChainingNetRadius radiusScale (j + 1) := by
    unfold dyadicChainingNetRadius
    field_simp [pow_succ]
    ring
  rw [shiftedMinimalMetricCoveringEntropyAtRadius,
    minimalMetricCoveringEntropyAtRadius,
    minimalMetricCoveringEntropyAtDyadic, hshift]
  rw [minimalMetricCoveringNumberAtRadius_of_pos
    (T := T) hT (dyadicChainingNetRadius_pos hradiusScale (j + 1))]

/-- The shifted one-radius minimal-cover entropy dominates the finite
prefix-envelope sample induced by adjacent cardinal-minimal dyadic products. -/
theorem minimalDyadicChainingCoverCountEntropy_dominates_shiftedMinimalEntropy_sample
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    FiniteSubGaussianProcess.finitePrefixSupEnvelope
        (fun k => Real.sqrt
          (Real.log
            (minimalDyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ))) j ≤
      shiftedMinimalMetricCoveringEntropyAtRadius (T := T) hT
        (radiusScale / (2 : ℝ) ^ (j + 1)) := by
  rw [shiftedMinimalMetricCoveringEntropyAtRadius_dyadic
    (T := T) hT hradiusScale j]
  unfold FiniteSubGaussianProcess.finitePrefixSupEnvelope
  refine Finset.sup'_le _ _ ?_
  intro k hk
  have hk_le_j : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hstep :=
    minimalDyadicChainingCoverCount_entropy_le_sqrt_two_mul_next_minimalMetricCoveringEntropy
      (T := T) hT hradiusScale k
  have hmono :
      minimalMetricCoveringEntropyAtDyadic
          (T := T) hT hradiusScale (k + 1) ≤
        minimalMetricCoveringEntropyAtDyadic
          (T := T) hT hradiusScale (j + 1) :=
    monotone_minimalMetricCoveringEntropyAtDyadic
      (T := T) hT hradiusScale (Nat.succ_le_succ hk_le_j)
  have hcoef_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  exact hstep.trans
    (mul_le_mul_of_nonneg_left hmono hcoef_nonneg)

private theorem integral_zero_to_eighth_le_zero_to_half
    {radiusScale : ℝ} (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2)) :
    (∫ ε in (0 : ℝ)..(radiusScale / 8), entropyAtRadius ε) ≤
      ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
  have hhalf_pos : 0 < radiusScale / 2 := half_pos hradiusScale
  have height_nonneg : 0 ≤ radiusScale / 8 := by positivity
  have height_le_half : radiusScale / 8 ≤ radiusScale / 2 := by
    nlinarith [hradiusScale]
  have hsub1 :
      Set.uIcc (0 : ℝ) (radiusScale / 8) ⊆
        Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hhalf_pos.le]; exact ⟨height_nonneg, height_le_half⟩)
  have hsub2 :
      Set.uIcc (radiusScale / 8) (radiusScale / 2) ⊆
        Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hhalf_pos.le]; exact ⟨height_nonneg, height_le_half⟩)
      Set.right_mem_uIcc
  have hI1 :
      IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 8) :=
    hint0.mono_set hsub1
  have hI2 :
      IntervalIntegrable entropyAtRadius volume (radiusScale / 8) (radiusScale / 2) :=
    hint0.mono_set hsub2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have htail_nonneg :
      0 ≤ ∫ ε in (radiusScale / 8)..(radiusScale / 2), entropyAtRadius ε :=
    intervalIntegral.integral_nonneg height_le_half
      (fun ε _ => hentropy_nonneg ε)
  linarith [hadd, htail_nonneg]

/-- A shifted dyadic upper sum with profile `ε ↦ sqrt 2 * f (ε / 4)` is
controlled by the pure profile integral on the original interval, with the
radius-shift loss made explicit. -/
theorem finiteDyadicEntropyAtRadiusUpperSum_shifted_div_four_le_eight_mul_full_integral
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hguard : ∀ j ∈ Finset.range m,
      GuardedAntitoneOnDyadicAnnulus entropyAtRadius (radiusScale / 4) j)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius volume
        ((radiusScale / 4) / (2 : ℝ) ^ (j + 2))
        ((radiusScale / 4) / (2 : ℝ) ^ (j + 1))) :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m (fun ε => Real.sqrt 2 * entropyAtRadius (ε / 4)) ≤
      8 * Real.sqrt 2 *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  have hscale :
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          radiusScale m (fun ε => Real.sqrt 2 * entropyAtRadius (ε / 4)) =
        4 * Real.sqrt 2 *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            (radiusScale / 4) m entropyAtRadius := by
    rw [FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum,
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    have hwidth :
        radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1) =
          4 * ((radiusScale / 4) / (2 : ℝ) ^ j -
            (radiusScale / 4) / (2 : ℝ) ^ (j + 1)) := by
      field_simp [pow_succ]
    have hsample :
        radiusScale / (2 : ℝ) ^ (j + 1) / 4 =
          (radiusScale / 4) / (2 : ℝ) ^ (j + 1) := by
      field_simp
    rw [hwidth, hsample]
    ring
  have hsum_truncated :=
    GuardedDudleyIntegral.finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral_guarded
      (m := m) (entropyAtRadius := entropyAtRadius)
      (radiusScale := radiusScale / 4) (by positivity : 0 ≤ radiusScale / 4)
      hguard hintervalIntegrable
  have hquarter_pos : 0 < radiusScale / 4 := by positivity
  have hquarter_half :
      (radiusScale / 4) / 2 = radiusScale / 8 := by ring
  have hsub_eighth :
      Set.uIcc (0 : ℝ) ((radiusScale / 4) / 2) ⊆
        Set.uIcc (0 : ℝ) (radiusScale / 2) := by
    rw [hquarter_half]
    have hhalf_pos : 0 < radiusScale / 2 := half_pos hradiusScale
    have height_nonneg : 0 ≤ radiusScale / 8 := by positivity
    have height_le_half : radiusScale / 8 ≤ radiusScale / 2 := by
      nlinarith [hradiusScale]
    exact Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hhalf_pos.le]; exact ⟨height_nonneg, height_le_half⟩)
  have hint_eighth :
      IntervalIntegrable entropyAtRadius volume 0 ((radiusScale / 4) / 2) :=
    hint0.mono_set hsub_eighth
  have htruncated_to_eighth :=
    FormalSLT.Covering.GuardedContinuousDudley.guarded_truncatedIntegral_le_full_integral
      (radiusScale := radiusScale / 4) (m := m)
      (entropyAtRadius := entropyAtRadius)
      hquarter_pos hentropy_nonneg hint_eighth
  have height_to_half :=
    integral_zero_to_eighth_le_zero_to_half
      (entropyAtRadius := entropyAtRadius) hradiusScale hentropy_nonneg hint0
  have htruncated_to_half :
      (∫ ε in ((radiusScale / 4) / (2 : ℝ) ^ (m + 1))..((radiusScale / 4) / 2),
        entropyAtRadius ε) ≤
        ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
    exact htruncated_to_eighth.trans (by simpa [hquarter_half] using height_to_half)
  have hsum_full :
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          (radiusScale / 4) m entropyAtRadius ≤
        2 * (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
    exact hsum_truncated.trans
      (mul_le_mul_of_nonneg_left htruncated_to_half
        (by norm_num : 0 ≤ (2 : ℝ)))
  rw [hscale]
  have hcoef_nonneg : 0 ≤ 4 * Real.sqrt 2 := by positivity
  calc
    4 * Real.sqrt 2 *
        FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          (radiusScale / 4) m entropyAtRadius
        ≤ 4 * Real.sqrt 2 *
          (2 * (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)) :=
          mul_le_mul_of_nonneg_left hsum_full hcoef_nonneg
    _ = 8 * Real.sqrt 2 *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by ring

private theorem minimalMetricCoveringEntropyAtRadius_nonneg
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) :
    0 ≤ minimalMetricCoveringEntropyAtRadius (T := T) hT ε := by
  simp [minimalMetricCoveringEntropyAtRadius]

private theorem minimalMetricCoveringEntropyAtRadius_guarded
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus
      (minimalMetricCoveringEntropyAtRadius (T := T) hT) radiusScale j := by
  intro ε hleft hright
  have hsample_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 1) := by positivity
  have hleft_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 2) := by positivity
  have hε_pos : 0 < ε := lt_of_lt_of_le hleft_pos hleft
  unfold minimalMetricCoveringEntropyAtRadius
  rw [minimalMetricCoveringNumberAtRadius_of_pos (T := T) hT hsample_pos,
    minimalMetricCoveringNumberAtRadius_of_pos (T := T) hT hε_pos]
  apply Real.sqrt_le_sqrt
  have hcount_le :
      minimalMetricCoveringNumber (T := T) hT hsample_pos ≤
        minimalMetricCoveringNumber (T := T) hT hε_pos :=
    minimalMetricCoveringNumber_antitone (T := T) hT hε_pos hsample_pos hright
  have hpos :
      (0 : ℝ) <
        (minimalMetricCoveringNumber (T := T) hT hsample_pos : ℝ) := by
    exact_mod_cast minimalMetricCoveringNumber_pos (T := T) hT hsample_pos
  have hle :
      (minimalMetricCoveringNumber (T := T) hT hsample_pos : ℝ) ≤
        (minimalMetricCoveringNumber (T := T) hT hε_pos : ℝ) := by
    exact_mod_cast hcount_le
  exact Real.log_le_log hpos hle

private theorem minimalMetricCoveringEntropyAtRadius_intervalIntegrable_div_four_dyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (hint0 :
      IntervalIntegrable
        (minimalMetricCoveringEntropyAtRadius (T := T) hT)
        volume 0 (radiusScale / 2))
    (m : ℕ) :
    ∀ j ∈ Finset.range m,
      IntervalIntegrable
        (minimalMetricCoveringEntropyAtRadius (T := T) hT)
        volume
        ((radiusScale / 4) / (2 : ℝ) ^ (j + 2))
        ((radiusScale / 4) / (2 : ℝ) ^ (j + 1)) := by
  intro j _hj
  have hhalf_pos : 0 < radiusScale / 2 := half_pos hradiusScale
  have ha_nonneg : 0 ≤ (radiusScale / 4) / (2 : ℝ) ^ (j + 2) := by positivity
  have hb_nonneg : 0 ≤ (radiusScale / 4) / (2 : ℝ) ^ (j + 1) := by positivity
  have hb_le_eighth :
      (radiusScale / 4) / (2 : ℝ) ^ (j + 1) ≤ radiusScale / 8 := by
    have hpow_ge : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num)
        (Nat.le_add_left 1 j)
      simpa [Nat.add_comm] using h
    have hdiv :=
      div_le_div_of_nonneg_left
        (by positivity : 0 ≤ radiusScale / 4)
        (by norm_num : (0 : ℝ) < 2) hpow_ge
    simpa [show (radiusScale / 4) / 2 = radiusScale / 8 by ring] using hdiv
  have height_le_half : radiusScale / 8 ≤ radiusScale / 2 := by
    nlinarith [hradiusScale]
  have hb_le_half :
      (radiusScale / 4) / (2 : ℝ) ^ (j + 1) ≤ radiusScale / 2 :=
    hb_le_eighth.trans height_le_half
  have ha_le_b :
      (radiusScale / 4) / (2 : ℝ) ^ (j + 2) ≤
        (radiusScale / 4) / (2 : ℝ) ^ (j + 1) := by
    have hpow_pos : 0 < (2 : ℝ) ^ (j + 1) := by positivity
    have hpow_le :
        (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 2) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    exact div_le_div_of_nonneg_left
      (by positivity : 0 ≤ radiusScale / 4) hpow_pos hpow_le
  have ha_le_half :
      (radiusScale / 4) / (2 : ℝ) ^ (j + 2) ≤ radiusScale / 2 :=
    ha_le_b.trans hb_le_half
  have ha_mem :
      (radiusScale / 4) / (2 : ℝ) ^ (j + 2) ∈
        Set.uIcc (0 : ℝ) (radiusScale / 2) := by
    rw [Set.uIcc_of_le hhalf_pos.le]
    exact ⟨ha_nonneg, ha_le_half⟩
  have hb_mem :
      (radiusScale / 4) / (2 : ℝ) ^ (j + 1) ∈
        Set.uIcc (0 : ℝ) (radiusScale / 2) := by
    rw [Set.uIcc_of_le hhalf_pos.le]
    exact ⟨hb_nonneg, hb_le_half⟩
  exact hint0.mono_set (Set.uIcc_subset_uIcc ha_mem hb_mem)

/-- Totally bounded continuous Dudley bound with the pure genuine
`minimalMetricCoveringNumber` entropy integrand, paying an explicit constant
for the dyadic shift from adjacent projection-pair products to one-radius
minimal covers. -/
theorem continuous_dudley_entropy_integral_iSup_totalBounded_minimalMetricCoveringNumber_shifted
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hint0 :
      IntervalIntegrable
        (minimalMetricCoveringEntropyAtRadius (T := T) hT)
        volume 0 (radiusScale / 2))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        MinimalSeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius :=
            shiftedMinimalMetricCoveringEntropyAtRadius (T := T) hT)
          (supFunctional := supFunctional) eta m) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 16 * Real.sqrt (2 * P.varianceProxy) * Real.sqrt 2 *
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          minimalMetricCoveringEntropyAtRadius (T := T) hT ε) := by
  refine _root_.le_of_forall_pos_le_add ?_
  intro eta heta
  rcases hchoose eta heta with ⟨m, hchoice⟩
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, separabilityError, terminalError,
      herror, _hintervalIntegrable, hseparable,
      hterminalApprox, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  let shiftedEntropy : ℝ → ℝ :=
    shiftedMinimalMetricCoveringEntropyAtRadius (T := T) hT
  let pureEntropy : ℝ → ℝ :=
    minimalMetricCoveringEntropyAtRadius (T := T) hT
  let terminalNet :=
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale m).net
  let projectedSup : Ω → ℝ :=
    fun ω => finiteSup
      (fun u : FiniteNet.ProjectedIndex terminalNet =>
        P.X ω (terminalNet.center u.1))
  have hadapter :
      finiteExpectation P.weight supFunctional ≤
        finiteExpectation P.weight projectedSup +
          (separabilityError + terminalError) := by
    exact finiteExpectation_supFunctional_le_projected_add_skeleton_terminalError
      P.weight_nonneg P.weight_sum_one terminalNet embed P.X
      supFunctional separabilityError terminalError hseparable
      hterminalApprox
  have hprojected :
      finiteExpectation P.weight projectedSup ≤
        coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy := by
    simpa [shiftedEntropy, terminalNet, projectedSup] using
      finite_projectedNet_dudley_entropy_sum_totalBounded_minimalDyadic_entropy_integral_comparison_nonempty
        (P := P) (hT := hT) (m := m) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (entropyAtRadius := shiftedEntropy)
        (integralBudget :=
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy)
        hradiusScale hdistP hvariance
        (by
          intro j hj
          simpa [shiftedEntropy] using
            minimalDyadicChainingCoverCountEntropy_dominates_shiftedMinimalEntropy_sample
              (T := T) hT hradiusScale j)
        le_rfl
        hcoarse
  have hfinite_with_error :
      finiteExpectation P.weight supFunctional ≤
        coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy +
          (separabilityError + terminalError) := by
    linarith [hadapter, hprojected]
  have hfinite_eta :
      finiteExpectation P.weight supFunctional ≤
        coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy + eta := by
    exact hfinite_with_error.trans
      (by
        have hbudget :=
          add_le_add_left herror
            (coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
              FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
                radiusScale m shiftedEntropy)
        simpa [add_comm, add_left_comm, add_assoc] using hbudget)
  have hpure_interval :
      ∀ j ∈ Finset.range m,
        IntervalIntegrable pureEntropy volume
          ((radiusScale / 4) / (2 : ℝ) ^ (j + 2))
          ((radiusScale / 4) / (2 : ℝ) ^ (j + 1)) := by
    simpa [pureEntropy] using
      minimalMetricCoveringEntropyAtRadius_intervalIntegrable_div_four_dyadic
        (T := T) hT hradiusScale hint0 m
  have hsum_shift :
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          radiusScale m shiftedEntropy ≤
        8 * Real.sqrt 2 *
          (∫ ε in (0 : ℝ)..(radiusScale / 2),
            minimalMetricCoveringEntropyAtRadius (T := T) hT ε) := by
    simpa [shiftedEntropy, pureEntropy, shiftedMinimalMetricCoveringEntropyAtRadius] using
      finiteDyadicEntropyAtRadiusUpperSum_shifted_div_four_le_eight_mul_full_integral
        (m := m) (entropyAtRadius := pureEntropy) hradiusScale
        (by
          intro ε
          simpa [pureEntropy] using
            minimalMetricCoveringEntropyAtRadius_nonneg (T := T) hT ε)
        (by simpa [pureEntropy] using hint0)
        (by
          intro j hj
          simpa [pureEntropy] using
            minimalMetricCoveringEntropyAtRadius_guarded
              (T := T) hT (by positivity : 0 < radiusScale / 4) j)
        hpure_interval
  have hcoef_nonneg : 0 ≤ 2 * Real.sqrt (2 * P.varianceProxy) := by positivity
  have hsum_budget :
      2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy ≤
        16 * Real.sqrt (2 * P.varianceProxy) * Real.sqrt 2 *
          (∫ ε in (0 : ℝ)..(radiusScale / 2),
            minimalMetricCoveringEntropyAtRadius (T := T) hT ε) := by
    calc
      2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy
          ≤ 2 * Real.sqrt (2 * P.varianceProxy) *
            (8 * Real.sqrt 2 *
              (∫ ε in (0 : ℝ)..(radiusScale / 2),
                minimalMetricCoveringEntropyAtRadius (T := T) hT ε)) :=
            mul_le_mul_of_nonneg_left hsum_shift hcoef_nonneg
      _ = 16 * Real.sqrt (2 * P.varianceProxy) * Real.sqrt 2 *
          (∫ ε in (0 : ℝ)..(radiusScale / 2),
            minimalMetricCoveringEntropyAtRadius (T := T) hT ε) := by ring
  have htarget_eta :
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m shiftedEntropy + eta ≤
        coarseBudget + 16 * Real.sqrt (2 * P.varianceProxy) * Real.sqrt 2 *
          (∫ ε in (0 : ℝ)..(radiusScale / 2),
            minimalMetricCoveringEntropyAtRadius (T := T) hT ε) + eta := by
    linarith [hsum_budget]
  exact hfinite_eta.trans htarget_eta

/-- Unit-interval nonnegativity sanity check for the shifted minimal-cover
entropy profile. -/
theorem unitInterval_shiftedMinimalMetricCoveringEntropy_sample_nonneg :
    0 ≤
      shiftedMinimalMetricCoveringEntropyAtRadius
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        ((1 : ℝ) / 2) := by
  have hleft : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hright :
      0 ≤
        minimalMetricCoveringEntropyAtRadius
          (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
          FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
          (((1 : ℝ) / 2) / 4) := by
    simp [minimalMetricCoveringEntropyAtRadius]
  exact mul_nonneg hleft hright

end

end FormalSLT.Covering.TotalBoundedDudleyMinimalShift
