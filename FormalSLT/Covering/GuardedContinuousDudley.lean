import FormalSLT.Covering.GuardedDudleyIntegral

/-!
# Guarded continuous Dudley finite-to-integral passage

This module records the continuous final step for guarded positive-radius
Dudley bounds. It isolates the passage from finite truncated integral bounds
to the full `0..radiusScale/2` integral, with no global
`Antitone entropyAtRadius` assumption.
-/

namespace FormalSLT.Covering.GuardedContinuousDudley

open scoped BigOperators Interval
open MeasureTheory
open FormalSLT.Covering.FiniteSubGaussianChaining

noncomputable section

/-- A positive-radius truncated entropy integral is dominated by the full
`0..radiusScale/2` entropy integral when the profile is nonnegative and
integrable on the full interval.

This is the continuous step needed after the guarded finite dyadic comparison:
it never evaluates the entropy profile at radius zero through an antitonicity
hypothesis. -/
theorem guarded_truncatedIntegral_le_full_integral
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2)) :
    (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
      entropyAtRadius ε) ≤
        ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  have ha_nonneg : (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) :=
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  have hsub1 :
      Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
  have hsub2 :
      Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
      Set.right_mem_uIcc
  have hI1 :
      IntervalIntegrable entropyAtRadius volume 0
        (radiusScale / (2 : ℝ) ^ (m + 1)) :=
    hint0.mono_set hsub1
  have hI2 :
      IntervalIntegrable entropyAtRadius volume
        (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
    hint0.mono_set hsub2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hnn :
      0 ≤ ∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)),
        entropyAtRadius ε :=
    intervalIntegral.integral_nonneg ha_nonneg (fun u _ => hentropy_nonneg u)
  linarith [hadd, hnn]

/-- Guarded continuous Dudley entropy integral bound from finite truncated
bounds.

The finite input is deliberately the post-guarded-truncation statement: for
every positive terminal error, some dyadic depth gives a finite expected
supremum bound with the positive-radius truncated integral. This theorem then
removes the truncation and yields the continuous `0..radiusScale/2` integral
bound without assuming `Antitone entropyAtRadius`. -/
theorem guarded_continuous_dudley_entropy_integral_nonempty_of_truncated_bounds
    {Ω T : Type*} [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (htruncated : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
            (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
              entropyAtRadius ε) + eta) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  refine le_of_forall_pos_le_add ?_
  intro eta heta
  rcases htruncated eta heta with ⟨m, hfinite⟩
  have hdom :=
    guarded_truncatedIntegral_le_full_integral
      (m := m) (entropyAtRadius := entropyAtRadius)
      hradiusScale hentropy_nonneg hint0
  have hsqrt_nonneg : 0 ≤ 4 * Real.sqrt (2 * P.varianceProxy) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdom hsqrt_nonneg
  have hbudget_eta :
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) + eta ≤
        coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) + eta := by
    linarith [hmul]
  exact hfinite.trans hbudget_eta

/-- Guarded continuous Dudley entropy integral bound from finite dyadic upper
sum bounds.

This is the guarded replacement for the global-antitone sum-to-integral step:
the finite input is allowed to be stated with the dyadic entropy upper sum, and
the only monotonicity needed is the positive-radius guarded annulus condition
from `GuardedDudleyIntegral`. -/
theorem guarded_continuous_dudley_entropy_integral_nonempty_of_upper_sum_bounds
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
          GuardedDudleyIntegral.GuardedAntitoneOnDyadicAnnulus
            entropyAtRadius radiusScale j) ∧
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
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  refine
    guarded_continuous_dudley_entropy_integral_nonempty_of_truncated_bounds
      (P := P) (coarseBudget := coarseBudget) (radiusScale := radiusScale)
      (entropyAtRadius := entropyAtRadius) (supFunctional := supFunctional)
      hradiusScale hentropy_nonneg hint0 ?_
  intro eta heta
  rcases hdyadic eta heta with ⟨m, hguard, hintervalIntegrable, hfinite⟩
  refine ⟨m, ?_⟩
  have hsum :=
    GuardedDudleyIntegral.finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral_guarded
      (m := m) (entropyAtRadius := entropyAtRadius) hradiusScale.le
      hguard hintervalIntegrable
  have hcoef_nonneg : 0 ≤ 2 * Real.sqrt (2 * P.varianceProxy) := by positivity
  have hmul :
      2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m entropyAtRadius ≤
        4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) := by
    calc
      2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m entropyAtRadius
          ≤ 2 * Real.sqrt (2 * P.varianceProxy) *
            (2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
              entropyAtRadius ε) := mul_le_mul_of_nonneg_left hsum hcoef_nonneg
      _ = 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) := by ring
  have hbudget_eta :
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
          FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m entropyAtRadius + eta ≤
        coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) + eta := by
    linarith [hmul]
  exact hfinite.trans hbudget_eta

end

end FormalSLT.Covering.GuardedContinuousDudley
