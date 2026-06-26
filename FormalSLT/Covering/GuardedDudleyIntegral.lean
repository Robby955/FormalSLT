import FormalSLT.Covering.FiniteSubGaussianChaining
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Guarded positive-radius Dudley finite-to-integral bridge

This module adds a finite, truncated-annulus variant of the Dudley
sum-to-integral comparison. The existing comparison assumes a globally
real-valued `Antitone entropyAtRadius`, which evaluates the entropy profile at
zero and therefore bounds it on every positive radius. The guarded comparison
below only asks for the lower-endpoint domination needed on each positive
dyadic annulus used by the finite sum.

The result is deliberately finite-scale. It does not re-state the continuous
supremum theorem and it does not instantiate a unit-interval covering profile.
-/

namespace FormalSLT.Covering.GuardedDudleyIntegral

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining

noncomputable section

/-- Local positive-radius monotonicity needed on one dyadic annulus.

At scale `j`, the finite entropy upper sum samples the larger radius
`radiusScale / 2^(j+1)`. This hypothesis says that sample is dominated by the
entropy profile throughout the annulus
`[radiusScale / 2^(j+2), radiusScale / 2^(j+1)]`. No value at radius zero is
mentioned. -/
def GuardedAntitoneOnDyadicAnnulus
    (entropyAtRadius : ℝ → ℝ) (radiusScale : ℝ) (j : ℕ) : Prop :=
  ∀ ε : ℝ,
    radiusScale / (2 : ℝ) ^ (j + 2) ≤ ε →
      ε ≤ radiusScale / (2 : ℝ) ^ (j + 1) →
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) ≤
          entropyAtRadius ε

/-- Guarded lower-endpoint comparison on one dyadic annulus.

This is the exact local replacement for
`FiniteSubGaussianChaining.dyadic_lowerEndpoint_mul_width_le_intervalIntegral`:
it replaces global antitonicity with `GuardedAntitoneOnDyadicAnnulus`. -/
theorem guarded_dyadic_lowerEndpoint_mul_width_le_intervalIntegral
    {radiusScale : ℝ} (entropyAtRadius : ℝ → ℝ) (j : ℕ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hguard : GuardedAntitoneOnDyadicAnnulus entropyAtRadius radiusScale j)
    (hintervalIntegrable :
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    (radiusScale / (2 : ℝ) ^ (j + 1) -
        radiusScale / (2 : ℝ) ^ (j + 2)) *
      entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) ≤
        ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε := by
  have hab :
      radiusScale / (2 : ℝ) ^ (j + 2) ≤
        radiusScale / (2 : ℝ) ^ (j + 1) := by
    have hwidth :=
      FiniteSubGaussianProcess.dyadic_annulus_width_nonneg
        (radiusScale := radiusScale)
        hradiusScale_nonneg (j + 1)
    linarith
  exact FiniteSubGaussianProcess.interval_const_mul_le_integral_of_le_on
    hab hintervalIntegrable
    (by
      intro ε hε
      exact hguard ε hε.1 hε.2)

/-- Guarded shifted-annulus finite sum-to-integral comparison.

The comparison is finite and only needs positive-radius annulus domination for
the finitely many dyadic annuli in `range m`; it never asks for
`entropyAtRadius 0`. -/
theorem finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum_guarded
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hguard : ∀ j ∈ Finset.range m,
      GuardedAntitoneOnDyadicAnnulus entropyAtRadius radiusScale j)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m entropyAtRadius ≤
      2 * ∑ j ∈ Finset.range m,
        ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε := by
  rw [FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hstep :=
    guarded_dyadic_lowerEndpoint_mul_width_le_intervalIntegral
      (entropyAtRadius := entropyAtRadius) (j := j) hradiusScale_nonneg
      (hguard j hj) (hintervalIntegrable j hj)
  have hwidth :=
    FiniteSubGaussianProcess.dyadic_annulus_width_eq_two_mul_next
      radiusScale j
  calc
    (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))
        =
      2 * ((radiusScale / (2 : ℝ) ^ (j + 1) -
          radiusScale / (2 : ℝ) ^ (j + 2)) *
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) := by
          rw [hwidth]
          ring
    _ ≤ 2 * (∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε) := by
          exact mul_le_mul_of_nonneg_left hstep (by norm_num : 0 ≤ (2 : ℝ))

/-- Guarded finite dyadic upper sum dominated by one truncated interval.

The lower endpoint is `radiusScale / 2^(m+1)`, not zero. This is the guarded
positive-radius bridge needed before a later continuous theorem can take a
limit as the lower endpoint tends to zero. -/
theorem finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral_guarded
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hguard : ∀ j ∈ Finset.range m,
      GuardedAntitoneOnDyadicAnnulus entropyAtRadius radiusScale j)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m entropyAtRadius ≤
      2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
        entropyAtRadius ε := by
  have hupper :=
    finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum_guarded
      (m := m) (entropyAtRadius := entropyAtRadius) hradiusScale_nonneg
      hguard hintervalIntegrable
  have hsum :=
    FiniteSubGaussianProcess.shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral
      (m := m) (entropyAtRadius := entropyAtRadius) hintervalIntegrable
  simpa [hsum] using hupper

/-! ## Witness profile: locally valid, globally invalid -/

/-- A toy entropy profile that may diverge along positive radii approaching
zero, while staying real-valued at zero for Lean convenience. -/
def positiveRadiusReciprocalEntropy (ε : ℝ) : ℝ :=
  if 0 < ε then ε⁻¹ else 0

theorem positiveRadiusReciprocalEntropy_guarded
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus
      positiveRadiusReciprocalEntropy radiusScale j := by
  intro ε hleft hright
  have hright_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 1) := by
    positivity
  have hε_pos : 0 < ε := by
    have hleft_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 2) := by
      positivity
    exact lt_of_lt_of_le hleft_pos hleft
  simp [positiveRadiusReciprocalEntropy, hright_pos, hε_pos]
  simpa [one_div] using one_div_le_one_div_of_le hε_pos hright

/-- The reciprocal witness is not globally antitone on `ℝ`.

This is the concrete type-level separation from the old theorem surface:
global antitonicity would force `f 1 ≤ f 0`, but the witness has `f 1 = 1`
and `f 0 = 0`. -/
theorem not_globalAntitone_positiveRadiusReciprocalEntropy :
    ¬ Antitone positiveRadiusReciprocalEntropy := by
  intro hanti
  have hbad := hanti (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num [positiveRadiusReciprocalEntropy] at hbad

/-- The reciprocal witness is integrable on every positive dyadic annulus. -/
theorem positiveRadiusReciprocalEntropy_intervalIntegrable_dyadic
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    IntervalIntegrable positiveRadiusReciprocalEntropy MeasureTheory.volume
      (radiusScale / (2 : ℝ) ^ (j + 2))
      (radiusScale / (2 : ℝ) ^ (j + 1)) := by
  have hleft_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 2) := by
    positivity
  have hab :
      radiusScale / (2 : ℝ) ^ (j + 2) ≤
        radiusScale / (2 : ℝ) ^ (j + 1) := by
    have hwidth :=
      FiniteSubGaussianProcess.dyadic_annulus_width_nonneg
        (radiusScale := radiusScale) hradiusScale.le (j + 1)
    linarith
  have hinv :
      IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)) := by
    refine intervalIntegral.intervalIntegrable_inv
      (f := fun x : ℝ => x) ?_ continuous_id.continuousOn
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ne_of_gt (lt_of_lt_of_le hleft_pos hx.1)
  refine hinv.congr ?_
  intro x hx
  rw [Set.uIoc_of_le hab] at hx
  have hx_pos : 0 < x := lt_trans hleft_pos hx.1
  simp [positiveRadiusReciprocalEntropy, hx_pos]

/-- The reciprocal witness can still enter the guarded truncated bridge once
finite positive-annulus integrability is supplied.

This theorem records the intended stronger API shape: no global antitonicity
and no value at zero is required. -/
theorem positiveRadiusReciprocalEntropy_truncated_bridge
    {radiusScale : ℝ} (m : ℕ) (hradiusScale : 0 < radiusScale) :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum radiusScale m
        positiveRadiusReciprocalEntropy ≤
      2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
        positiveRadiusReciprocalEntropy ε := by
  exact
    finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral_guarded
      (m := m) (entropyAtRadius := positiveRadiusReciprocalEntropy)
      hradiusScale.le
      (fun j _hj => positiveRadiusReciprocalEntropy_guarded hradiusScale j)
      (fun j _hj =>
        positiveRadiusReciprocalEntropy_intervalIntegrable_dyadic hradiusScale j)

end

end FormalSLT.Covering.GuardedDudleyIntegral
