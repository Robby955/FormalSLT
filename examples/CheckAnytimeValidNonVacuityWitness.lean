/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.MixtureCS

/-!
# Non-vacuity witness for the mixture confidence sequence

This file instantiates `mixture_confidence_sequence_uniformPrior` with a genuine
nonzero increment process, proving the headline anytime-valid bound is not vacuous.

The witness is a Rademacher (sign) increment on `Ω = Bool` under the uniform
probability measure: `X 0 ω = if ω then 1 else -1` (so `X 0` takes the values
`±1`, never zero), with `X k = 0` for `k ≥ 1`. The filtration reveals the first
increment one step late: `ℱ 0 = ⊥`, `ℱ k = ⊤` for `k ≥ 1`. This is the
predictable-increment (martingale-difference) model required by
`IncrementAdapted ℱ X`: each `X k` is `ℱ (k+1)`-measurable while remaining
conditionally centered with respect to the past, `μ[X k | ℱ k] = 0`.

This is the point of the corrected hypothesis. Under the earlier
`StronglyAdapted ℱ X` (present-conditioning) requirement, pairing adaptedness with
`μ[X k | ℱ k] = 0` forces `X k =ᵐ 0` by `condExp_of_stronglyMeasurable`, so the
only admissible process was the zero process and the bound was vacuous. The `+1`
shift in `IncrementAdapted` admits the genuine `±1` increment here.

The instance uses `b = 1`, `sigma2 = 1`, `delta = 1/2`, `lam0 = 1/2`, `lam1 = 1`
(so `lam1 = 1 < 3 / b = 3`), and yields the concrete bound
`μ.real {ω | ∃ n > 0, 2 ≤ M_n ω} ≤ 1/2`.

The printed axiom set is exactly `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped ENNReal

noncomputable section

namespace FormalSLT.AnytimeValid.NonVacuityWitness

/-- Uniform probability measure on `Bool`. -/
def μBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure μBool := by
  refine ⟨?_⟩
  simp only [μBool, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.add_halves 1

/-- The Rademacher (sign) increment process: `X 0 = ±1`, later increments zero. -/
def XBool : ℕ → Bool → ℝ :=
  fun k ω => if k = 0 then (if ω then (1 : ℝ) else -1) else 0

/-- The two-level filtration: `ℱ 0 = ⊥`, `ℱ k = ⊤` for `k ≥ 1`. -/
def filtBool : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq := fun k => if k = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj]; exact bot_le
    · have hj : j ≠ 0 := by
        rintro rfl; exact hi (Nat.le_zero.mp hij)
      simp [hi, hj]
  le' := by
    intro i
    by_cases hi : i = 0
    · simp only [hi]; exact bot_le
    · simp [hi]

theorem nonVacuityWitness :
    (μBool).real {ω | ∃ n : ℕ, 0 < n ∧
        (1 / (1 / 2 : ℝ)) ≤
          mixtureExponentialProcess XBool 1 1 (uniformTiltPrior (1 / 2) 1) n ω}
      ≤ (1 / 2 : ℝ) := by
  refine mixture_confidence_sequence_uniformPrior
    (μ := μBool) (ℱ := filtBool) (X := XBool)
    (sigma2 := 1) (b := 1) (delta := 1 / 2) (lam0 := 1 / 2) (lam1 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · -- hX_meas
    intro k
    exact measurable_from_top
  · -- hX_int
    intro k
    exact Integrable.of_finite
  · -- hX_adapted : IncrementAdapted filtBool XBool
    intro k
    have : filtBool (k + 1) = ⊤ := by
      simp [filtBool]
    rw [show (StronglyMeasurable[filtBool (k + 1)] (XBool k)) =
        (StronglyMeasurable[⊤] (XBool k)) from by rw [this]]
    exact (measurable_from_top).stronglyMeasurable
  · -- hbound
    intro k
    refine Filter.Eventually.of_forall ?_
    intro ω
    simp only [XBool]
    by_cases hk : k = 0
    · subst hk; cases ω <;> norm_num
    · simp only [if_neg hk]; norm_num
  · -- hcenter
    intro k
    by_cases hk : k = 0
    · subst hk
      have hℱ0 : filtBool 0 = ⊥ := by simp [filtBool]
      rw [hℱ0, condExp_bot]
      have hint : ∫ x, XBool 0 x ∂μBool = 0 := by
        haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (true : Bool)) :=
          Measure.smul_finite _ (by norm_num)
        haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (false : Bool)) :=
          Measure.smul_finite _ (by norm_num)
        rw [μBool, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
          integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
        simp only [XBool, smul_eq_mul]
        norm_num
      rw [hint]
      rfl
    · have hXk : XBool k = 0 := by
        funext ω; simp only [XBool, if_neg hk]; rfl
      rw [hXk, condExp_zero]
  · -- hvar
    intro k
    by_cases hk : k = 0
    · subst hk
      have hsq : (fun ω => (XBool 0 ω) ^ 2) = (fun _ : Bool => (1 : ℝ)) := by
        funext ω; simp only [XBool]; cases ω <;> norm_num
      rw [hsq, condExp_const (filtBool.le 0)]
    · have hXk : XBool k = 0 := by
        funext ω; simp only [XBool, if_neg hk]; rfl
      have hsq : (fun ω => (XBool k ω) ^ 2) = (0 : Bool → ℝ) := by
        funext ω; rw [hXk]; simp
      rw [hsq, condExp_zero]
      exact Filter.Eventually.of_forall (by intro ω; norm_num)

#print axioms nonVacuityWitness

end FormalSLT.AnytimeValid.NonVacuityWitness
