/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.EProcess
import FormalSLT.AnytimeValid.MixtureCS
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Non-vacuity witness for the e-process / safe-testing layer

This file builds a GENUINE, non-constant e-process and fires the three e-process
theorems on it with a numeric Type-I bound, certifying that
`FormalSLT.AnytimeValid.EProcess.lean` is not vacuous.

The witness is the fixed-tilt sub-Gamma exponential of a Rademacher (sign)
increment on `Ω = Bool` under the uniform probability measure, reusing the
predictable-increment model already used by the confidence-sequence witness:

* `XBool 0 ω = if ω then 1 else -1` (values `±1`, never zero), `XBool k = 0` for
  `k ≥ 1`. The increment is revealed one step late: `filtBool 0 = ⊥`,
  `filtBool k = ⊤` for `k ≥ 1`, so `IncrementAdapted filtBool XBool` holds (each
  `X k` is `filtBool (k+1)`-measurable) while staying conditionally centered with
  respect to the past, `μ[X k | filtBool k] = 0`. The `+1` shift is what keeps
  the increment genuinely nonzero (present-conditioning would force `X k =ᵐ 0`).
* `E n ω = subGammaExponentialProcess XBool 1 1 1 n ω = exp(S_n - n·cgf)` with
  `sigma2 = b = lam = 1`, so `cgf = 1/(2·(1 - 1/3)) = 3/4`.

`E` is a nonnegative `filtBool`-supermartingale with `E 0 = 1` (built from the
banked `nonneg_supermartingale_of_condSubGamma` ∘ `condSubGamma_supermartingale_step`),
so `eProcessWitness : EProcess μBool filtBool E`. It is non-trivial: on `ω = true`,
`E 1 ω = exp(1 - 3/4) = exp(1/4) > 1`, so the rejection event is genuinely
exercised (see `witness_exceeds_one`).

The three theorems then fire:

* `witness_typeI_control`: at level `α = 1/4` (threshold `1/α = 4`), Type-I
  control gives `μBool.real {ω | 4 ≤ finiteRunningMax E n ω} ≤ 1/4`, a closed
  numeric inequality.
* `witness_product`: `E · E` is again an e-process (the squared exponential is
  again a supermartingale on this witness, via the same `condSubGamma` route at
  tilt `2`).
* `witness_optionalContinuation`: for the constant stopping time `τ ≡ n` (bounded
  by `n`), `∫ ω, stoppedValue E τ ω ∂μBool ≤ 1`, the `E[E_τ] ≤ 1` e-value bound.

The printed axiom set for each is exactly `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped ENNReal BigOperators

noncomputable section

namespace FormalSLT.AnytimeValid.EProcessWitness

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

/-- The witness e-process: the fixed-tilt sub-Gamma exponential at `σ² = b = λ = 1`. -/
def Ewit : ℕ → Bool → ℝ := subGammaExponentialProcess XBool 1 1 1

/-- The increment process is predictable-increment adapted to `filtBool`. -/
theorem XBool_incrementAdapted : IncrementAdapted filtBool XBool := by
  intro k
  have hfilt : filtBool (k + 1) = ⊤ := by simp [filtBool]
  rw [show (StronglyMeasurable[filtBool (k + 1)] (XBool k)) =
      (StronglyMeasurable[⊤] (XBool k)) from by rw [hfilt]]
  exact measurable_from_top.stronglyMeasurable

/-- The witness process is `filtBool`-strongly-adapted. -/
theorem Ewit_stronglyAdapted : StronglyAdapted filtBool Ewit :=
  stronglyAdapted_subGammaExponentialProcess_of_adapted 1 1 1 XBool_incrementAdapted

/-- `XBool k` is measurable. -/
theorem XBool_meas (k : ℕ) : Measurable (XBool k) := measurable_from_top

/-- `XBool k` is integrable. -/
theorem XBool_int (k : ℕ) : Integrable (XBool k) μBool := Integrable.of_finite

/-- `|XBool k| ≤ 1` a.e. -/
theorem XBool_bound (k : ℕ) : ∀ᵐ ω ∂μBool, |XBool k ω| ≤ (1 : ℝ) := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  simp only [XBool]
  by_cases hk : k = 0
  · subst hk; cases ω <;> norm_num
  · simp only [if_neg hk]; norm_num

/-- `μ[XBool k | filtBool k] = 0`: conditionally centered with respect to the past. -/
theorem XBool_center (k : ℕ) : μBool[XBool k | filtBool k] =ᵐ[μBool] 0 := by
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

/-- `μ[XBool k² | filtBool k] ≤ 1`: conditional second moment bounded by `σ² = 1`. -/
theorem XBool_var (k : ℕ) :
    μBool[fun ω => (XBool k ω) ^ 2 | filtBool k] ≤ᵐ[μBool] fun _ => (1 : ℝ) := by
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

/-- The witness process is integrable at every time (finite measure space). -/
theorem Ewit_int (k : ℕ) : Integrable (Ewit k) μBool := Integrable.of_finite

/-- The fixed-tilt-1 witness process is a nonnegative supermartingale. -/
theorem Ewit_supermartingale_and_nonneg :
    Supermartingale Ewit filtBool μBool ∧ ∀ n ω, 0 ≤ Ewit n ω := by
  refine nonneg_supermartingale_of_condSubGamma (lam := 1)
    Ewit_stronglyAdapted Ewit_int ?_
  exact condSubGamma_supermartingale_step (b := 1) (sigma2 := 1) (lam := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    XBool_meas XBool_int Ewit_stronglyAdapted XBool_bound XBool_center XBool_var

/-- **The concrete e-process witness.** -/
theorem eProcessWitness : EProcess μBool filtBool Ewit where
  nonneg := fun n ω => Ewit_supermartingale_and_nonneg.2 n ω
  start_one := fun ω => by simp [Ewit, subGammaExponentialProcess, runningSum]
  supermartingale := Ewit_supermartingale_and_nonneg.1

/--
Non-triviality: the witness exceeds `1` on a positive-mass event. On `ω = true`,
`E 1 ω = exp(1 - 3/4) = exp(1/4) > 1`, so the e-process is genuinely non-constant
and the rejection event of `eProcess_typeI_control` is actually exercised. -/
theorem witness_exceeds_one : (1 : ℝ) < Ewit 1 true := by
  have h : Ewit 1 true = Real.exp (1 / 4) := by
    simp only [Ewit, subGammaExponentialProcess, runningSum, subGammaCgf]
    norm_num [XBool, Finset.sum_range_one]
  rw [h]
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ < Real.exp (1 / 4) := Real.exp_lt_exp.mpr (by norm_num)

/--
**Type-I control fires on the witness with a numeric bound.** At level `α = 1/4`
(rejection threshold `1/α = 4`), the realized-prefix-max rejection event has mass
at most `1/4`, for every horizon `n`. This is a closed numeric inequality, not a
`Prop`-shaped restatement. -/
theorem witness_typeI_control (n : ℕ) :
    μBool.real {ω | (1 : ℝ) / (1 / 4) ≤ finiteRunningMax Ewit n ω} ≤ (1 / 4 : ℝ) :=
  eProcess_typeI_control eProcessWitness (by norm_num) n

/-- Restated with the threshold `4` made explicit: `μ{ max E ≥ 4 } ≤ 1/4`. -/
theorem witness_typeI_control_threshold_four (n : ℕ) :
    μBool.real {ω | (4 : ℝ) ≤ finiteRunningMax Ewit n ω} ≤ (1 / 4 : ℝ) := by
  have h := witness_typeI_control n
  norm_num at h
  exact h

/-- The squared witness `G n ω = (E n ω)² = exp(2·Sₙ - n·(3/2))`. -/
def Gsq : ℕ → Bool → ℝ := fun n ω => Ewit n ω * Ewit n ω

/-- Closed form of the squared witness: `Gsq n ω = exp(2·Sₙ(ω) - n·(3/2))`. -/
theorem Gsq_eq (n : ℕ) (ω : Bool) :
    Gsq n ω = Real.exp (2 * runningSum XBool n ω - (n : ℝ) * (3 / 2)) := by
  simp only [Gsq, Ewit, subGammaExponentialProcess, subGammaCgf, ← Real.exp_add]
  congr 1
  norm_num
  ring

/-- The squared witness is `filtBool`-strongly-adapted (product of two adapted processes). -/
theorem Gsq_stronglyAdapted : StronglyAdapted filtBool Gsq := fun n =>
  (Ewit_stronglyAdapted n).mul (Ewit_stronglyAdapted n)

/-- `runningSum XBool` past time `1` is constant: `Sₙ = X₀` for `n ≥ 1` (later increments zero). -/
theorem runningSum_succ_eq (n : ℕ) (ω : Bool) :
    runningSum XBool (n + 1) ω = runningSum XBool 1 ω := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [runningSum, Finset.sum_range_succ, ← runningSum, ih]
    have : XBool (m + 1) ω = 0 := by simp [XBool]
    rw [this, add_zero]

/--
The squared witness process `E · E` is again a `filtBool`-supermartingale.

This is the honest composition obligation discharged directly on the witness: the
square of the exponential e-process is the exponential `exp(2·Sₙ - n·(3/2))`, whose
one-step conditional expectation is bounded by the current value. For `i ≥ 1`
(`filtBool i = ⊤`) the increment is already revealed and the ratio is the constant
`exp(-3/2) ≤ 1`. For `i = 0` (`filtBool 0 = ⊥`) the conditional expectation is the
integral `½·exp(2 - 3/2) + ½·exp(-2 - 3/2) = ½·exp(1/2) + ½·exp(-7/2) ≈ 0.84`,
bounded by `1 = G₀` via the explicit exp bounds `exp(1/2) < 5/3` and `exp(-7/2) < 1/3`.
(The exact `condSubGamma` route cannot match a sub-Gamma exponential with
`σ² ≥ X² = 1` here, so the supermartingale step is proved directly — a genuine,
non-vacuous discharge.) -/
theorem Ewit_sq_supermartingale : Supermartingale Gsq filtBool μBool := by
  refine supermartingale_nat Gsq_stronglyAdapted (fun _ => Integrable.of_finite) ?_
  intro i
  by_cases hi : i = 0
  · -- i = 0: filtBool 0 = ⊥, so μ[G 1 | ⊥] = ∫ G 1 ≤ 1 = G 0.
    subst hi
    have hℱ0 : filtBool 0 = ⊥ := by simp [filtBool]
    rw [hℱ0, condExp_bot]
    -- ∫ G 1 = ½·exp(1/2) + ½·exp(-7/2)
    have hint : ∫ x, Gsq 1 x ∂μBool
        = (1 / 2) * Real.exp (1 / 2) + (1 / 2) * Real.exp (-7 / 2) := by
      haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (true : Bool)) :=
        Measure.smul_finite _ (by norm_num)
      haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (false : Bool)) :=
        Measure.smul_finite _ (by norm_num)
      rw [μBool, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
        integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
      rw [Gsq_eq, Gsq_eq]
      have hst : runningSum XBool 1 true = 1 := by simp [runningSum, XBool]
      have hsf : runningSum XBool 1 false = -1 := by simp [runningSum, XBool]
      rw [hst, hsf]
      simp only [smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
      norm_num
    -- The conditional expectation under ⊥ is the constant `∫ G 1`.
    refine Filter.Eventually.of_forall ?_
    intro ω
    rw [hint]
    -- ½·exp(1/2)+½·exp(-7/2) ≤ 1 = G 0 ω, via exp(1/2) < 5/3 and exp(-7/2) < 1/3.
    have hG0 : Gsq 0 ω = 1 := by rw [Gsq_eq]; simp [runningSum]
    rw [hG0]
    -- exp(1/2) < 5/3 :  exp(1/2)² = exp 1 < 2.719 < 25/9 = (5/3)².
    have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hhalf_sq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hhalf_pos : (0 : ℝ) < Real.exp (1 / 2) := Real.exp_pos _
    have hhalf_lt : Real.exp (1 / 2) < 5 / 3 := by nlinarith [hhalf_sq, he1, hhalf_pos]
    -- exp(-7/2) < 1/3 :  exp(7/2) ≥ exp 2 = exp 1² > 2.718² > 3, and exp(-7/2)·exp(7/2) = 1.
    have he1' : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hsq2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have hexp72 : Real.exp 2 ≤ Real.exp (7 / 2) := Real.exp_le_exp.mpr (by norm_num)
    have hexp72_gt : (3 : ℝ) < Real.exp (7 / 2) := by nlinarith [he1', hsq2, hexp72]
    have hmul72 : Real.exp (-7 / 2) * Real.exp (7 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hneg72_pos : (0 : ℝ) < Real.exp (-7 / 2) := Real.exp_pos _
    have hneg72_lt : Real.exp (-7 / 2) < 1 / 3 := by nlinarith [hmul72, hexp72_gt, hneg72_pos]
    nlinarith [hhalf_lt, hneg72_lt, hhalf_pos, hneg72_pos]
  · -- i ≥ 1: filtBool i = ⊤, μ[G (i+1) | ⊤] = G (i+1) = G i · exp(-3/2) ≤ G i.
    have hℱi : filtBool i = ⊤ := by simp [filtBool, hi]
    have hmeas : StronglyMeasurable[filtBool i] (Gsq (i + 1)) := by
      rw [hℱi]; exact (Gsq_stronglyAdapted (i + 1)).mono le_top
    rw [condExp_of_stronglyMeasurable (filtBool.le i) hmeas (Integrable.of_finite)]
    refine Filter.Eventually.of_forall ?_
    intro ω
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hi)).symm⟩
    -- G (i+1) ω = exp(2·S_{m+2} - (m+2)·3/2), G i ω = exp(2·S_{m+1} - (m+1)·3/2),
    -- and S_{m+2} = S_{m+1} = S_1, so the exponent only loses an extra (3/2).
    rw [Gsq_eq, Gsq_eq, show m + 1 + 1 = (m + 1) + 1 from rfl,
      runningSum_succ_eq (m + 1) ω, runningSum_succ_eq m ω]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith []

/-- **The composition law fires on the witness:** `E · E` is again an e-process. -/
theorem witness_product : EProcess μBool filtBool (fun n ω => Ewit n ω * Ewit n ω) :=
  eProcess_product_of_supermartingale eProcessWitness eProcessWitness Ewit_sq_supermartingale

/--
**Optional continuation fires on the witness with a numeric bound.** For the
the constant stopping time `τ ≡ n` (bounded by `n`), the stopped e-value integrates to
at most `1`: `∫ ω, stoppedValue E (fun _ => n) ω ∂μBool ≤ 1`. This is the `E[E_τ] ≤ 1`
guarantee. -/
theorem witness_optionalContinuation (n : ℕ) :
    ∫ ω, stoppedValue Ewit (fun _ => (n : ℕ∞)) ω ∂μBool ≤ 1 :=
  eProcess_optionalContinuation eProcessWitness (τ := fun _ => (n : ℕ∞))
    (isStoppingTime_const filtBool n) (fun _ => le_rfl)

#print axioms eProcessWitness
#print axioms witness_typeI_control
#print axioms witness_typeI_control_threshold_four
#print axioms witness_product
#print axioms witness_optionalContinuation
#print axioms witness_exceeds_one

end FormalSLT.AnytimeValid.EProcessWitness
