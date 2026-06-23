/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.OptimizedLambdaCS

/-!
# Non-vacuity witness for the optimized-`lambda` iterated-log confidence sequence

This file instantiates `optimized_lambda_confidence_sequence_subGamma` with a genuine
nonzero increment process, proving the optimized-`lambda` (stitched-grid) bound is not
vacuous, and exhibits the iterated-log width on concrete numeric data.

The witness is a Rademacher (sign) increment on `Ω = Bool` under the uniform
probability measure: `X 0 ω = if ω then 1 else -1` (so `X 0` takes the values
`±1`, never zero), with `X k = 0` for `k ≥ 1`. The filtration reveals the first
increment one step late: `ℱ 0 = ⊥`, `ℱ k = ⊤` for `k ≥ 1`. This is the
predictable-increment (martingale-difference) model required by
`IncrementAdapted ℱ X`: each `X k` is `ℱ (k+1)`-measurable while remaining
conditionally centered with respect to the past, `μ[X k | ℱ k] = 0`.

Under the earlier present-conditioning `StronglyAdapted ℱ X` requirement, pairing
adaptedness with `μ[X k | ℱ k] = 0` forces `X k =ᵐ 0` (by
`condExp_of_stronglyMeasurable`), leaving only the zero process, which makes the
crossing event empty (the `atTopSubGammaUpperFailure_zero_process_empty` trap). The
`+1` shift in `IncrementAdapted` admits the genuine `±1` increment here.

The instance uses `b = 1`, `sigma2 = 1`, `delta = 1/2`, and a genuine two-element
tilt grid `Lam = {1/2, 1}` (both in `(0, 3/b) = (0, 3)`), yielding the concrete
optimized-`lambda` coverage bound `... ≤ 1/2`. The iterated-log width
`subGammaLogLogWidth 1 1 16 (1/2)` is shown strictly positive and finite via
`subGammaLogLogWidth_loglog_rate`, so the rate is witnessed on real numeric data,
not by `#check`.

The printed axiom set is exactly `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped ENNReal BigOperators

noncomputable section

namespace FormalSLT.AnytimeValid.OptimizedLambdaWitness

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

/-- The genuine two-element tilt grid `{1/2, 1}`, both admissible in `(0, 3/b) = (0, 3)`. -/
def LamGrid : Finset ℝ := {1 / 2, 1}

theorem LamGrid_nonempty : LamGrid.Nonempty := by
  refine ⟨1, ?_⟩; simp [LamGrid]

theorem LamGrid_card : LamGrid.card = 2 := by
  rw [LamGrid, Finset.card_pair (by norm_num)]

theorem LamGrid_mem : ∀ lam ∈ LamGrid, lam ∈ Set.Ioo (0 : ℝ) (3 / 1) := by
  intro lam hlam
  simp only [LamGrid, Finset.mem_insert, Finset.mem_singleton] at hlam
  rcases hlam with h | h <;> subst h <;> constructor <;> norm_num

/-- The increment process is genuinely non-zero. -/
example : XBool 0 true = 1 := by simp [XBool]
example : XBool 0 false = -1 := by simp [XBool]

/-- Integrability of each fixed-tilt exponential process (everything on `Bool` is
integrable under the finite `μBool`). -/
theorem proc_integrable (sigma2 b lam : ℝ) (n : ℕ) :
    Integrable (subGammaExponentialProcess XBool sigma2 b lam n) μBool := by
  haveI : IsFiniteMeasure μBool := inferInstance
  exact Integrable.of_finite

/--
**Witnessed optimized-`lambda` coverage bound.** Instantiation of
`optimized_lambda_confidence_sequence_subGamma` on the Rademacher `±1` increment with
the genuine two-element tilt grid `{1/2, 1}`: the centered running mean crosses the
optimized (best-of-grid) stitched boundary only on an event of mass at most `1/2`.
-/
theorem witnessOptimizedLambdaCS :
    (μBool).real {ω | ∃ n : ℕ, 0 < n ∧
        (∃ lam ∈ LamGrid, subGammaCgf 1 1 lam / lam
            + Real.log ((LamGrid.card : ℝ) / (1 / 2)) / ((n : ℝ) * lam)
              ≤ runningMean XBool n ω)} ≤ (1 / 2 : ℝ) := by
  refine optimized_lambda_confidence_sequence_subGamma
    (μ := μBool) (ℱ := filtBool) (X := XBool)
    (sigma2 := 1) (b := 1) (delta := 1 / 2) (Lam := LamGrid)
    (by norm_num) (by norm_num) (by norm_num) LamGrid_nonempty ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hLam_mem
    intro lam hlam
    have := LamGrid_mem lam hlam
    simpa using this
  · -- hX_meas
    intro k; exact measurable_from_top
  · -- hX_int
    intro k; exact Integrable.of_finite
  · -- hX_adapted : IncrementAdapted filtBool XBool
    intro k
    have : filtBool (k + 1) = ⊤ := by simp [filtBool]
    rw [show (StronglyMeasurable[filtBool (k + 1)] (XBool k)) =
        (StronglyMeasurable[⊤] (XBool k)) from by rw [this]]
    exact (measurable_from_top).stronglyMeasurable
  · -- h_integrable
    intro lam _ n; exact proc_integrable 1 1 lam n
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
      rw [hint]; rfl
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

/-- The discharged increment-model obligations for the Rademacher witness, reused by both the
one-sided and the two-sided endpoints: bound, conditional centering, conditional second moment. -/
theorem witness_hbound : ∀ k, ∀ᵐ ω ∂μBool, |XBool k ω| ≤ (1 : ℝ) := by
  intro k
  refine Filter.Eventually.of_forall ?_
  intro ω
  simp only [XBool]
  by_cases hk : k = 0
  · subst hk; cases ω <;> norm_num
  · simp only [if_neg hk]; norm_num

theorem witness_hcenter : ∀ k, μBool[XBool k | filtBool k] =ᵐ[μBool] 0 := by
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
    rw [hint]; rfl
  · have hXk : XBool k = 0 := by funext ω; simp only [XBool, if_neg hk]; rfl
    rw [hXk, condExp_zero]

theorem witness_hvar :
    ∀ k, μBool[fun ω => (XBool k ω) ^ 2 | filtBool k] ≤ᵐ[μBool] fun _ => (1 : ℝ) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    have hsq : (fun ω => (XBool 0 ω) ^ 2) = (fun _ : Bool => (1 : ℝ)) := by
      funext ω; simp only [XBool]; cases ω <;> norm_num
    rw [hsq, condExp_const (filtBool.le 0)]
  · have hXk : XBool k = 0 := by funext ω; simp only [XBool, if_neg hk]; rfl
    have hsq : (fun ω => (XBool k ω) ^ 2) = (0 : Bool → ℝ) := by funext ω; rw [hXk]; simp
    rw [hsq, condExp_zero]
    exact Filter.Eventually.of_forall (by intro ω; norm_num)

theorem witness_hadapted : IncrementAdapted filtBool XBool := by
  intro k
  have : filtBool (k + 1) = ⊤ := by simp [filtBool]
  rw [show (StronglyMeasurable[filtBool (k + 1)] (XBool k)) =
      (StronglyMeasurable[⊤] (XBool k)) from by rw [this]]
  exact (measurable_from_top).stronglyMeasurable

/--
**Witnessed two-sided optimized-`lambda` coverage bound.** Instantiation of
`optimized_lambda_two_sided_confidence_sequence` on the genuine Rademacher `±1` increment with
the two-element tilt grid `{1/2, 1}`: the centered running mean crosses the optimized (best-of-grid)
stitched boundary on *either* side only on an event of mass at most `1/2`. This is the genuine
two-sided interval-width non-vacuity witness — the failure event involves `|runningMean|`, and the
process is the nonzero `±1` Rademacher increment (`IncrementAdapted`), not a zero process. -/
theorem witnessOptimizedLambdaTwoSidedCS :
    (μBool).real {ω | ∃ n : ℕ, 0 < n ∧
        (∃ lam ∈ LamGrid, subGammaCgf 1 1 lam / lam
            + Real.log ((LamGrid.card : ℝ) / ((1 / 2) / 2)) / ((n : ℝ) * lam)
              ≤ |runningMean XBool n ω|)} ≤ (1 / 2 : ℝ) := by
  refine optimized_lambda_two_sided_confidence_sequence
    (μ := μBool) (ℱ := filtBool) (X := XBool)
    (sigma2 := 1) (b := 1) (delta := 1 / 2) (Lam := LamGrid)
    (by norm_num) (by norm_num) (by norm_num) LamGrid_nonempty ?_ ?_ ?_
    witness_hadapted ?_ ?_ witness_hbound witness_hcenter witness_hvar
  · -- hLam_mem
    intro lam hlam; have := LamGrid_mem lam hlam; simpa using this
  · -- hX_meas
    intro k; exact measurable_from_top
  · -- hX_int
    intro k; exact Integrable.of_finite
  · -- h_integrable
    intro lam _ n; exact proc_integrable 1 1 lam n
  · -- h_integrable_neg
    intro lam _ n
    haveI : IsFiniteMeasure μBool := inferInstance
    exact Integrable.of_finite

/-- The iterated-log width is strictly positive and finite at the concrete numeric
parameters `sigma2 = 1`, `b = 1`, `n = 16` (`16 > e^e`), `delta = 1/2`. This is the
genuine numeric rate witness, not a `#check`. -/
theorem witnessLogLogWidth_pos : 0 < subGammaLogLogWidth 1 1 16 (1 / 2) :=
  subGammaLogLogWidth_loglog_rate.1

/-- A concrete numeric `≤` bound on the iterated-log width: it equals its explicit
closed form `sqrt (2 * (log log 16 + log 2) / 16) + (log log 16 + log 2) / 48`. -/
theorem witnessLogLogWidth_closed_form :
    subGammaLogLogWidth 1 1 16 (1 / 2)
      = Real.sqrt (2 * (logLogBudget 16 (1 / 2)) / 16)
        + (logLogBudget 16 (1 / 2)) / 48 :=
  subGammaLogLogWidth_loglog_rate.2

#print axioms witnessOptimizedLambdaCS
#print axioms witnessOptimizedLambdaTwoSidedCS
#print axioms witnessLogLogWidth_pos
#print axioms subGamma_stitched_boundary_supermartingale
#print axioms optimized_lambda_confidence_sequence_subGamma
#print axioms subGammaLogLogWidth_loglog_rate
#print axioms subGammaLogLogWidth_le_boundary
#print axioms subGammaLogLogWidth_eq_boundary_optTilt
#print axioms optimized_lambda_two_sided_confidence_sequence
#print axioms optimized_lambda_two_sided_closed_form_pointwise

end FormalSLT.AnytimeValid.OptimizedLambdaWitness

end
