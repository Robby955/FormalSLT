import FormalSLT.TestTimeMeta.FlagshipFiveComponentAssembly
import FormalSLT.AnytimeValid.MixtureCS

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.TestTimeMeta

noncomputable section

/-! Concrete non-trivial witness for the increment-model hypotheses of
`flagshipFiveComponent_conclusion_from_incrementModel`.

Space: `Ω = Bool`, `μ = fair Bernoulli`.
Increment: a single Rademacher shock at index 0, revealed at time 1.
  `X 0 ω = if ω then 1 else -1`  (NON-zero), `X k = 0` for `k ≥ 1`.
Filtration: `ℱ 0 = ⊥` (past at time 0 sees nothing), `ℱ k = ⊤` for `k ≥ 1`.

This avoids the `condExp_of_stronglyMeasurable` collapse: `X 0` is NOT `ℱ 0 = ⊥`
measurable, so `μ[X 0 | ℱ 0] = 0` does not force `X 0 = 0`.  It holds because the
Rademacher shock has mean zero under the fair Bernoulli, and `condExp_bot` reduces
`μ[· | ⊥]` to the integral. -/

namespace RefuteWitness

/-- Fair Bernoulli measure on `Bool`. -/
def μ : Measure Bool := (1/2 : ENNReal) • Measure.dirac false + (1/2 : ENNReal) • Measure.dirac true

instance : IsProbabilityMeasure μ := by
  constructor
  simp only [μ, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    Measure.dirac_apply', MeasurableSet.univ, Set.indicator_of_mem, Set.mem_univ,
    smul_eq_mul]
  norm_num
  exact ENNReal.inv_two_add_inv_two

/-- The single Rademacher increment process. -/
def Xproc : ℕ → Bool → ℝ := fun k ω => if k = 0 then (if ω then 1 else -1) else 0

/-- Filtration: `⊥` at time 0, `⊤` afterwards. -/
def ℱ : Filtration ℕ (inferInstance : MeasurableSpace Bool) where
  seq := fun k => if k = 0 then (⊥ : MeasurableSpace Bool) else (⊤ : MeasurableSpace Bool)
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj, if_true]
        exact bot_le
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  le' := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, if_true]; exact bot_le
    · simp only [hk]
      exact le_top

/-- The Rademacher shock is genuinely non-constant: `X 0 true = 1 ≠ -1 = X 0 false`. -/
example : Xproc 0 true ≠ Xproc 0 false := by simp only [Xproc]; norm_num

/-- `ℱ 0 = ⊥`. -/
theorem seq_zero : (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Bool)) 0 = ⊥ := rfl

/-- `ℱ (k+1) = ⊤`. -/
theorem seq_succ (k : ℕ) :
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Bool)) (k + 1) = ⊤ := by
  show (if k + 1 = 0 then (⊥ : MeasurableSpace Bool) else ⊤) = ⊤
  simp

/-- (1) Each `X k` is measurable (Bool is discrete). -/
theorem hX_meas : ∀ k, Measurable (Xproc k) := fun _ => by measurability

/-- Pointwise bound `|X k ω| ≤ 1`. -/
theorem Xproc_abs_le (k : ℕ) (ω : Bool) : |Xproc k ω| ≤ (1 : ℝ) := by
  simp only [Xproc]
  by_cases hk : k = 0
  · rw [if_pos hk]; cases ω <;> norm_num
  · rw [if_neg hk]; norm_num

/-- (5) Each `|X k| ≤ b = 1`. -/
theorem hbound : ∀ k, ∀ᵐ ω ∂μ, |Xproc k ω| ≤ (1 : ℝ) :=
  fun k => Filter.Eventually.of_forall (fun ω => Xproc_abs_le k ω)

/-- (2) Each `X k` is integrable (bounded on a probability space). -/
theorem hX_int : ∀ k, Integrable (Xproc k) μ :=
  fun k => (integrable_const (1 : ℝ)).mono' (hX_meas k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact Xproc_abs_le k ω))

/-- `IncrementAdapted ℱ Xproc`: each `X k` is `ℱ (k+1)`-measurable, since `ℱ (k+1) = ⊤`. -/
theorem incrementAdapted_Xproc : IncrementAdapted ℱ Xproc := by
  intro k
  rw [seq_succ k]
  exact (measurable_from_top (f := Xproc k)).stronglyMeasurable

/-- (3) The running-sum exponential process is `ℱ`-adapted via the increment shift. -/
theorem h_adapted :
    StronglyAdapted ℱ (subGammaExponentialProcess Xproc 1 1 1) :=
  stronglyAdapted_subGammaExponentialProcess_of_adapted 1 1 1 incrementAdapted_Xproc

/-- (4) Each `subGammaExponentialProcess` term is integrable: `Bool` is finite, so any
function is integrable under the finite measure `μ`. -/
theorem h_integrable :
    ∀ k, Integrable (subGammaExponentialProcess Xproc 1 1 1 k) μ :=
  fun _ => Integrable.of_finite

/-- (6) Conditional centering `μ[X k | ℱ k] =ᵐ 0`.  For `k = 0` this is `condExp_bot`
applied to the mean-zero Rademacher shock; for `k ≥ 1` it is `condExp_zero`. -/
theorem hcenter : ∀ k, μ[Xproc k | (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Bool)) k]
    =ᵐ[μ] 0 := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [seq_zero, condExp_bot]
    refine Filter.Eventually.of_forall (fun _ => ?_)
    show ∫ ω, Xproc 0 ω ∂μ = 0
    rw [μ, integral_add_measure (Integrable.of_finite.smul_measure (by simp))
        (Integrable.of_finite.smul_measure (by simp)),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp only [Xproc, if_true, if_false, Bool.false_eq_true]
    rw [show (1 / 2 : ENNReal).toReal = (1 / 2 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num]
    norm_num
  · have hzero : Xproc k = 0 := by
      funext ω; simp only [Xproc]; rw [if_neg (by omega)]; rfl
    rw [hzero, condExp_zero]

/-- (7) Conditional second moment `μ[X k² | ℱ k] ≤ σ² = 1`.  For `k = 0`, `X 0² = 1`
constant; for `k ≥ 1`, `X k² = 0 ≤ 1`. -/
theorem hvar : ∀ k, μ[fun ω => (Xproc k ω) ^ 2
    | (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Bool)) k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
  intro k
  have hsq : (fun ω => (Xproc k ω) ^ 2) = (fun _ => if k = 0 then (1 : ℝ) else 0) := by
    funext ω; simp only [Xproc]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]; cases ω <;> norm_num
    · rw [if_neg hk, if_neg hk]; norm_num
  rw [hsq]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [if_true]
    rw [condExp_const (le_top)]
  · rw [if_neg (by omega)]
    have : ((fun _ : Bool => (0 : ℝ))) = 0 := rfl
    rw [this, condExp_zero]
    exact Filter.Eventually.of_forall (fun _ => by norm_num)

/-- The DECISIVE non-vacuity witness: the full five-component flagship conclusion holds
for the NON-zero Rademacher increment process, fair Bernoulli measure, and the
`⊥`/`⊤` filtration, with rational parameters `b = σ² = lam = 1`. -/
theorem nonvacuous_witness (n : ℕ) (t : ℝ) (hn : 0 < n) :
    FlagshipFiveComponentConclusion
      (flagshipFiveComponent_certificate_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := Xproc) (sigma2 := 1) (b := 1)
        (lam := 1) (t := t) (n := n)
        hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)
      μ Xproc 1 1 1 t n :=
  flagshipFiveComponent_conclusion_from_incrementModel
    (μ := μ) (ℱ := ℱ) (X := Xproc) (sigma2 := 1) (b := 1)
    (lam := 1) (t := t) (n := n)
    hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

/-- The witnessed process is genuinely non-zero (NOT the collapsed trivial instance). -/
theorem Xproc_nonzero : Xproc ≠ (fun _ _ => (0 : ℝ)) := by
  intro h
  have : Xproc 0 true = 0 := by rw [h]
  simp only [Xproc] at this
  norm_num at this

#print axioms nonvacuous_witness
#print axioms Xproc_nonzero
#print axioms hcenter
#print axioms incrementAdapted_Xproc

end RefuteWitness
