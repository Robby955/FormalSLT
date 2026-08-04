import FormalSLT.AnytimeValid.AtTopCS
import FormalSLT.AnytimeValid.MixtureCS

/-!
Scratch concrete non-trivial witness for
`atTop_time_uniform_confidence_sequence_subGamma`.

Space: `Ω = Bool`, measure `μ = (1/2) δ_true + (1/2) δ_false` (fair coin).
Increment process: a single non-zero centered coin at time 0,
`X 0 ω = if ω then b else -b`, `X k = 0` for `k ≥ 1`.
Filtration: `ℱ 0 = ⊥` (trivial, does not see `X 0`), `ℱ k = ⊤` for `k ≥ 1`.

This avoids the collapse trap: `X 0` is NOT `ℱ 0`-measurable, so
`μ[X 0 | ℱ 0] = μ[X 0 | ⊥] = ∫ X 0 = 0` is genuine centering of a non-zero
increment, while the running sum is `ℱ n`-measurable for all `n`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped ENNReal

noncomputable section

namespace WitnessAtTopCS

/-- Fair-coin measure on `Bool`. -/
def μcoin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac true + (2 : ℝ≥0∞)⁻¹ • Measure.dirac false

/-- The single non-zero centered increment with bound `b = 1`. -/
def Xc : ℕ → Bool → ℝ := fun k ω => if k = 0 then (if ω then (1:ℝ) else -1) else 0

/-- Two-step filtration: `⊥` at time 0, full Bool σ-algebra afterwards. -/
def ℱc : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq k := if k = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0 <;> simp [hi, hj]
    · have : j ≠ 0 := by omega
      simp [hi, this]
  le' := by
    intro i; by_cases hi : i = 0 <;> simp [hi]

instance : IsProbabilityMeasure μcoin := by
  constructor
  simp only [μcoin, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [ENNReal.inv_two_add_inv_two]

/-- Every real function on `Bool` is `⊤`-measurable, so all measurability is free. -/
theorem Xc_measurable (k : ℕ) : Measurable[(⊤ : MeasurableSpace Bool)] (Xc k) :=
  measurable_from_top

theorem Xc_integrable (k : ℕ) : Integrable (Xc k) μcoin := by
  haveI : IsFiniteMeasure μcoin := inferInstance
  exact (integrable_const (1 : ℝ)).mono' (Xc_measurable k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      simp only [Xc, Real.norm_eq_abs]
      by_cases hk : k = 0 <;> by_cases hω : ω <;> simp [hk, hω]))

/-- For any real `f`, `∫ f dμcoin = (1/2) f true + (1/2) f false`. -/
theorem integral_coin (f : Bool → ℝ) :
    ∫ ω, f ω ∂μcoin = (2:ℝ)⁻¹ * f true + (2:ℝ)⁻¹ * f false := by
  have hfin : Integrable f (Measure.dirac (true : Bool)) :=
    integrable_dirac (by exact enorm_lt_top)
  have hfin' : Integrable f (Measure.dirac (false : Bool)) :=
    integrable_dirac (by exact enorm_lt_top)
  have h1 : Integrable f ((2 : ℝ≥0∞)⁻¹ • Measure.dirac true) :=
    hfin.smul_measure (by simp)
  have h2 : Integrable f ((2 : ℝ≥0∞)⁻¹ • Measure.dirac false) :=
    hfin'.smul_measure (by simp)
  rw [μcoin, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [smul_eq_mul]
  norm_num [ENNReal.toReal_inv]

/-- Integral of the single increment is zero (fair-coin centering). -/
theorem integral_Xc_zero (k : ℕ) : ∫ ω, Xc k ω ∂μcoin = 0 := by
  rw [integral_coin]
  by_cases hk : k = 0 <;> simp [Xc, hk]

theorem ℱc_zero : (ℱc : Filtration ℕ (⊤ : MeasurableSpace Bool)) 0 = ⊥ := rfl

/-- Centering on the past: `μ[X k | ℱ k] = 0` for all `k`. -/
theorem Xc_center (k : ℕ) :
    (μcoin)[Xc k | ℱc k] =ᵐ[μcoin] (0 : Bool → ℝ) := by
  by_cases hk : k = 0
  · subst hk
    rw [ℱc_zero, condExp_bot]
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [integral_Xc_zero]; rfl
  · have hXk : Xc k = (0 : Bool → ℝ) := by
      funext ω; simp [Xc, hk]
    rw [hXk, condExp_zero]

/-- Conditional variance bound: `μ[X k² | ℱ k] ≤ σ² = 1`. -/
theorem Xc_var (k : ℕ) :
    (μcoin)[fun ω => (Xc k ω) ^ 2 | ℱc k] ≤ᵐ[μcoin] (fun _ => (1 : ℝ)) := by
  by_cases hk : k = 0
  · subst hk
    rw [ℱc_zero, condExp_bot]
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [integral_coin]
    simp only [Xc]
    norm_num
  · have hXk2 : (fun ω => (Xc k ω) ^ 2) = (0 : Bool → ℝ) := by
      funext ω; simp [Xc, hk]
    rw [hXk2, condExp_zero]
    exact Filter.Eventually.of_forall (fun _ => by norm_num)

/-- Boundedness `|X k| ≤ 1`. -/
theorem Xc_bound (k : ℕ) : ∀ᵐ ω ∂μcoin, |Xc k ω| ≤ 1 := by
  refine Filter.Eventually.of_forall (fun ω => ?_)
  simp only [Xc]
  by_cases hk : k = 0 <;> by_cases hω : ω <;> simp [hk, hω]

/-- `X` is increment-adapted: `X k` is `ℱc (k+1)`-measurable (full σ-algebra). -/
theorem Xc_incrementAdapted : IncrementAdapted ℱc Xc := by
  intro k
  have : ℱc (k + 1) = ⊤ := by simp [ℱc]
  rw [stronglyMeasurable_iff_measurable, this]
  exact measurable_from_top

/-- Strong adaptedness of the exponential process, via the author's helper. -/
theorem Xc_adapted (sigma2 b lam : ℝ) :
    StronglyAdapted ℱc (subGammaExponentialProcess Xc sigma2 b lam) :=
  stronglyAdapted_subGammaExponentialProcess_of_adapted sigma2 b lam Xc_incrementAdapted

/-- Integrability of the exponential process at each time. -/
theorem Xc_proc_integrable (sigma2 b lam : ℝ) (n : ℕ) :
    Integrable (subGammaExponentialProcess Xc sigma2 b lam n) μcoin := by
  haveI : IsFiniteMeasure μcoin := inferInstance
  refine (integrable_const (Real.exp (|lam| * (n : ℝ) + (n : ℝ) * |subGammaCgf sigma2 b lam|))).mono'
    (measurable_from_top (f := subGammaExponentialProcess Xc sigma2 b lam n)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs]
  unfold subGammaExponentialProcess
  rw [abs_of_nonneg (Real.exp_pos _).le]
  refine Real.exp_le_exp.2 ?_
  have hsum : |runningSum Xc n ω| ≤ (n : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∑ i ∈ Finset.range n, |Xc i ω| ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => by
        simp only [Xc]; by_cases hi : i = 0 <;> by_cases hω : ω <;> simp [hi, hω])
    refine hstep.trans ?_
    simp
  have h1 : lam * runningSum Xc n ω ≤ |lam| * (n : ℝ) := by
    calc lam * runningSum Xc n ω ≤ |lam * runningSum Xc n ω| := le_abs_self _
      _ = |lam| * |runningSum Xc n ω| := abs_mul _ _
      _ ≤ |lam| * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  have h2 : -((n : ℝ) * subGammaCgf sigma2 b lam) ≤ (n : ℝ) * |subGammaCgf sigma2 b lam| := by
    rw [neg_mul_eq_mul_neg]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact (neg_le_abs _)
  linarith [h1, h2]

#check @atTop_time_uniform_confidence_sequence_subGamma

/-! ### The concrete instantiation: all 12 hypotheses discharged with `X ≠ 0`. -/

theorem witness_atTopCS (delta : ℝ) (hδ : 0 < delta) :
    μcoin.real (atTopSubGammaUpperFailure Xc 1 1 1 delta) ≤ delta := by
  have hblam : (1 : ℝ) * 1 < 3 := by norm_num
  exact atTop_time_uniform_confidence_sequence_subGamma
    (μ := μcoin) (ℱ := ℱc) (X := Xc)
    (sigma2 := 1) (b := 1) (lam := 1) (delta := delta)
    hδ (by norm_num) (by norm_num) (by norm_num) hblam
    (fun k => Xc_measurable k)
    (fun k => Xc_integrable k)
    (Xc_adapted 1 1 1)
    (fun n => Xc_proc_integrable 1 1 1 n)
    (fun k => Xc_bound k)
    (fun k => Xc_center k)
    (fun k => Xc_var k)

/-- The process is genuinely non-zero: `Xc 0 true = 1 ≠ 0`. -/
example : Xc 0 true = 1 := by simp [Xc]
example : Xc 0 false = -1 := by simp [Xc]

#print axioms witness_atTopCS

end WitnessAtTopCS
end
