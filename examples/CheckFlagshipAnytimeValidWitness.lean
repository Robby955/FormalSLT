import FormalSLT.TestTimeMeta.FlagshipAnytimeValid

/-!
# Concrete satisfiability witness for the anytime-valid flagship

This file constructs an EXPLICIT probability space, filtration, and increment
process and discharges all eleven hypotheses of
`flagshipAnytimeValid_conclusion_from_incrementModel` simultaneously, on a
genuinely NONZERO process. It machine-checks non-vacuity (joint satisfiability),
which the pure `#print axioms` audit file does not.

Construction (single fair-coin Rademacher increment):
* `Ω = Bool`, ambient σ-algebra `⊤` (the discrete one on `Bool`).
* `μ = (1/2) dirac true + (1/2) dirac false` (the fair coin).
* `X 0 ω = if ω then 1 else -1` (the ±1 coin); `X k = 0` for `k ≥ 1`.
* `ℱ n = ⊥` if `n = 0`, else `⊤`.

The collapse the authors warn about (an `ℱk`-measurable, `ℱk`-centered `X`
being forced to `0`) is avoided exactly as documented: `X 0` is NOT
`ℱ 0 = ⊥`-measurable, so `μ[X 0 | ℱ 0] = ∫ X 0 = 0` is a genuine centering, not
a forcing one. The exponential process is adapted because `M 0` is constant
(`= 1`) and `ℱ n = ⊤` for `n ≥ 1`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.TestTimeMeta

noncomputable section

namespace WitnessFlagship

/-- Ambient space: the two-point set with its discrete σ-algebra `⊤`. -/
abbrev Ω : Type := Bool

/-- The fair coin `μ = (1/2)·δ_true + (1/2)·δ_false`. -/
noncomputable def μ : Measure Ω :=
  (1/2 : ENNReal) • Measure.dirac true + (1/2 : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure μ := by
  constructor
  unfold μ
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    MeasurableSet.univ, Measure.dirac_apply', Set.indicator_univ, Pi.one_apply,
    mul_one]
  rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 1 = 2 by norm_num,
    ENNReal.div_self (a := 2) (by norm_num) (by norm_num)]

/-- `μ.real {true} = 1/2`. -/
theorem μ_real_true : μ.real {true} = 1/2 := by
  unfold μ Measure.real
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (by trivial), Measure.dirac_apply' _ (by trivial)]
  simp only [Set.mem_singleton_iff, smul_eq_mul]
  rw [Set.indicator_of_mem (by trivial), Set.indicator_of_notMem (by decide)]
  simp only [Pi.one_apply, mul_one, mul_zero, add_zero]
  rw [show (1/2 : ENNReal) = ENNReal.ofReal (1/2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  rw [ENNReal.toReal_ofReal (by norm_num)]

/-- `μ.real {false} = 1/2`. -/
theorem μ_real_false : μ.real {false} = 1/2 := by
  unfold μ Measure.real
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (by trivial), Measure.dirac_apply' _ (by trivial)]
  simp only [Set.mem_singleton_iff, smul_eq_mul]
  rw [Set.indicator_of_notMem (by decide), Set.indicator_of_mem (by trivial)]
  simp only [Pi.one_apply, mul_one, mul_zero, zero_add]
  rw [show (1/2 : ENNReal) = ENNReal.ofReal (1/2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  rw [ENNReal.toReal_ofReal (by norm_num)]

/-- The Rademacher coin increment: `X 0` is `±1`, all later increments are `0`. -/
def X : ℕ → Ω → ℝ :=
  fun k ω => if k = 0 then (if ω then (1 : ℝ) else -1) else 0

/-- Filtration: trivial `⊥` at time `0`, full `⊤` thereafter. Monotone since
`⊥ ≤ ⊤`. The exponential process `M 0 = 1` is `⊥`-measurable (constant), and
`M n` for `n ≥ 1` is `⊤`-measurable. -/
def ℱ : Filtration ℕ (⊤ : MeasurableSpace Ω) where
  seq := fun n => if n = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp only [if_pos rfl]; exact bot_le
    · have hj : j ≠ 0 := by omega
      have hi' : i ≠ 0 := by omega
      simp only [if_neg hi', if_neg hj]
      exact le_refl ⊤
  le' := by intro i; split <;> exact le_top

theorem ℱ_zero : (ℱ : ℕ → MeasurableSpace Ω) 0 = ⊥ := rfl

theorem ℱ_succ {n : ℕ} (hn : n ≠ 0) : (ℱ : ℕ → MeasurableSpace Ω) n = ⊤ := by
  simp only [ℱ, if_neg hn]

-- Parameters: b = σ² = lam = 1 satisfy 0<b, 0≤σ², 0<lam, b·lam = 1 < 3.

/-- `∫ X k dμ = 0` for every `k`. -/
theorem integral_X_eq_zero (k : ℕ) : ∫ ω, X k ω ∂μ = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hint : Integrable (X 0) μ := Integrable.of_finite
    rw [integral_fintype hint, Fintype.sum_bool]
    simp only [X, if_pos rfl, if_true, if_false, smul_eq_mul]
    rw [μ_real_true, μ_real_false]
    norm_num
  · have hk0 : k ≠ 0 := by omega
    simp only [X, if_neg hk0, integral_zero]

/-- `∫ (X k)² dμ ≤ 1` for every `k` (`= 1` at `k = 0`, else `0`). -/
theorem integral_Xsq_le_one (k : ℕ) : ∫ ω, (X k ω) ^ 2 ∂μ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hint : Integrable (fun ω => (X 0 ω) ^ 2) μ := Integrable.of_finite
    rw [integral_fintype hint, Fintype.sum_bool]
    simp only [X, if_pos rfl, smul_eq_mul]
    rw [μ_real_true, μ_real_false]
    norm_num
  · have hk0 : k ≠ 0 := by omega
    simp only [X, if_neg hk0]
    simp

/-- Each increment is measurable w.r.t. the ambient `⊤`. -/
theorem hX_meas : ∀ k, Measurable (X k) := fun _ => measurable_from_top

/-- Each increment is integrable. -/
theorem hX_int : ∀ k, Integrable (X k) μ := fun _ => Integrable.of_finite

/-- `|X k| ≤ 1` everywhere. -/
theorem hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ (1 : ℝ) := by
  intro k
  refine ae_of_all _ (fun ω => ?_)
  simp only [X]
  split
  · rcases ω with _ | _ <;> norm_num
  · norm_num

/-- Conditional centering `μ[X k | ℱ k] =ᵐ 0`. For `k = 0`, `ℱ 0 = ⊥` and
`μ[X 0 | ⊥] = ∫ X 0 = 0`. For `k ≥ 1`, `X k = 0`. -/
theorem hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0 := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [ℱ_zero, condExp_bot]
    refine ae_of_all _ (fun ω => ?_)
    simp only [Pi.zero_apply]
    exact integral_X_eq_zero 0
  · have hk0 : k ≠ 0 := by omega
    have hXk : X k = 0 := by funext ω; simp [X, hk0]
    rw [hXk, condExp_zero]

/-- Conditional second-moment control `μ[X k² | ℱ k] ≤ᵐ σ² = 1`. For `k = 0`,
`ℱ 0 = ⊥` gives `μ[X 0² | ⊥] = ∫ X 0² = 1 ≤ 1`. For `k ≥ 1`, `X k² = 0 ≤ 1`. -/
theorem hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [ℱ_zero, condExp_bot]
    refine ae_of_all _ (fun ω => ?_)
    exact integral_Xsq_le_one 0
  · have hk0 : k ≠ 0 := by omega
    have hXk : (fun ω => (X k ω) ^ 2) = (0 : Ω → ℝ) := by
      funext ω; simp [X, hk0]
    rw [hXk, condExp_zero]
    refine ae_of_all _ (fun ω => ?_)
    simp only [Pi.zero_apply]
    norm_num

/-- The exponential process is strongly adapted to `ℱ`. `M 0 = exp 0 = 1`
is constant hence `⊥`-measurable; for `n ≥ 1`, `ℱ n = ⊤` makes everything
strongly measurable. -/
theorem h_adapted :
    StronglyAdapted ℱ (subGammaExponentialProcess X 1 1 1) := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [ℱ_zero]
    have hconst : subGammaExponentialProcess X 1 1 1 0 = fun _ => (1 : ℝ) := by
      funext ω
      simp [subGammaExponentialProcess, runningSum]
    rw [hconst]
    exact stronglyMeasurable_const
  · have hn0 : n ≠ 0 := by omega
    rw [ℱ_succ hn0]
    exact (measurable_from_top (f := subGammaExponentialProcess X 1 1 1 n)).stronglyMeasurable

/-- The exponential process is integrable at every time (a.e. bounded on the
finite space). -/
theorem h_integrable :
    ∀ k, Integrable (subGammaExponentialProcess X 1 1 1 k) μ :=
  fun _ => Integrable.of_finite

end WitnessFlagship

open WitnessFlagship

/-- **The witness.** All eleven hypotheses of the flagship theorem hold on the
concrete fair-coin Rademacher space, with `b = σ² = lam = 1`, any horizon and
threshold `t`. The conclusion is a genuine probability bound, so the theorem is
non-vacuous. -/
theorem flagship_witness (horizon : ℕ) (t : ℝ) :
    FlagshipAnytimeValidConclusion μ X 1 1 1 t horizon :=
  flagshipAnytimeValid_conclusion_from_incrementModel
    (μ := μ) (X := X) (ℱ := ℱ)
    (by norm_num)            -- 0 < b
    (by norm_num)            -- 0 ≤ σ²
    (by norm_num)            -- 0 < lam
    (by norm_num)            -- b * lam < 3
    hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

/-- The process is genuinely NONZERO: `X 0 true = 1 ≠ 0`, so this is not the
degenerate zero process. -/
example : X 0 true = 1 := by simp [X]
example : X 0 false = -1 := by simp [X]

/-- Sanity: the conclusion's tail bound at `t = 1`, `horizon = 1`, `lam = 1` is
`exp (-1) < 1` — a non-trivial probability bound, not `≤ 1` vacuity. -/
example : anytimeVilleTailContribution 1 1 1 = Real.exp (-1) := by
  simp [anytimeVilleTailContribution]

#print axioms flagship_witness
