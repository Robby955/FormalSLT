import FormalSLT.TestTimeMeta.FlagshipFourComponentAssembly

/-!
# Concrete non-vacuity witness for `flagshipFourComponent_conclusion_from_incrementModel`

We instantiate the increment-model flagship theorem at fully concrete data with a
**non-zero** increment process and show the entire hypothesis bundle
(`hbound, hcenter, hvar, h_adapted, ...`) is simultaneously satisfiable while the
conclusion is non-trivial.

Space      : `Ω = Bool` (two points), `μ = uniform` (probability measure).
Filtration : `ℱ 0 = ⊥` (trivial), `ℱ k = ⊤` for `k ≥ 1`.
Process    : `X 0 ω = if ω then 1 else -1` (Rademacher, NON-ZERO), `X k = 0` for `k ≥ 1`.
Params     : `sigma2 = 1, b = 1, lam = 1, t = 1, n = 1`.

The load-bearing point: `X 0 ≠ 0` is conditionally centered against `ℱ 0 = ⊥`
(`μ[X 0 | ⊥] = ∫ X 0 = 0`) WITHOUT collapsing, precisely because `X 0` is not
`ℱ 0`-measurable. `condExp_of_stronglyMeasurable` does NOT apply. The running sum
`S_n` is still `ℱ n`-measurable for the adaptedness hypothesis.
-/

open FormalSLT.TestTimeMeta
open FormalSLT.AnytimeValid
open MeasureTheory ProbabilityTheory

noncomputable section

/-- Uniform probability measure on `Bool`. -/
noncomputable def μF : Measure Bool :=
  (1/2 : ENNReal) • Measure.dirac true + (1/2 : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure μF := by
  constructor
  unfold μF
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
  rw [ENNReal.div_add_div_same]
  rw [show (1 : ENNReal) + 1 = 2 by norm_num, ENNReal.div_self (by norm_num) (by norm_num)]

/-- The non-zero Rademacher increment at time 0; zero thereafter. -/
def XF : ℕ → Bool → ℝ := fun k ω => if k = 0 then (if ω then 1 else -1) else 0

/-- The filtration: trivial at time 0, full thereafter. So `X 0` is NOT `ℱ 0`-measurable
(it is not `⊥`-measurable, being non-constant), avoiding the collapse, while the running
sum `S_n` is `ℱ n`-measurable for every `n`. -/
def ℱF : Filtration ℕ (by infer_instance : MeasurableSpace Bool) where
  seq k := if k = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj, if_true, if_false]; exact bot_le
    · have hj : j ≠ 0 := by omega
      simp only [hi, hj, if_false, le_refl]
  le' := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, if_true]; exact bot_le
    · simp only [hk, if_false]; exact le_refl _

lemma XF_meas (k : ℕ) : Measurable (XF k) := by
  apply measurable_of_countable

lemma XF_int (k : ℕ) : Integrable (XF k) μF := by
  apply Integrable.of_finite

/-- `μF {ω} = 1/2` for either point. -/
lemma μF_singleton (ω : Bool) : μF {ω} = 1/2 := by
  unfold μF
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (by trivial), Measure.dirac_apply' _ (by trivial)]
  cases ω <;>
  · simp only [smul_eq_mul]
    norm_num [Set.indicator_apply]

/-- `μF.real {ω} = 1/2` for either point. -/
lemma μF_real_singleton (ω : Bool) : μF.real {ω} = 1/2 := by
  rw [Measure.real, μF_singleton]
  rw [show (1/2 : ENNReal) = ENNReal.ofReal (1/2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  rw [ENNReal.toReal_ofReal (by norm_num)]

/-- `∫ X 0 ∂μF = 0`: the Rademacher increment is centered. -/
lemma integral_XF_zero : ∫ ω, XF 0 ω ∂μF = 0 := by
  rw [integral_fintype (μ := μF) (XF_int 0)]
  simp only [Fintype.sum_bool, μF_real_singleton]
  unfold XF
  norm_num

/-- `∫ (X 0)² ∂μF = 1`: the conditional second moment hits `sigma2 = 1`. -/
lemma integral_XF_sq : ∫ ω, (XF 0 ω) ^ 2 ∂μF = 1 := by
  rw [integral_fintype (μ := μF) (by exact Integrable.of_finite)]
  simp only [Fintype.sum_bool, μF_real_singleton]
  unfold XF
  norm_num

/-- `ℱF 0 = ⊥`. -/
lemma ℱF_zero : (ℱF : Filtration ℕ _).seq 0 = ⊥ := rfl

/-- For `k ≥ 1`, `ℱF k = ⊤`, the full σ-algebra. -/
lemma ℱF_succ (k : ℕ) : (ℱF : Filtration ℕ _).seq (k + 1) = ⊤ := by
  simp [ℱF]

/-- `h_adapted`: the exponential process is `ℱF`-adapted. -/
lemma hadaptedF : StronglyAdapted ℱF (subGammaExponentialProcess XF 1 1 1) := by
  intro n
  cases n with
  | zero =>
    -- M_0 = exp(1·S_0 − 0·cgf) = exp 0, constant ⟹ ⊥-measurable.
    rw [ℱF_zero]
    have hconst : subGammaExponentialProcess XF 1 1 1 0
        = fun _ => Real.exp (1 * 0 - (0 : ℝ) * subGammaCgf 1 1 1) := by
      funext ω
      simp [subGammaExponentialProcess, runningSum]
    rw [hconst]
    exact stronglyMeasurable_const
  | succ m =>
    -- ℱF (m+1) = ⊤, everything is measurable.
    rw [ℱF_succ]
    exact (Measurable.stronglyMeasurable (by
      apply Measurable.comp (by exact Real.measurable_exp)
      exact measurable_from_top)).mono le_top

/-- `h_integrable`: every `M_k` is integrable (finite space). -/
lemma hintF (k : ℕ) : Integrable (subGammaExponentialProcess XF 1 1 1 k) μF :=
  Integrable.of_finite

/-- `hbound`: `|XF k| ≤ 1` a.e. -/
lemma hboundF (k : ℕ) : ∀ᵐ ω ∂μF, |XF k ω| ≤ 1 := by
  filter_upwards with ω
  unfold XF
  by_cases hk : k = 0
  · simp only [hk, if_true]; cases ω <;> norm_num
  · simp only [hk, if_false]; norm_num

/-- `hcenter`: `μ[XF k | ℱF k] = 0`.  At `k = 0`, this is the genuine non-collapse
case: `μ[XF 0 | ⊥] = ∫ XF 0 = 0` with `XF 0 ≠ 0`. -/
lemma hcenterF (k : ℕ) : μF[XF k | (ℱF : Filtration ℕ _) k] =ᵐ[μF] 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [ℱF_zero, condExp_bot]
    filter_upwards with ω
    rw [integral_XF_zero]; rfl
  · have hXk : XF k = 0 := by funext ω; simp [XF, hk]
    rw [hXk, condExp_zero]

/-- `hvar`: `μ[(XF k)² | ℱF k] ≤ 1 = sigma2`.  At `k = 0`, `μ[(XF 0)² | ⊥] = 1`. -/
lemma hvarF (k : ℕ) :
    μF[fun ω => (XF k ω) ^ 2 | (ℱF : Filtration ℕ _) k] ≤ᵐ[μF] fun _ => (1 : ℝ) := by
  by_cases hk : k = 0
  · subst hk
    rw [ℱF_zero, condExp_bot]
    filter_upwards with ω
    rw [integral_XF_sq]
  · have hXk : (fun ω => (XF k ω) ^ 2) = 0 := by funext ω; simp [XF, hk]
    rw [hXk, condExp_zero]
    filter_upwards with ω
    norm_num

/--
**CONCRETE NON-VACUITY WITNESS.**

We instantiate `flagshipFourComponent_conclusion_from_incrementModel` at fully
explicit data with a `NON-ZERO` increment process `XF` (Rademacher at time 0).
All hypotheses are discharged simultaneously.  The collapse argument
(`condExp_of_stronglyMeasurable`) does NOT fire because `XF 0` is not
`ℱF 0 = ⊥`-measurable; the centering `μ[XF 0 | ⊥] = ∫ XF 0 = 0` is genuine.
-/
example :
    FlagshipFourComponentConclusion
      (flagshipFourComponent_certificate_from_incrementModel
        (μ := μF) (ℱ := ℱF) (X := XF) (sigma2 := 1) (b := 1)
        (lam := 1) (t := 1) (n := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        XF_meas XF_int hadaptedF hintF hboundF hcenterF hvarF)
      μF XF 1 1 1 1 1 :=
  flagshipFourComponent_conclusion_from_incrementModel
    (μ := μF) (ℱ := ℱF) (X := XF) (sigma2 := 1) (b := 1)
    (lam := 1) (t := 1) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    XF_meas XF_int hadaptedF hintF hboundF hcenterF hvarF

-- All five hypothesis lemmas hold of the SAME concrete `XF` (non-zero at time 0),
-- and feed the theorem, so the hypothesis bundle is jointly satisfiable.
#check @hadaptedF
#check @hcenterF
#check @hvarF
#print axioms hcenterF

/-! ### Adversarial self-check: the witness is genuinely non-trivial -/

-- (1) `XF` is GENUINELY NON-ZERO at time 0 on both points.
example : XF 0 true = 1 := by unfold XF; norm_num
example : XF 0 false = -1 := by unfold XF; norm_num
example : XF 0 true ≠ 0 := by unfold XF; norm_num

-- (2) The conclusion's bound `anytimeVilleTailContribution 1 1 1 = exp(-1) < 1`: NON-TRIVIAL
--     (a real tail probability bound, not the vacuous `≤ 1`).
example : anytimeVilleTailContribution 1 1 1 < 1 := by
  unfold anytimeVilleTailContribution
  rw [show (-1 : ℝ) * (1 : ℕ) * 1 = -1 by norm_num]
  calc Real.exp (-1) < Real.exp 0 := by apply Real.exp_lt_exp.mpr; norm_num
    _ = 1 := Real.exp_zero

-- (3) The bound is also POSITIVE: it lies in (0,1), so it is not the vacuous `≤ 0` either.
example : 0 < anytimeVilleTailContribution 1 1 1 := by
  unfold anytimeVilleTailContribution; exact Real.exp_pos _

-- (4) `ℱF 0 = ⊥`: the centering hypothesis is discharged against the trivial σ-algebra,
--     which does NOT contain the non-constant `XF 0`, so the collapse lemma cannot fire.
example : (ℱF : Filtration ℕ _).seq 0 = ⊥ := ℱF_zero

end
