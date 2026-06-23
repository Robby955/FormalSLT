/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.AtTopCS
import FormalSLT.AnytimeValid.EProcess
import FormalSLT.AnytimeValid.MixtureCS
import FormalSLT.Concentration.SubGamma.CondExpProduct

/-!
# Betting confidence sequences

This file adds the betting/e-process confidence-sequence construction for a
bounded mean. For a candidate null mean `m` and predictable betting fractions
`lambda_k`, the wealth process is

`K_n(m) = prod_{k < n} (1 + lambda_k * (X_k - m))`.

If each factor is nonnegative, each `lambda_k` is `F_k`-measurable and
nonnegative, and the null conditional-mean condition
`E[X_k | F_k] <= m` holds, then `K_n(m)` is a nonnegative supermartingale.
Ville's inequality gives the countable-time rejection bound
`P(exists n > 0, K_n(m) >= 1 / delta) <= delta`.

The increment process uses `IncrementAdapted F X`, so `X_k` is revealed at
time `k+1`. The betting fraction process uses `StronglyAdapted F lambda`, so
`lambda_k` is predictable.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace FormalSLT.AnytimeValid

noncomputable section

/-- One multiplicative betting factor for candidate mean `m`. -/
def bettingFactor {Ω : Type*} (X lambda : ℕ → Ω → ℝ) (m : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  1 + lambda k ω * (X k ω - m)

/-- Betting wealth `K_n(m) = prod_{k<n} (1 + lambda_k (X_k - m))`. -/
def bettingWealthProcess {Ω : Type*} (X lambda : ℕ → Ω → ℝ) (m : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range n, bettingFactor X lambda m k ω

/-- Candidate mean `m` is rejected once the betting wealth crosses `1 / delta`. -/
def bettingMeanRejectionEvent {Ω : Type*} (X lambda : ℕ → Ω → ℝ) (m delta : ℝ) :
    Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧ (1 / delta) ≤ bettingWealthProcess X lambda m n ω}

/-- Nonnegative betting factors give nonnegative wealth. -/
theorem bettingWealth_nonneg {Ω : Type*} {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω) :
    0 ≤ bettingWealthProcess X lambda m := by
  intro n ω
  unfold bettingWealthProcess
  exact Finset.prod_nonneg fun k _ => hfactor_nonneg k ω

/-- The betting wealth is adapted when increments are revealed one step late and bets are predictable. -/
theorem stronglyAdapted_bettingWealthProcess_of_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hX_adapted : IncrementAdapted ℱ X)
    (hlambda_adapted : StronglyAdapted ℱ lambda) :
    StronglyAdapted ℱ (bettingWealthProcess X lambda m) := by
  intro n
  have hprod : StronglyMeasurable[ℱ n]
      (fun ω => ∏ k ∈ Finset.range n, bettingFactor X lambda m k ω) := by
    apply Finset.stronglyMeasurable_fun_prod
    intro k hk
    rw [Finset.mem_range] at hk
    have hlambda : StronglyMeasurable[ℱ n] (lambda k) :=
      (hlambda_adapted k).mono (ℱ.mono (le_of_lt hk))
    have hX : StronglyMeasurable[ℱ n] (X k) :=
      (hX_adapted k).mono (ℱ.mono (Nat.succ_le_of_lt hk))
    exact stronglyMeasurable_const.add (hlambda.mul (hX.sub stronglyMeasurable_const))
  simpa [bettingWealthProcess] using hprod

/--
The one-step betting factor has conditional expectation at most `1` under the
conditional-mean null. The betting fraction is predictable, bounded, and
nonnegative.
-/
theorem bettingFactor_condExp_le_one_of_condMean
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m C : ℝ} (k : ℕ)
    (hlambda_meas : StronglyMeasurable[ℱ k] (lambda k))
    (hlambda_bdd : ∀ᵐ ω ∂μ, |lambda k ω| ≤ C)
    (hlambda_nonneg : ∀ᵐ ω ∂μ, 0 ≤ lambda k ω)
    (hX_int : Integrable (X k) μ)
    (hmean : μ[X k | ℱ k] ≤ᵐ[μ] fun _ => m) :
    μ[bettingFactor X lambda m k | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
  set Y : Ω → ℝ := fun ω => X k ω - m with hY_def
  have hY_int : Integrable Y μ := by
    simpa [Y] using hX_int.sub (integrable_const m)
  have hprod_int : Integrable (fun ω => lambda k ω * Y ω) μ := by
    refine hY_int.bdd_mul (c := C)
      ((hlambda_meas.mono (ℱ.le k)).aestronglyMeasurable) ?_
    filter_upwards [hlambda_bdd] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hconst_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have hsplit :
      μ[bettingFactor X lambda m k | ℱ k]
        =ᵐ[μ]
      μ[(fun _ : Ω => (1 : ℝ)) | ℱ k] + μ[fun ω => lambda k ω * Y ω | ℱ k] :=
    by simpa [bettingFactor, Y] using condExp_add hconst_int hprod_int (ℱ k)
  have hpull :
      μ[fun ω => lambda k ω * Y ω | ℱ k]
        =ᵐ[μ] fun ω => lambda k ω * (μ[Y | ℱ k]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (ℱ.le k) hlambda_meas hlambda_bdd hY_int
  have hsub :
      μ[Y | ℱ k] =ᵐ[μ] fun ω => (μ[X k | ℱ k]) ω - m := by
    have hraw := condExp_sub hX_int (integrable_const m) (ℱ k)
    have hconst : μ[(fun _ : Ω => m) | ℱ k] = fun _ : Ω => m :=
      condExp_const (ℱ.le k) m
    filter_upwards [hraw] with ω hω
    change μ[X k - (fun _ : Ω => m) | ℱ k] ω = μ[X k | ℱ k] ω - m
    rw [hω]
    simp [hconst]
  have hconst_one : μ[(fun _ : Ω => (1 : ℝ)) | ℱ k] = fun _ : Ω => (1 : ℝ) :=
    condExp_const (ℱ.le k) 1
  filter_upwards [hsplit, hpull, hsub, hmean, hlambda_nonneg] with
    ω hsplitω hpullω hsubω hmeanω hlambdaω
  rw [hsplitω]
  simp only [Pi.add_apply]
  rw [hconst_one, hpullω, hsubω]
  have hdiff : (μ[X k | ℱ k]) ω - m ≤ 0 := sub_nonpos.mpr hmeanω
  have hmul : lambda k ω * ((μ[X k | ℱ k]) ω - m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlambdaω hdiff
  linarith

/--
The betting wealth is a supermartingale from one-step factor control.

The hypotheses keep the predictable-bet discipline explicit: `X` uses
`IncrementAdapted`, while `lambda` is `StronglyAdapted`. The bounded-current-
wealth hypothesis is the exact condition needed to use mathlib's conditional
pull-out theorem.
-/
theorem bettingWealth_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hX_adapted : IncrementAdapted ℱ X)
    (hlambda_adapted : StronglyAdapted ℱ lambda)
    (hwealth_int : ∀ n, Integrable (bettingWealthProcess X lambda m n) μ)
    (hfactor_int : ∀ n, Integrable (bettingFactor X lambda m n) μ)
    (hwealth_bdd : ∀ n, ∃ C : ℝ,
      ∀ᵐ ω ∂μ, |bettingWealthProcess X lambda m n ω| ≤ C)
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω)
    (hfactor_step : ∀ k,
      μ[bettingFactor X lambda m k | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    Supermartingale (bettingWealthProcess X lambda m) ℱ μ := by
  refine supermartingale_nat
    (stronglyAdapted_bettingWealthProcess_of_adapted hX_adapted hlambda_adapted)
    hwealth_int ?_
  intro n
  set Z : Ω → ℝ := bettingWealthProcess X lambda m n with hZ_def
  set Y : Ω → ℝ := bettingFactor X lambda m n with hY_def
  have hfact :
      bettingWealthProcess X lambda m (n + 1) = fun ω => Z ω * Y ω := by
    funext ω
    simp [bettingWealthProcess, bettingFactor, Z, Y, Finset.prod_range_succ, mul_comm]
  have hZ_meas : StronglyMeasurable[ℱ n] Z := by
    simpa [Z] using
      stronglyAdapted_bettingWealthProcess_of_adapted
        (ℱ := ℱ) (X := X) (lambda := lambda) (m := m)
        hX_adapted hlambda_adapted n
  obtain ⟨C, hZ_bdd⟩ := hwealth_bdd n
  have hpull :
      μ[fun ω => Z ω * Y ω | ℱ n] =ᵐ[μ] fun ω => Z ω * (μ[Y | ℱ n]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (ℱ.le n) hZ_meas hZ_bdd (by simpa [Y] using hfactor_int n)
  rw [hfact]
  filter_upwards [hpull, hfactor_step n] with ω hpullω hstepω
  rw [hpullω]
  have hZ_nonneg : 0 ≤ Z ω := by
    simpa [Z] using bettingWealth_nonneg (X := X) (lambda := lambda) (m := m)
      hfactor_nonneg n ω
  calc
    Z ω * (μ[Y | ℱ n]) ω ≤ Z ω * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [Y] using hstepω) hZ_nonneg
    _ = bettingWealthProcess X lambda m n ω := by simp [Z]

/-- The betting wealth is an e-process when it is nonnegative and a supermartingale. -/
theorem bettingWealth_eProcess
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hsup : Supermartingale (bettingWealthProcess X lambda m) ℱ μ)
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω) :
    EProcess μ ℱ (bettingWealthProcess X lambda m) where
  nonneg := bettingWealth_nonneg hfactor_nonneg
  start_one := fun ω => by simp [bettingWealthProcess]
  supermartingale := hsup

/-- Countable-time Ville confidence sequence for the betting wealth. -/
theorem betting_time_uniform_confidence_sequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m delta : ℝ}
    (hdelta : 0 < delta)
    (hE : EProcess μ ℱ (bettingWealthProcess X lambda m)) :
    μ.real (bettingMeanRejectionEvent X lambda m delta) ≤ delta := by
  have ha : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ)
      (M := bettingWealthProcess X lambda m)
      hE.supermartingale hE.nonneg ha
  rw [hE.integral_start_eq_one] at hville
  have h_atTop :
      μ.real (atTopCrossingEvent (bettingWealthProcess X lambda m) (1 / delta))
        ≤ delta := by
    calc
      μ.real (atTopCrossingEvent (bettingWealthProcess X lambda m) (1 / delta))
          = delta *
            ((1 / delta) *
              μ.real
                (atTopCrossingEvent (bettingWealthProcess X lambda m) (1 / delta))) := by
            field_simp [hdelta.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
      _ = delta := by ring
  have hsubset :
      bettingMeanRejectionEvent X lambda m delta
        ⊆ atTopCrossingEvent (bettingWealthProcess X lambda m) (1 / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn, hn_cross⟩
    exact ⟨n, hn_cross⟩
  exact (measureReal_mono hsubset).trans h_atTop

/--
End-to-end betting confidence sequence from predictable bets and the
conditional-mean null.
-/
theorem betting_confidence_sequence_of_condMean
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m delta : ℝ}
    (hdelta : 0 < delta)
    (hX_adapted : IncrementAdapted ℱ X)
    (hlambda_adapted : StronglyAdapted ℱ lambda)
    (hlambda_bdd : ∀ k, ∃ C : ℝ, ∀ᵐ ω ∂μ, |lambda k ω| ≤ C)
    (hlambda_nonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambda k ω)
    (hX_int : ∀ k, Integrable (X k) μ)
    (hwealth_int : ∀ n, Integrable (bettingWealthProcess X lambda m n) μ)
    (hfactor_int : ∀ n, Integrable (bettingFactor X lambda m n) μ)
    (hwealth_bdd : ∀ n, ∃ C : ℝ,
      ∀ᵐ ω ∂μ, |bettingWealthProcess X lambda m n ω| ≤ C)
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω)
    (hmean : ∀ k, μ[X k | ℱ k] ≤ᵐ[μ] fun _ => m) :
    μ.real (bettingMeanRejectionEvent X lambda m delta) ≤ delta := by
  have hfactor_step :
      ∀ k, μ[bettingFactor X lambda m k | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    intro k
    obtain ⟨C, hC⟩ := hlambda_bdd k
    exact bettingFactor_condExp_le_one_of_condMean
      (μ := μ) (ℱ := ℱ) (X := X) (lambda := lambda) (m := m) (C := C) k
      (hlambda_adapted k) hC (hlambda_nonneg k) (hX_int k) (hmean k)
  have hsup : Supermartingale (bettingWealthProcess X lambda m) ℱ μ :=
    bettingWealth_supermartingale
      hX_adapted hlambda_adapted hwealth_int hfactor_int hwealth_bdd
      hfactor_nonneg hfactor_step
  exact betting_time_uniform_confidence_sequence hdelta
    (bettingWealth_eProcess hsup hfactor_nonneg)

namespace BettingNonVacuityWitness

/-- Uniform probability measure on `Bool`. -/
def μBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure μBool := by
  refine ⟨?_⟩
  simp only [μBool, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.add_halves 1

/-- One Rademacher increment, followed by zero increments. -/
def XBool : ℕ → Bool → ℝ :=
  fun k ω => if k = 0 then (if ω then (1 : ℝ) else -1) else 0

/-- Constant predictable betting fraction `1/4`. -/
def lambdaBool : ℕ → Bool → ℝ :=
  fun _ _ => 1 / 4

/-- The two-level filtration: `F 0 = bot`, `F k = top` for `k >= 1`. -/
def filtBool : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq := fun k => if k = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj]; exact bot_le
    · have hj : j ≠ 0 := by
        rintro rfl
        exact hi (Nat.le_zero.mp hij)
      simp [hi, hj]
  le' := by
    intro i
    by_cases hi : i = 0
    · simp only [hi]; exact bot_le
    · simp [hi]

theorem XBool_incrementAdapted : IncrementAdapted filtBool XBool := by
  intro k
  have hfilt : filtBool (k + 1) = ⊤ := by simp [filtBool]
  rw [show (StronglyMeasurable[filtBool (k + 1)] (XBool k)) =
      (StronglyMeasurable[⊤] (XBool k)) from by rw [hfilt]]
  exact measurable_from_top.stronglyMeasurable

theorem lambdaBool_stronglyAdapted : StronglyAdapted filtBool lambdaBool := by
  intro k
  exact stronglyMeasurable_const

theorem XBool_int (k : ℕ) : Integrable (XBool k) μBool := Integrable.of_finite

theorem factor_nonneg (k : ℕ) (ω : Bool) :
    0 ≤ bettingFactor XBool lambdaBool 0 k ω := by
  simp only [bettingFactor, lambdaBool, XBool, sub_zero]
  by_cases hk : k = 0
  · subst hk
    cases ω <;> norm_num
  · simp [hk]

theorem lambda_nonneg (k : ℕ) : ∀ᵐ ω ∂μBool, 0 ≤ lambdaBool k ω :=
  Filter.Eventually.of_forall (by intro ω; norm_num [lambdaBool])

theorem lambda_bdd (k : ℕ) : ∃ C : ℝ, ∀ᵐ ω ∂μBool, |lambdaBool k ω| ≤ C :=
  ⟨1, Filter.Eventually.of_forall (by intro ω; norm_num [lambdaBool])⟩

theorem XBool_center (k : ℕ) : μBool[XBool k | filtBool k] =ᵐ[μBool] 0 := by
  by_cases hk : k = 0
  · subst hk
    have hF0 : filtBool 0 = ⊥ := by simp [filtBool]
    rw [hF0, condExp_bot]
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
      funext ω
      simp only [XBool, if_neg hk]
      rfl
    rw [hXk, condExp_zero]

theorem XBool_condMean (k : ℕ) : μBool[XBool k | filtBool k] ≤ᵐ[μBool] fun _ => (0 : ℝ) := by
  filter_upwards [XBool_center k] with ω hω
  rw [hω]
  rfl

theorem factor_int (k : ℕ) : Integrable (bettingFactor XBool lambdaBool 0 k) μBool :=
  Integrable.of_finite

theorem wealth_int (n : ℕ) : Integrable (bettingWealthProcess XBool lambdaBool 0 n) μBool :=
  Integrable.of_finite

theorem wealth_bdd (n : ℕ) :
    ∃ C : ℝ, ∀ᵐ ω ∂μBool, |bettingWealthProcess XBool lambdaBool 0 n ω| ≤ C := by
  refine ⟨max
      (|bettingWealthProcess XBool lambdaBool 0 n true|)
      (|bettingWealthProcess XBool lambdaBool 0 n false|), ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro ω
  cases ω
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- The betting witness gains wealth on the positive Rademacher outcome. -/
theorem bettingWitness_positive_gain :
    (1 : ℝ) < bettingWealthProcess XBool lambdaBool 0 1 true := by
  simp [bettingWealthProcess, bettingFactor, XBool, lambdaBool]

/--
Concrete non-vacuity witness: one nonzero Rademacher increment with constant
predictable bet `1/4`. At `delta = 4/5`, the threshold is `5/4`, and the
time-uniform rejection event has mass at most `4/5`.
-/
theorem bettingNonVacuityWitness :
    μBool.real (bettingMeanRejectionEvent XBool lambdaBool 0 (4 / 5)) ≤ (4 / 5 : ℝ) := by
  refine betting_confidence_sequence_of_condMean
    (μ := μBool) (ℱ := filtBool) (X := XBool) (lambda := lambdaBool)
    (m := 0) (delta := 4 / 5)
    (by norm_num)
    XBool_incrementAdapted lambdaBool_stronglyAdapted lambda_bdd lambda_nonneg XBool_int
    wealth_int factor_int wealth_bdd factor_nonneg XBool_condMean

end BettingNonVacuityWitness

end

end FormalSLT.AnytimeValid
