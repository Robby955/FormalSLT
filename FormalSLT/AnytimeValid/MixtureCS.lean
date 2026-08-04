/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.AtTopCS
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalProbability

/-!
# Mixture confidence sequences

This file adds the measure-mixture exponential process used by the method of
mixtures. The core analytic primitive is the conditional-expectation swap for a
prior integral over tilts.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Prior mixture of the fixed-tilt sub-Gamma exponential processes. -/
def mixtureExponentialProcess {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (ρ : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ lam, subGammaExponentialProcess X sigma2 b lam n ω ∂ρ

/-- Continuous uniform prior on a compact tilt interval. -/
def uniformTiltPrior (lam0 lam1 : ℝ) : Measure ℝ :=
  volume[|Set.Icc lam0 lam1]

lemma uniformTiltPrior_isProbabilityMeasure {lam0 lam1 : ℝ} (h : lam0 < lam1) :
    IsProbabilityMeasure (uniformTiltPrior lam0 lam1) := by
  unfold uniformTiltPrior
  refine ProbabilityTheory.cond_isProbabilityMeasure_of_finite ?_ ?_
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr h))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

lemma uniformTiltPrior_valid_tilt_support
    {b lam0 lam1 : ℝ} (h0 : 0 < lam0) (_h01 : lam0 < lam1) (h1 : lam1 < 3 / b) :
    ∀ᵐ lam ∂uniformTiltPrior lam0 lam1, lam ∈ Set.Ioo 0 (3 / b) := by
  unfold uniformTiltPrior
  exact ProbabilityTheory.ae_cond_of_forall_mem measurableSet_Icc fun lam hlam => by
    exact ⟨h0.trans_le hlam.1, hlam.2.trans_lt h1⟩

/--
Order from testing set integrals on a sub-sigma-algebra. This is the
inequality analogue of the conditional-expectation uniqueness principle.
-/
theorem ae_le_of_forall_subalgebra_setIntegral_le
    {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfm : StronglyMeasurable[m] f) (hgm : StronglyMeasurable[m] g)
    (hfg : ∀ s : Set Ω, MeasurableSet[m] s → μ s < ⊤ →
      ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  have hnonneg : 0 ≤ᵐ[μ.trim hm] fun x => g x - f x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
    · intro t ht _htfin
      exact ((hg.trim hm hgm).sub (hf.trim hm hfm)).integrableOn
    · intro s hs hμs
      change 0 ≤ ∫ x in s, (g - f) x ∂μ.trim hm
      rw [integral_sub' (hg.trim hm hgm).integrableOn
        (hf.trim hm hfm).integrableOn, sub_nonneg]
      rw [← setIntegral_trim hm hfm hs, ← setIntegral_trim hm hgm hs]
      exact hfg s hs (by rwa [trim_measurableSet_eq hm hs] at hμs)
  have htrim : f ≤ᵐ[μ.trim hm] g := by
    filter_upwards [hnonneg] with x hx
    have hx' : 0 ≤ g x - f x := by simpa [Pi.zero_apply] using hx
    linarith
  exact ae_le_of_ae_le_trim htrim

/--
Conditional expectation commutes with the prior integral, under the product
integrability and conditional-side measurability obligations needed for Fubini
and the defining set-integral property of conditional expectation.
-/
theorem condExp_mixture_swap
    {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ]
    (hm : m ≤ m₀)
    {ρ : Measure ℝ} [SFinite ρ]
    {M : ℝ → ℕ → Ω → ℝ} {n : ℕ}
    (hM_int :
      Integrable (fun p : ℝ × Ω => M p.1 (n + 1) p.2) (ρ.prod μ))
    (hM_int_restrict :
      ∀ {s : Set Ω}, @MeasurableSet Ω m₀ s → μ s < ⊤ →
        Integrable (fun p : Ω × ℝ => M p.2 (n + 1) p.1) ((μ.restrict s).prod ρ))
    (hCE_int_restrict :
      ∀ {s : Set Ω}, @MeasurableSet Ω m₀ s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => (condExp m μ (M p.2 (n + 1))) p.1)
          ((μ.restrict s).prod ρ))
    (hCE_meas :
      @AEStronglyMeasurable Ω ℝ _ m m₀
        (fun ω => ∫ lam, (condExp m μ (M lam (n + 1))) ω ∂ρ) μ) :
    condExp m μ (fun ω => ∫ lam, M lam (n + 1) ω ∂ρ) =ᵐ[μ]
      fun ω => ∫ lam, (condExp m μ (M lam (n + 1))) ω ∂ρ := by
  let f : Ω → ℝ := fun ω => ∫ lam, M lam (n + 1) ω ∂ρ
  let g : Ω → ℝ := fun ω => ∫ lam, (condExp m μ (M lam (n + 1))) ω ∂ρ
  have hf_int : Integrable f μ := by
    have hswap :
        Integrable (fun p : Ω × ℝ => M p.2 (n + 1) p.1) (μ.prod ρ) := by
      simpa [Function.comp_def] using hM_int.swap
    simpa [f] using hswap.integral_prod_left
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf_int ?_ ?_ hCE_meas
  · intro s hs hμs
    simpa [IntegrableOn, g] using
      (hCE_int_restrict (hm s hs) hμs).integral_prod_left
  · intro s hs hμs
    have hCEs := hCE_int_restrict (hm s hs) hμs
    have hMs := hM_int_restrict (hm s hs) hμs
    have h_fiber : ∀ᵐ lam ∂ρ, Integrable (fun ω => M lam (n + 1) ω) μ := by
      simpa using hM_int.prod_right_ae
    calc
      ∫ ω in s, g ω ∂μ
          = ∫ ω, ∫ lam, (condExp m μ (M lam (n + 1))) ω ∂ρ ∂(μ.restrict s) := by
              rfl
      _ = ∫ lam, ∫ ω, (condExp m μ (M lam (n + 1))) ω ∂(μ.restrict s) ∂ρ := by
              simpa [Function.uncurry, g] using
                (integral_integral_swap (μ := μ.restrict s) (ν := ρ)
                  (f := fun ω lam => (condExp m μ (M lam (n + 1))) ω) hCEs)
      _ = ∫ lam, ∫ ω in s, M lam (n + 1) ω ∂μ ∂ρ := by
              apply integral_congr_ae
              filter_upwards [h_fiber] with lam hlam
              exact setIntegral_condExp hm hlam hs
      _ = ∫ ω, ∫ lam, M lam (n + 1) ω ∂ρ ∂(μ.restrict s) := by
              simpa [Function.uncurry] using
                (integral_integral_swap (μ := μ.restrict s) (ν := ρ)
                  (f := fun ω lam => M lam (n + 1) ω) hMs).symm
      _ = ∫ ω in s, f ω ∂μ := by
              rfl

/--
One mixture supermartingale step from fixed-tilt conditional steps, proved by
testing on `F_n`-measurable sets. This avoids needing joint measurability of the
chosen conditional-expectation versions in the tilt parameter.
-/
theorem mixture_condExp_step_of_fixed_tilt_steps
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b : ℝ} {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (h_adapted_mix : StronglyAdapted ℱ (mixtureExponentialProcess X sigma2 b ρ))
    (h_integrable_mix : ∀ n, Integrable (mixtureExponentialProcess X sigma2 b ρ n) μ)
    (hM_int_next :
      ∀ n, Integrable
        (fun p : ℝ × Ω => subGammaExponentialProcess X sigma2 b p.1 (n + 1) p.2)
        (ρ.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 (n + 1) p.1)
          ((μ.restrict s).prod ρ))
    (hM_int_current :
      ∀ n, Integrable
        (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 n p.1)
        (μ.prod ρ))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 n p.1)
          ((μ.restrict s).prod ρ))
    (hfixed_step :
      ∀ n, ∀ᵐ lam ∂ρ,
        μ[fun ω => subGammaExponentialProcess X sigma2 b lam (n + 1) ω | ℱ n]
          ≤ᵐ[μ] fun ω => subGammaExponentialProcess X sigma2 b lam n ω) :
    ∀ n,
      condExp (ℱ n) μ (mixtureExponentialProcess X sigma2 b ρ (n + 1))
        ≤ᵐ[μ] mixtureExponentialProcess X sigma2 b ρ n := by
  intro n
  refine ae_le_of_forall_subalgebra_setIntegral_le (ℱ.le n)
    integrable_condExp (h_integrable_mix n) stronglyMeasurable_condExp
    (h_adapted_mix n) ?_
  intro s hs hμs
  have hs₀ : MeasurableSet s := ℱ.le n s hs
  have hnext_restrict := hM_int_next_restrict n hs₀ hμs
  have hcurrent_restrict := hM_int_current_restrict n hs₀ hμs
  have hnext_fiber :
      ∀ᵐ lam ∂ρ,
        Integrable (fun ω => subGammaExponentialProcess X sigma2 b lam (n + 1) ω) μ := by
    simpa using (hM_int_next n).prod_right_ae
  have hcurrent_fiber :
      ∀ᵐ lam ∂ρ,
        Integrable (fun ω => subGammaExponentialProcess X sigma2 b lam n ω) μ := by
    simpa using (hM_int_current n).prod_left_ae
  calc
    ∫ ω in s,
        (condExp (ℱ n) μ (mixtureExponentialProcess X sigma2 b ρ (n + 1))) ω ∂μ
        = ∫ ω in s, mixtureExponentialProcess X sigma2 b ρ (n + 1) ω ∂μ := by
            exact setIntegral_condExp (ℱ.le n) (h_integrable_mix (n + 1)) hs
    _ = ∫ lam,
          ∫ ω in s, subGammaExponentialProcess X sigma2 b lam (n + 1) ω ∂μ ∂ρ := by
            simpa [mixtureExponentialProcess, Function.uncurry] using
              (integral_integral_swap (μ := μ.restrict s) (ν := ρ)
                (f := fun ω lam => subGammaExponentialProcess X sigma2 b lam (n + 1) ω)
                hnext_restrict)
    _ ≤ ∫ lam,
          ∫ ω in s, subGammaExponentialProcess X sigma2 b lam n ω ∂μ ∂ρ := by
            refine integral_mono_ae hnext_restrict.integral_prod_right
              hcurrent_restrict.integral_prod_right ?_
            filter_upwards [hfixed_step n, hnext_fiber, hcurrent_fiber] with
              lam hstep hnext_int hcurrent_int
            calc
              ∫ ω in s, subGammaExponentialProcess X sigma2 b lam (n + 1) ω ∂μ
                  = ∫ ω in s,
                      (condExp (ℱ n) μ
                        (fun ω => subGammaExponentialProcess X sigma2 b lam (n + 1) ω)) ω ∂μ := by
                      exact (setIntegral_condExp (ℱ.le n) hnext_int hs).symm
              _ ≤ ∫ ω in s, subGammaExponentialProcess X sigma2 b lam n ω ∂μ := by
                      exact setIntegral_mono_ae integrable_condExp.integrableOn
                        hcurrent_int.integrableOn hstep
    _ = ∫ ω in s, mixtureExponentialProcess X sigma2 b ρ n ω ∂μ := by
            simpa [mixtureExponentialProcess, Function.uncurry] using
              (integral_integral_swap (μ := μ.restrict s) (ν := ρ)
                (f := fun ω lam => subGammaExponentialProcess X sigma2 b lam n ω)
                hcurrent_restrict).symm

/--
The mixture process is a nonnegative supermartingale once the conditional
expectation swap and the resulting integral one-step inequality are available.
-/
theorem mixture_is_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b : ℝ} {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hsupport : ∀ᵐ lam ∂ρ, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted_lam :
      ∀ lam, StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_adapted : StronglyAdapted ℱ (mixtureExponentialProcess X sigma2 b ρ))
    (h_integrable : ∀ n, Integrable (mixtureExponentialProcess X sigma2 b ρ n) μ)
    (hM_int :
      ∀ n, Integrable
        (fun p : ℝ × Ω => subGammaExponentialProcess X sigma2 b p.1 (n + 1) p.2)
        (ρ.prod μ))
    (hM_int_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 (n + 1) p.1)
          ((μ.restrict s).prod ρ))
    (hM_int_step :
      ∀ n, Integrable
        (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 n p.1)
        (μ.prod ρ))
    (hM_int_step_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
        (fun p : Ω × ℝ =>
          subGammaExponentialProcess X sigma2 b p.2 n p.1)
          ((μ.restrict s).prod ρ))
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    Supermartingale (mixtureExponentialProcess X sigma2 b ρ) ℱ μ
      ∧ ∀ n ω, 0 ≤ mixtureExponentialProcess X sigma2 b ρ n ω := by
  have hfixed_step :
      ∀ n, ∀ᵐ lam ∂ρ,
        μ[fun ω => subGammaExponentialProcess X sigma2 b lam (n + 1) ω | ℱ n]
          ≤ᵐ[μ] fun ω => subGammaExponentialProcess X sigma2 b lam n ω := by
    intro n
    filter_upwards [hsupport] with lam hlam
    have hlam_nonneg : 0 ≤ lam := hlam.1.le
    have hblam : b * lam < 3 := by
      have hmul : b * lam < b * (3 / b) := mul_lt_mul_of_pos_left hlam.2 hb
      have hb_ne : b ≠ 0 := ne_of_gt hb
      have hcancel : b * (3 / b) = 3 := by field_simp [hb_ne]
      linarith
    exact condSubGamma_supermartingale_step hb hσ hlam_nonneg hblam
      hX_meas hX_int (h_adapted_lam lam) hbound hcenter hvar n
  have h_cond_step :
      ∀ n,
        condExp (ℱ n) μ (mixtureExponentialProcess X sigma2 b ρ (n + 1))
          ≤ᵐ[μ] mixtureExponentialProcess X sigma2 b ρ n := by
    exact mixture_condExp_step_of_fixed_tilt_steps
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (ρ := ρ)
      h_adapted h_integrable hM_int hM_int_restrict hM_int_step hM_int_step_restrict
      hfixed_step
  refine ⟨supermartingale_nat h_adapted h_integrable h_cond_step, ?_⟩
  intro n ω
  exact integral_nonneg fun lam => (Real.exp_pos _).le

/-- Countable-time Ville bound for the mixture exponential process. -/
theorem atTop_time_uniform_confidence_sequence_subGamma_mixture
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {ρ : Measure ℝ}
    [IsProbabilityMeasure ρ]
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hsupport : ∀ᵐ lam ∂ρ, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted_lam :
      ∀ lam, StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_adapted_mix : StronglyAdapted ℱ (mixtureExponentialProcess X sigma2 b ρ))
    (h_integrable_mix : ∀ n, Integrable (mixtureExponentialProcess X sigma2 b ρ n) μ)
    (hM_int :
      ∀ n, Integrable
        (fun p : ℝ × Ω => subGammaExponentialProcess X sigma2 b p.1 (n + 1) p.2)
        (ρ.prod μ))
    (hM_int_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 (n + 1) p.1)
          ((μ.restrict s).prod ρ))
    (hM_int_step :
      ∀ n, Integrable
        (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 n p.1)
        (μ.prod ρ))
    (hM_int_step_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
        (fun p : Ω × ℝ =>
          subGammaExponentialProcess X sigma2 b p.2 n p.1)
          ((μ.restrict s).prod ρ))
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ mixtureExponentialProcess X sigma2 b ρ n ω} ≤ delta := by
  have hsup : Supermartingale (mixtureExponentialProcess X sigma2 b ρ) ℱ μ :=
    (mixture_is_supermartingale
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (ρ := ρ)
      hb hσ hsupport hX_meas hX_int h_adapted_lam h_adapted_mix h_integrable_mix
      hM_int hM_int_restrict hM_int_step hM_int_step_restrict hbound hcenter hvar).1
  have hnonneg : 0 ≤ mixtureExponentialProcess X sigma2 b ρ := by
    intro n ω
    exact integral_nonneg fun lam => (Real.exp_pos _).le
  have ha : 0 < 1 / delta := one_div_pos.mpr hδ
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ)
      (M := mixtureExponentialProcess X sigma2 b ρ)
      hsup hnonneg ha
  have hM0 : ∫ ω, mixtureExponentialProcess X sigma2 b ρ 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => mixtureExponentialProcess X sigma2 b ρ 0 ω) =ᵐ[μ] fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => by
        simp [mixtureExponentialProcess, subGammaExponentialProcess, runningSum]
    rw [integral_congr_ae hbody]
    simp [integral_const]
  rw [hM0] at hville
  have h_atTop :
      μ.real (atTopCrossingEvent (mixtureExponentialProcess X sigma2 b ρ) (1 / delta))
        ≤ delta := by
    calc
      μ.real (atTopCrossingEvent (mixtureExponentialProcess X sigma2 b ρ) (1 / delta))
          = delta *
            ((1 / delta) *
              μ.real
                (atTopCrossingEvent (mixtureExponentialProcess X sigma2 b ρ) (1 / delta))) := by
            field_simp [hδ.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
      _ = delta := by ring
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ mixtureExponentialProcess X sigma2 b ρ n ω}
        ⊆ atTopCrossingEvent (mixtureExponentialProcess X sigma2 b ρ) (1 / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn_pos, hn_cross⟩
    exact ⟨n, hn_cross⟩
  exact (measureReal_mono hsubset).trans h_atTop

/-!
## Discharging the measurability / integrability package for the uniform prior

The headline `atTop_time_uniform_confidence_sequence_subGamma_mixture` carries six
measurability / integrability obligations. For the concrete `uniformTiltPrior` (a probability
measure supported on the compact interval `[lam0, lam1]`) they are all discharged from the
increment model alone, with no free hypotheses:

* joint measurability of `(λ, ω) ↦ subGammaExponentialProcess λ n ω` in the product σ-algebra;
* the pointwise process bound `M ≤ exp (lam1 · n · b)` valid on the bounded-increment, admissible-tilt
  region, which yields product-integrability over `[lam0, lam1] × Ω` (and its restricted variants)
  via `Integrable.of_bound`, since the product of two finite measures is finite;
* adaptedness of each fixed-tilt process and of the prior integral, from adaptedness of `X`.
-/

/-- Joint measurability of the parameterized sub-Gamma exponential process in the product
σ-algebra, from measurability of each increment. -/
theorem measurable_subGammaExponentialProcess_prod {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (n : ℕ)
    (hX_meas : ∀ k, Measurable (X k)) :
    Measurable (fun p : ℝ × Ω => subGammaExponentialProcess X sigma2 b p.1 n p.2) := by
  unfold subGammaExponentialProcess runningSum subGammaCgf
  fun_prop (disch := intro i _; exact (hX_meas i).comp measurable_snd)

/-- Pointwise upper bound `M_n ≤ exp (lam1 · n · b)` on the fixed-tilt exponential process when the
increments are bounded (`|X_i ω| ≤ b` for `i < n`) and the tilt is admissible
(`0 ≤ lam ≤ lam1`, `b · lam < 3`). The negative cumulant term only helps, so it is dropped. -/
theorem subGammaExponentialProcess_le_of_bound {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam lam1 : ℝ) (n : ℕ) (ω : Ω)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ lam1) (hblam : b * lam < 3)
    (hbound : ∀ i ∈ Finset.range n, |X i ω| ≤ b) :
    subGammaExponentialProcess X sigma2 b lam n ω ≤ Real.exp (lam1 * (n : ℝ) * b) := by
  unfold subGammaExponentialProcess
  apply Real.exp_le_exp.2
  have hden : 0 < 2 * (1 - b * lam / 3) := by
    have : b * lam / 3 < 1 := by linarith
    linarith
  have hcgf_nonneg : 0 ≤ subGammaCgf sigma2 b lam := by
    unfold subGammaCgf
    apply div_nonneg
    · positivity
    · linarith
  have hsum_le : runningSum X n ω ≤ (n : ℝ) * b := by
    have hle : ∀ i ∈ Finset.range n, X i ω ≤ b := fun i hi => (abs_le.mp (hbound i hi)).2
    calc runningSum X n ω = Finset.sum (Finset.range n) (fun i => X i ω) := rfl
      _ ≤ Finset.sum (Finset.range n) (fun _ => b) := Finset.sum_le_sum hle
      _ = (n : ℝ) * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hlS : lam * runningSum X n ω ≤ lam * ((n : ℝ) * b) :=
    mul_le_mul_of_nonneg_left hsum_le hlam0
  have hlS2 : lam * ((n : ℝ) * b) ≤ lam1 * ((n : ℝ) * b) := by
    apply mul_le_mul_of_nonneg_right hlam1
    positivity
  have hcgf2 : 0 ≤ (n : ℝ) * subGammaCgf sigma2 b lam := by positivity
  nlinarith [hlS, hlS2, hcgf2]

/-- For the uniform prior, almost every tilt lies in the closed parameter interval. -/
theorem uniformTiltPrior_ae_mem_Icc {lam0 lam1 : ℝ} :
    ∀ᵐ lam ∂uniformTiltPrior lam0 lam1, lam ∈ Set.Icc lam0 lam1 := by
  unfold uniformTiltPrior
  exact ae_cond_mem measurableSet_Icc

/-- Product integrability for `subGammaExponentialProcess` under `(uniformTiltPrior …).prod μ`.
The integrand is a.e. bounded by `exp (lam1 · n · b)` and the product of two probability measures
is finite, so `Integrable.of_bound` applies. -/
theorem integrable_subGammaExponentialProcess_prod_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {sigma2 b lam0 lam1 : ℝ} (n : ℕ)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam1)
    (hlam1 : b * lam1 < 3)
    (hX_meas : ∀ k, Measurable (X k))
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b) :
    Integrable
      (fun p : ℝ × Ω => subGammaExponentialProcess X sigma2 b p.1 n p.2)
      ((uniformTiltPrior lam0 lam1).prod μ) := by
  haveI : IsProbabilityMeasure (uniformTiltPrior lam0 lam1) :=
    uniformTiltPrior_isProbabilityMeasure h01
  refine Integrable.of_bound ?_ (Real.exp (lam1 * (n : ℝ) * b)) ?_
  · exact (measurable_subGammaExponentialProcess_prod X sigma2 b n hX_meas).aestronglyMeasurable
  · have hlam_mem : ∀ᵐ p : ℝ × Ω ∂((uniformTiltPrior lam0 lam1).prod μ),
        p.1 ∈ Set.Icc lam0 lam1 :=
      (Measure.quasiMeasurePreserving_fst).ae uniformTiltPrior_ae_mem_Icc
    have hX : ∀ᵐ p : ℝ × Ω ∂((uniformTiltPrior lam0 lam1).prod μ),
        ∀ i ∈ Finset.range n, |X i p.2| ≤ b := by
      have h1 : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, |X i ω| ≤ b := by
        have hall : ∀ᵐ ω ∂μ, ∀ k, |X k ω| ≤ b := ae_all_iff.2 hbound
        filter_upwards [hall] with ω hω i _ using hω i
      exact (Measure.quasiMeasurePreserving_snd).ae h1
    filter_upwards [hlam_mem, hX] with p hp hpX
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold subGammaExponentialProcess; exact (Real.exp_pos _).le)]
    have hlam0' : 0 ≤ p.1 := hlam0.trans hp.1
    have hlam1' : p.1 ≤ lam1 := hp.2
    have hblam' : b * p.1 < 3 := by nlinarith [hp.2, hb]
    exact subGammaExponentialProcess_le_of_bound X sigma2 b p.1 lam1 n p.2
      hb hσ hlam0' hlam1' hblam' hpX

/-- Product integrability in the `Ω × ℝ` orientation under `ν.prod (uniformTiltPrior …)`, for any
finite measure `ν` on `Ω` carrying a `ν`-a.e. increment bound. This single statement covers both the
full measure (`ν = μ`) and the filtration-restricted measure (`ν = μ.restrict s`) variants the
supermartingale step needs. -/
theorem integrable_subGammaExponentialProcess_omegaProd_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {X : ℕ → Ω → ℝ} {sigma2 b lam0 lam1 : ℝ} (n : ℕ)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam1)
    (hlam1 : b * lam1 < 3)
    (hX_meas : ∀ k, Measurable (X k))
    (hbound : ∀ k, ∀ᵐ ω ∂ν, |X k ω| ≤ b) :
    Integrable
      (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 n p.1)
      (ν.prod (uniformTiltPrior lam0 lam1)) := by
  haveI : IsProbabilityMeasure (uniformTiltPrior lam0 lam1) :=
    uniformTiltPrior_isProbabilityMeasure h01
  refine Integrable.of_bound ?_ (Real.exp (lam1 * (n : ℝ) * b)) ?_
  · have hmeas : Measurable (fun p : Ω × ℝ => subGammaExponentialProcess X sigma2 b p.2 n p.1) := by
      unfold subGammaExponentialProcess runningSum subGammaCgf
      fun_prop (disch := intro i _; exact (hX_meas i).comp measurable_fst)
    exact hmeas.aestronglyMeasurable
  · have hlam_mem : ∀ᵐ p : Ω × ℝ ∂(ν.prod (uniformTiltPrior lam0 lam1)),
        p.2 ∈ Set.Icc lam0 lam1 :=
      (Measure.quasiMeasurePreserving_snd).ae uniformTiltPrior_ae_mem_Icc
    have hX : ∀ᵐ p : Ω × ℝ ∂(ν.prod (uniformTiltPrior lam0 lam1)),
        ∀ i ∈ Finset.range n, |X i p.1| ≤ b := by
      have h1 : ∀ᵐ ω ∂ν, ∀ i ∈ Finset.range n, |X i ω| ≤ b := by
        have hall : ∀ᵐ ω ∂ν, ∀ k, |X k ω| ≤ b := ae_all_iff.2 hbound
        filter_upwards [hall] with ω hω i _ using hω i
      exact (Measure.quasiMeasurePreserving_fst).ae h1
    filter_upwards [hlam_mem, hX] with p hp hpX
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold subGammaExponentialProcess; exact (Real.exp_pos _).le)]
    have hlam0' : 0 ≤ p.2 := hlam0.trans hp.1
    have hlam1' : p.2 ≤ lam1 := hp.2
    have hblam' : b * p.2 < 3 := by nlinarith [hp.2, hb]
    exact subGammaExponentialProcess_le_of_bound X sigma2 b p.2 lam1 n p.1
      hb hσ hlam0' hlam1' hblam' hpX

/--
**Predictable-increment (martingale-difference) adaptedness.**

The increment `X_k` is revealed at time `k + 1`, i.e. each `X_k` is `ℱ (k+1)`-strongly-measurable.
This is the correct admissibility for a martingale-difference sequence whose centering and
conditional variance are taken with respect to the past `ℱ k`: it lets `X_k` be a genuine
nonconstant increment while keeping `μ[X k | ℱ k] = 0` non-vacuous.

Conditioning the *present* (`StronglyAdapted ℱ X`, i.e. each `X_k` is `ℱ k`-measurable) together
with `μ[X k | ℱ k] = 0` would force `X_k =ᵐ 0` by `condExp_of_stronglyMeasurable`, leaving only the
zero process admissible. The `+1` shift is what avoids that collapse. The running sum `S_n`
remains `ℱ n`-measurable because it only involves `X_0, …, X_{n-1}`, each `ℱ n`-measurable since
`i < n ⟹ i + 1 ≤ n`. -/
def IncrementAdapted {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)

/-- Each fixed-tilt exponential process is `ℱ`-adapted once the increment process is
predictable-increment adapted (`X_k` is `ℱ (k+1)`-measurable). The running sum `S_n` is
`ℱ n`-measurable because it only involves `X_0, …, X_{n-1}` and `i < n ⟹ i + 1 ≤ n`. -/
theorem stronglyAdapted_subGammaExponentialProcess_of_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} (sigma2 b lam : ℝ)
    (hX_adapted : IncrementAdapted ℱ X) :
    StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam) := by
  intro n
  have hsum : StronglyMeasurable[ℱ n] (fun ω => runningSum X n ω) := by
    have hrw : (fun ω => runningSum X n ω) = ∑ i ∈ Finset.range n, X i := by
      funext ω; simp [runningSum, Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact (hX_adapted i).mono (ℱ.mono (Nat.succ_le_of_lt hi))
  have hbody : StronglyMeasurable[ℱ n]
      (fun ω => lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam) :=
    (hsum.const_mul lam).sub stronglyMeasurable_const
  exact Real.continuous_exp.comp_stronglyMeasurable hbody

/-- Joint strong-measurability of the parameterized process in the `ℱ n`-product σ-algebra, from
adaptedness of the increment process. This is the input to the integral-over-tilt adaptedness. -/
theorem stronglyMeasurable_filtration_prod_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} (sigma2 b : ℝ) (n : ℕ)
    (hX_adapted : IncrementAdapted ℱ X) :
    StronglyMeasurable[(ℱ n).prod (inferInstance : MeasurableSpace ℝ)]
      (Function.uncurry (fun ω lam => subGammaExponentialProcess X sigma2 b lam n ω)) := by
  rw [stronglyMeasurable_iff_measurable]
  unfold Function.uncurry subGammaExponentialProcess runningSum subGammaCgf
  have hXmeas : ∀ i ∈ Finset.range n,
      Measurable[(ℱ n).prod (inferInstance : MeasurableSpace ℝ)]
        (fun p : Ω × ℝ => X i p.1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hXi : Measurable[ℱ n] (X i) := by
      rw [← stronglyMeasurable_iff_measurable]
      exact (hX_adapted i).mono (ℱ.mono (Nat.succ_le_of_lt hi))
    exact hXi.comp measurable_fst
  apply Measurable.exp
  apply Measurable.sub
  · apply Measurable.mul
    · exact measurable_snd
    · exact Finset.measurable_sum _ hXmeas
  · apply Measurable.const_mul
    apply Measurable.div
    · apply Measurable.const_mul
      exact (measurable_snd.pow_const 2)
    · apply Measurable.const_mul
      apply Measurable.const_sub
      apply Measurable.div_const
      apply Measurable.const_mul
      exact measurable_snd

/-- The prior integral preserves `ℱ n`-strong-measurability, so the mixture process is adapted
to `ℱ` whenever the increment process is. -/
theorem stronglyAdapted_mixtureExponentialProcess_of_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} (sigma2 b : ℝ) (ρ : Measure ℝ) [SFinite ρ]
    (hX_adapted : IncrementAdapted ℱ X) :
    StronglyAdapted ℱ (mixtureExponentialProcess X sigma2 b ρ) := by
  intro n
  have hjoint := stronglyMeasurable_filtration_prod_subGamma (ℱ := ℱ) sigma2 b n hX_adapted
  show StronglyMeasurable[ℱ n]
    (fun ω => ∫ lam, subGammaExponentialProcess X sigma2 b lam n ω ∂ρ)
  letI : MeasurableSpace Ω := ℱ n
  exact MeasureTheory.StronglyMeasurable.integral_prod_right (ν := ρ) hjoint

/--
The mixture confidence sequence for the continuous uniform tilt prior, with **no free
measurability or integrability hypotheses**. The increment model on `X` is a genuine
martingale-difference sequence: each increment `X_k` is revealed at time `k + 1`
(`IncrementAdapted ℱ X`, i.e. `X_k` is `ℱ (k+1)`-strongly-measurable), is bounded `|X_k| ≤ b`,
is conditionally centered with respect to the **past** `μ[X_k | F_k] = 0`, and has conditional
second moment `μ[X_k² | F_k] ≤ σ²`. With an admissible compact tilt interval
`[lam0, lam1] ⊆ (0, 3/b)`, the prior-mixture exponential process is an anytime-valid confidence
sequence:

`μ.real {ω | ∃ n > 0, 1/δ ≤ ∫ lam, M_λ(n, ω) ∂Unif[lam0,lam1]} ≤ δ`.

The `+1` increment shift is essential for non-vacuity: pairing the *present*-conditioning
`StronglyAdapted ℱ X` with `μ[X_k | F_k] = 0` would force `X_k =ᵐ 0` (by
`condExp_of_stronglyMeasurable`), admitting only the zero process. With the shift the centering is
genuine and the running sum `S_n` is still `ℱ n`-measurable (it uses only `X_0, …, X_{n-1}`).

Every measurability / integrability obligation of
`atTop_time_uniform_confidence_sequence_subGamma_mixture` is discharged internally for the concrete
uniform prior: joint measurability from `hX_meas`, the four product-integrability conditions from the
process bound `M ≤ exp (lam1 · n · b)` via `Integrable.of_bound`, and both adaptedness conditions
from `hX_adapted`.
-/
theorem mixture_confidence_sequence_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta lam0 lam1 : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam0 : 0 < lam0) (h01 : lam0 < lam1) (hlam1 : lam1 < 3 / b)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ mixtureExponentialProcess X sigma2 b (uniformTiltPrior lam0 lam1) n ω}
        ≤ delta := by
  haveI : IsProbabilityMeasure (uniformTiltPrior lam0 lam1) :=
    uniformTiltPrior_isProbabilityMeasure h01
  -- The tilt interval lies in `(0, 3/b)`, hence `b · lam1 < 3` and `lam0 ≥ 0`.
  have hblam1 : b * lam1 < 3 := by
    have hmul : b * lam1 < b * (3 / b) := mul_lt_mul_of_pos_left hlam1 hb
    have hb_ne : b ≠ 0 := ne_of_gt hb
    have hcancel : b * (3 / b) = 3 := by field_simp [hb_ne]
    linarith
  have hsupport : ∀ᵐ lam ∂uniformTiltPrior lam0 lam1, lam ∈ Set.Ioo 0 (3 / b) :=
    uniformTiltPrior_valid_tilt_support hlam0 h01 hlam1
  refine atTop_time_uniform_confidence_sequence_subGamma_mixture
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (delta := delta)
    (ρ := uniformTiltPrior lam0 lam1)
    hδ hb hσ hsupport hX_meas hX_int
    (fun lam => stronglyAdapted_subGammaExponentialProcess_of_adapted sigma2 b lam hX_adapted)
    (stronglyAdapted_mixtureExponentialProcess_of_adapted sigma2 b _ hX_adapted)
    ?_ ?_ ?_ ?_ ?_ hbound hcenter hvar
  · -- h_integrable_mix
    intro n
    have hprod :=
      integrable_subGammaExponentialProcess_omegaProd_uniformPrior
        (ν := μ) (X := X) (sigma2 := sigma2) (b := b)
        (lam0 := lam0) (lam1 := lam1) n hb hσ hlam0.le h01 hblam1 hX_meas hbound
    change Integrable
      (fun ω => ∫ lam, subGammaExponentialProcess X sigma2 b lam n ω
        ∂uniformTiltPrior lam0 lam1) μ
    exact hprod.integral_prod_left
  · -- hM_int
    intro n
    exact integrable_subGammaExponentialProcess_prod_uniformPrior
      (μ := μ) (X := X) (sigma2 := sigma2) (b := b) (lam0 := lam0) (lam1 := lam1)
      (n + 1) hb hσ hlam0.le h01 hblam1 hX_meas hbound
  · -- hM_int_restrict
    intro n s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := by
      rw [isFiniteMeasure_restrict]; exact ne_of_lt hμs
    exact integrable_subGammaExponentialProcess_omegaProd_uniformPrior
      (ν := μ.restrict s) (X := X) (sigma2 := sigma2) (b := b)
      (lam0 := lam0) (lam1 := lam1) (n + 1) hb hσ hlam0.le h01 hblam1 hX_meas
      (fun k => ae_restrict_of_ae (hbound k))
  · -- hM_int_step
    intro n
    exact integrable_subGammaExponentialProcess_omegaProd_uniformPrior
      (ν := μ) (X := X) (sigma2 := sigma2) (b := b)
      (lam0 := lam0) (lam1 := lam1) n hb hσ hlam0.le h01 hblam1 hX_meas hbound
  · -- hM_int_step_restrict
    intro n s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := by
      rw [isFiniteMeasure_restrict]; exact ne_of_lt hμs
    exact integrable_subGammaExponentialProcess_omegaProd_uniformPrior
      (ν := μ.restrict s) (X := X) (sigma2 := sigma2) (b := b)
      (lam0 := lam0) (lam1 := lam1) n hb hσ hlam0.le h01 hblam1 hX_meas
      (fun k => ae_restrict_of_ae (hbound k))

end

end FormalSLT.AnytimeValid
