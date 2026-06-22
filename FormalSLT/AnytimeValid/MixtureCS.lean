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

end

end FormalSLT.AnytimeValid
