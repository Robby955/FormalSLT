/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.AtTopCS
import Mathlib.MeasureTheory.Integral.Prod

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
    (hCE_int_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ =>
            (condExp (ℱ n) μ
              (fun ω => subGammaExponentialProcess X sigma2 b p.2 (n + 1) ω)) p.1)
          ((μ.restrict s).prod ρ))
    (hCE_int_step :
      ∀ n, Integrable
        (fun p : Ω × ℝ =>
          (condExp (ℱ n) μ
            (fun ω => subGammaExponentialProcess X sigma2 b p.2 (n + 1) ω)) p.1)
        (μ.prod ρ))
    (hCE_meas :
      ∀ n, @AEStronglyMeasurable Ω ℝ _ (ℱ n) mΩ
        (fun ω => ∫ lam,
          (condExp (ℱ n) μ
            (fun ω' => subGammaExponentialProcess X sigma2 b lam (n + 1) ω')) ω ∂ρ) μ)
    (hstep_meas :
      ∀ n, MeasurableSet
        {p : Ω × ℝ |
          (condExp (ℱ n) μ
            (fun ω => subGammaExponentialProcess X sigma2 b p.2 (n + 1) ω)) p.1 ≤
          subGammaExponentialProcess X sigma2 b p.2 n p.1})
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    Supermartingale (mixtureExponentialProcess X sigma2 b ρ) ℱ μ
      ∧ ∀ n ω, 0 ≤ mixtureExponentialProcess X sigma2 b ρ n ω := by
  have h_integral_step :
      ∀ n, Filter.Eventually
        (fun ω =>
          (∫ lam,
            (condExp (ℱ n) μ
              (fun ω' => subGammaExponentialProcess X sigma2 b lam (n + 1) ω')) ω ∂ρ)
            ≤ mixtureExponentialProcess X sigma2 b ρ n ω)
        (ae μ) := by
    intro n
    have hstep_lam :
        ∀ᵐ lam ∂ρ,
          μ[fun ω => subGammaExponentialProcess X sigma2 b lam (n + 1) ω | ℱ n]
            ≤ᵐ[μ] fun ω => subGammaExponentialProcess X sigma2 b lam n ω := by
      filter_upwards [hsupport] with lam hlam
      have hlam_nonneg : 0 ≤ lam := hlam.1.le
      have hblam : b * lam < 3 := by
        have hmul : b * lam < b * (3 / b) := mul_lt_mul_of_pos_left hlam.2 hb
        have hb_ne : b ≠ 0 := ne_of_gt hb
        have hcancel : b * (3 / b) = 3 := by field_simp [hb_ne]
        linarith
      exact condSubGamma_supermartingale_step hb hσ hlam_nonneg hblam
        hX_meas hX_int (h_adapted_lam lam) hbound hcenter hvar n
    have hstep_comm :
        ∀ᵐ ω ∂μ, ∀ᵐ lam ∂ρ,
          (condExp (ℱ n) μ
            (fun ω' => subGammaExponentialProcess X sigma2 b lam (n + 1) ω')) ω
            ≤ subGammaExponentialProcess X sigma2 b lam n ω := by
      exact (Measure.ae_ae_comm (μ := μ) (ν := ρ)
        (p := fun ω lam =>
          (condExp (ℱ n) μ
            (fun ω' => subGammaExponentialProcess X sigma2 b lam (n + 1) ω')) ω
            ≤ subGammaExponentialProcess X sigma2 b lam n ω)
        (hstep_meas n)).2 hstep_lam
    filter_upwards [hstep_comm, (hCE_int_step n).prod_right_ae,
      (hM_int_step n).prod_right_ae] with ω hstepω hCEω hMω
    exact integral_mono_ae hCEω hMω hstepω
  have h_cond_step :
      ∀ n,
        condExp (ℱ n) μ (mixtureExponentialProcess X sigma2 b ρ (n + 1))
          ≤ᵐ[μ] mixtureExponentialProcess X sigma2 b ρ n := by
    intro n
    have hswap :=
      condExp_mixture_swap
        (hm := ℱ.le n) (ρ := ρ)
        (M := fun lam k ω => subGammaExponentialProcess X sigma2 b lam k ω)
        (n := n)
        (hM_int n) (hM_int_restrict n) (hCE_int_restrict n) (hCE_meas n)
    filter_upwards [hswap, h_integral_step n] with ω hswapω hstepω
    simpa [mixtureExponentialProcess] using hswapω.le.trans hstepω
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
    (hCE_int_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ =>
            (condExp (ℱ n) μ
              (fun ω => subGammaExponentialProcess X sigma2 b p.2 (n + 1) ω)) p.1)
          ((μ.restrict s).prod ρ))
    (hCE_int_step :
      ∀ n, Integrable
        (fun p : Ω × ℝ =>
          (condExp (ℱ n) μ
            (fun ω => subGammaExponentialProcess X sigma2 b p.2 (n + 1) ω)) p.1)
        (μ.prod ρ))
    (hCE_meas :
      ∀ n, @AEStronglyMeasurable Ω ℝ _ (ℱ n) mΩ
        (fun ω => ∫ lam,
          (condExp (ℱ n) μ
            (fun ω' => subGammaExponentialProcess X sigma2 b lam (n + 1) ω')) ω ∂ρ) μ)
    (hstep_meas :
      ∀ n, MeasurableSet
        {p : Ω × ℝ |
          (condExp (ℱ n) μ
            (fun ω => subGammaExponentialProcess X sigma2 b p.2 (n + 1) ω)) p.1 ≤
          subGammaExponentialProcess X sigma2 b p.2 n p.1})
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ mixtureExponentialProcess X sigma2 b ρ n ω} ≤ delta := by
  have hsup : Supermartingale (mixtureExponentialProcess X sigma2 b ρ) ℱ μ :=
    (mixture_is_supermartingale
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (ρ := ρ)
      hb hσ hsupport hX_meas hX_int h_adapted_lam h_adapted_mix h_integrable_mix
      hM_int hM_int_restrict hM_int_step hCE_int_restrict hCE_int_step hCE_meas
      hstep_meas hbound hcenter hvar).1
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
