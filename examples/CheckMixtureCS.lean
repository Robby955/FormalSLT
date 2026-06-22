import FormalSLT.AnytimeValid.MixtureCS

open FormalSLT.AnytimeValid

#check mixtureExponentialProcess
#check condExp_mixture_swap
#check mixture_is_supermartingale
#check atTop_time_uniform_confidence_sequence_subGamma_mixture

#print axioms condExp_mixture_swap
#print axioms mixture_is_supermartingale
#print axioms atTop_time_uniform_confidence_sequence_subGamma_mixture

open MeasureTheory ProbabilityTheory

example
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
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
  exact atTop_time_uniform_confidence_sequence_subGamma_mixture
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (delta := delta)
    (ρ := ρ) hδ hb hσ hsupport hX_meas hX_int h_adapted_lam h_adapted_mix
    h_integrable_mix hM_int hM_int_restrict hM_int_step hCE_int_restrict hCE_int_step
    hCE_meas hstep_meas hbound hcenter hvar
