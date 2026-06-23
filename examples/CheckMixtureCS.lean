import FormalSLT.AnytimeValid.MixtureCS

open FormalSLT.AnytimeValid

#check mixtureExponentialProcess
#check condExp_mixture_swap
#check ae_le_of_forall_subalgebra_setIntegral_le
#check mixture_condExp_step_of_fixed_tilt_steps
#check mixture_is_supermartingale
#check atTop_time_uniform_confidence_sequence_subGamma_mixture
#check uniformTiltPrior
#check uniformTiltPrior_isProbabilityMeasure
#check uniformTiltPrior_valid_tilt_support
-- Discharged measurability / integrability package and the headline.
#check measurable_subGammaExponentialProcess_prod
#check subGammaExponentialProcess_le_of_bound
#check uniformTiltPrior_ae_mem_Icc
#check integrable_subGammaExponentialProcess_prod_uniformPrior
#check integrable_subGammaExponentialProcess_omegaProd_uniformPrior
#check stronglyAdapted_subGammaExponentialProcess_of_adapted
#check stronglyMeasurable_filtration_prod_subGamma
#check stronglyAdapted_mixtureExponentialProcess_of_adapted
#check mixture_confidence_sequence_uniformPrior

#print axioms condExp_mixture_swap
#print axioms mixture_is_supermartingale
#print axioms atTop_time_uniform_confidence_sequence_subGamma_mixture
#print axioms mixture_confidence_sequence_uniformPrior
#print axioms stronglyAdapted_mixtureExponentialProcess_of_adapted
#print axioms integrable_subGammaExponentialProcess_prod_uniformPrior

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
  exact atTop_time_uniform_confidence_sequence_subGamma_mixture
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (delta := delta)
    (ρ := ρ) hδ hb hσ hsupport hX_meas hX_int h_adapted_lam h_adapted_mix
    h_integrable_mix hM_int hM_int_restrict hM_int_step hM_int_step_restrict
    hbound hcenter hvar

-- The genuine non-vacuity witness for `mixture_confidence_sequence_uniformPrior` lives in
-- `examples/CheckAnytimeValidNonVacuityWitness.lean`: a nonzero `±1` Rademacher increment under the
-- corrected predictable-increment model (`IncrementAdapted ℱ X`, `X k` is `ℱ (k+1)`-measurable and
-- conditionally centered with respect to the past). It yields a real bound `μ.real {…} ≤ 1/2`.
--
-- The earlier witness here used the zero process. That was the *only* process admissible under the
-- former `StronglyAdapted ℱ X` hypothesis, since present-conditioning plus `μ[X k | ℱ k] = 0` forces
-- `X k =ᵐ 0` by `condExp_of_stronglyMeasurable`. The headline now requires `IncrementAdapted`, under
-- which a genuine nonzero increment is admissible.
#check @IncrementAdapted
