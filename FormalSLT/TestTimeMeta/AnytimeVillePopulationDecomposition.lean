/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipComposition

/-!
# Anytime/Ville population-decomposition slot

This module discharges the q063/q092 anytime/Ville scalar slot as a standalone
component. It connects the flagship scalar assembly to the existing
`AnytimeValid.SubGaussianCS` endpoint:

* the event mass is the real probability of the sub-Gamma running-mean boundary;
* the component contribution is the canonical fixed-horizon Ville tail
  `exp (-lambda * n * t)`;
* the population-risk bound follows from the scalar flagship assembly once the
  caller supplies the decomposition using that event mass as the anytime gap.

Scope: this is only the single anytime/Ville slot.
Out of scope: no four-component q094 assembly and no prefix-kernel route.
-/

namespace FormalSLT.TestTimeMeta

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

noncomputable section

/-- Boundary event controlled by the fixed-horizon sub-Gamma Ville bound. -/
def anytimeVilleBoundaryEvent {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : Set Ω :=
  {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}

/-- Scalar mass of the anytime/Ville boundary event. -/
def anytimeVilleBoundaryMass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : ℝ :=
  μ.real (anytimeVilleBoundaryEvent X sigma2 b lam t n)

/--
Discharge the flagship anytime contribution from the conditional sub-Gamma
increment model.
-/
theorem anytimeVilleContribution_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    anytimeVilleBoundaryMass μ X sigma2 b lam t n ≤
      anytimeVilleTailContribution lam n t := by
  dsimp [anytimeVilleBoundaryMass, anytimeVilleBoundaryEvent,
    anytimeVilleTailContribution]
  exact ville_inequality_subGamma_running_mean_of_increment_model
    hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

/--
Package the discharged anytime contribution into the flagship scalar component
bound structure, with the other component gaps set to zero.
-/
theorem anytimeVilleScalarBounds_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (user : FlagshipUserSupplied) (derived : FlagshipDerivedContributions)
    (hderived_anytime :
      derived.anytimeVilleContribution = anytimeVilleTailContribution lam n t)
    (hpopulation :
      user.populationRisk ≤
        user.empiricalRisk + anytimeVilleBoundaryMass μ X sigma2 b lam t n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    FlagshipScalarComponentBounds user derived 0 0 0
      (anytimeVilleBoundaryMass μ X sigma2 b lam t n) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · simpa using
      mul_nonneg user.lossWidthNonnegative
        derived.mcAllesterGeneralWidthContributionNonnegative
  · exact derived.onlineIidContributionNonnegative
  · exact derived.bernsteinOrGaussianContributionNonnegative
  · rw [hderived_anytime]
    exact anytimeVilleContribution_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar
  · exact derived.prefixKernelContributionNonnegative

/--
Assemble the single discharged anytime/Ville slot into the flagship population
risk bound.
-/
theorem anytimeVilleFlagship_population_le_bound_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (user : FlagshipUserSupplied) (derived : FlagshipDerivedContributions)
    (hderived_anytime :
      derived.anytimeVilleContribution = anytimeVilleTailContribution lam n t)
    (hpopulation :
      user.populationRisk ≤
        user.empiricalRisk + anytimeVilleBoundaryMass μ X sigma2 b lam t n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    user.populationRisk ≤ flagshipBound user derived := by
  exact flagshipScalarAssembly_from_componentInequalities user derived
    (anytimeVilleScalarBounds_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      user derived hderived_anytime hpopulation
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)

end

end FormalSLT.TestTimeMeta
