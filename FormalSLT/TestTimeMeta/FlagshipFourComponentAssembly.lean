/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipAnytimeValid

/-!
# Four-component flagship scalar assembly

This module extends the q092 simultaneous flagship assembly with the q093
anytime/Ville slot. The McAllester, online/IID, and Bernstein components are
the existing q092 worked instance. The fourth gap is the q095 finite-horizon
running-max boundary-event mass, and the fourth contribution is the matching
Ville tail.

## Scope

Assemble the four real scalar slots into the flagship certificate and expose
the anytime-valid event bound on the public theorem.

## Assumptions

The first three slots use the fixed q092 worked instance. The anytime slot uses
the same conditional sub-Gamma increment model as q095, with positive horizon
`n` stored as the certificate sample size.

## Current boundaries

This is finite-horizon anytime validity up to `n`. The prefix-kernel slot
remains zero in this rung.
-/

namespace FormalSLT.TestTimeMeta

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

noncomputable section

namespace FlagshipFourComponentAssembly

def mcAllesterGap : ℝ := FlagshipSimultaneousAssembly.mcAllesterGap

def onlineGap : ℝ := FlagshipSimultaneousAssembly.onlineGap

def gaussianBernsteinGap : ℝ := FlagshipSimultaneousAssembly.gaussianBernsteinGap

def empiricalRisk : ℝ := FlagshipSimultaneousAssembly.user.empiricalRisk

def anytimeGap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : ℝ :=
  μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t n)

def populationRisk : ℝ :=
  FlagshipSimultaneousAssembly.user.populationRisk

theorem populationRisk_nonnegative :
    0 ≤ populationRisk :=
  FlagshipSimultaneousAssembly.user.populationRiskNonnegative

def user (n : ℕ) (hn : 0 < n) :
    FlagshipUserSupplied where
  sampleSize := n
  targetConfidence := FlagshipSimultaneousAssembly.user.targetConfidence
  delta := FlagshipSimultaneousAssembly.user.delta
  lossWidth := FlagshipSimultaneousAssembly.user.lossWidth
  empiricalRisk := empiricalRisk
  populationRisk := populationRisk
  positiveSampleSize := hn
  deltaPositive := FlagshipSimultaneousAssembly.user.deltaPositive
  confidenceNonnegative := FlagshipSimultaneousAssembly.user.confidenceNonnegative
  lossWidthNonnegative := FlagshipSimultaneousAssembly.user.lossWidthNonnegative
  empiricalRiskNonnegative := FlagshipSimultaneousAssembly.user.empiricalRiskNonnegative
  populationRiskNonnegative := populationRisk_nonnegative

def derived (lam : ℝ) (n : ℕ) (t : ℝ) : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution :=
    FlagshipSimultaneousAssembly.derived.mcAllesterGeneralWidthContribution
  onlineIidContribution := FlagshipSimultaneousAssembly.derived.onlineIidContribution
  bernsteinOrGaussianContribution :=
    FlagshipSimultaneousAssembly.derived.bernsteinOrGaussianContribution
  anytimeVilleContribution := anytimeVilleTailContribution lam n t
  prefixKernelContribution := FlagshipSimultaneousAssembly.derived.prefixKernelContribution
  mcAllesterGeneralWidthContributionNonnegative :=
    FlagshipSimultaneousAssembly.derived.mcAllesterGeneralWidthContributionNonnegative
  onlineIidContributionNonnegative :=
    FlagshipSimultaneousAssembly.derived.onlineIidContributionNonnegative
  bernsteinOrGaussianContributionNonnegative :=
    FlagshipSimultaneousAssembly.derived.bernsteinOrGaussianContributionNonnegative
  anytimeVilleContributionNonnegative := by
    unfold anytimeVilleTailContribution
    exact (Real.exp_pos _).le
  prefixKernelContributionNonnegative :=
    FlagshipSimultaneousAssembly.derived.prefixKernelContributionNonnegative

/--
Four-slot population decomposition with the anytime gap carried as a
nonnegative risk slot.

The tight anytime event-mass certificate lives in the separate `anytimeUniform`
field consumed by the public four-component conclusion.
-/
theorem populationDecomposition_holds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) (hn : 0 < n) :
    (user n hn).populationRisk ≤
      (user n hn).empiricalRisk +
        mcAllesterGap +
        onlineGap +
        gaussianBernsteinGap +
        anytimeGap μ X sigma2 b lam t n +
        0 := by
  have hbase := FlagshipSimultaneousAssembly.populationDecomposition_holds
  have hanytime_nonnegative :
      0 ≤ μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t n) :=
    measureReal_nonneg
  unfold user populationRisk empiricalRisk mcAllesterGap onlineGap
    gaussianBernsteinGap anytimeGap
  dsimp
  linarith [hbase, hanytime_nonnegative]

end FlagshipFourComponentAssembly

/-- The four assembled non-prefix contribution slots are strictly positive. -/
theorem flagshipFourComponent_four_slots_positive (lam : ℝ) (n : ℕ) (t : ℝ) :
    0 <
        (FlagshipFourComponentAssembly.derived lam n t).mcAllesterGeneralWidthContribution ∧
      0 < (FlagshipFourComponentAssembly.derived lam n t).onlineIidContribution ∧
      0 <
        (FlagshipFourComponentAssembly.derived lam n t).bernsteinOrGaussianContribution ∧
      0 < (FlagshipFourComponentAssembly.derived lam n t).anytimeVilleContribution := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < FlagshipSimultaneousAssembly.derived.mcAllesterGeneralWidthContribution
    unfold FlagshipSimultaneousAssembly.derived
    exact FlagshipSimultaneousAssembly.mcAllesterContribution_pos
  · change 0 < FlagshipSimultaneousAssembly.derived.onlineIidContribution
    unfold FlagshipSimultaneousAssembly.derived
    exact FlagshipSimultaneousAssembly.onlineContribution_pos
  · change 0 < FlagshipSimultaneousAssembly.derived.bernsteinOrGaussianContribution
    unfold FlagshipSimultaneousAssembly.derived
    exact FlagshipSimultaneousAssembly.bernsteinContribution_pos
  · unfold FlagshipFourComponentAssembly.derived anytimeVilleTailContribution
    exact Real.exp_pos _

/--
Scalar bounds for the q092 three-slot worked instance plus the q093
increment-model anytime/Ville slot.
-/
theorem flagshipFourComponent_scalarBounds_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    FlagshipScalarComponentBounds
      (FlagshipFourComponentAssembly.user n hn)
      (FlagshipFourComponentAssembly.derived lam n t)
      FlagshipFourComponentAssembly.mcAllesterGap
      FlagshipFourComponentAssembly.onlineGap
      FlagshipFourComponentAssembly.gaussianBernsteinGap
      (FlagshipFourComponentAssembly.anytimeGap μ X sigma2 b lam t n)
      0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FlagshipFourComponentAssembly.populationDecomposition_holds
      μ X sigma2 b lam t n hn
  · simpa [
      FlagshipFourComponentAssembly.user,
      FlagshipFourComponentAssembly.derived,
      FlagshipFourComponentAssembly.mcAllesterGap] using
      flagshipSimultaneous_scalarBounds.mcAllesterGap_le
  · simpa [
      FlagshipFourComponentAssembly.derived,
      FlagshipFourComponentAssembly.onlineGap] using
      flagshipSimultaneous_scalarBounds.onlineGap_le
  · simpa [
      FlagshipFourComponentAssembly.derived,
      FlagshipFourComponentAssembly.gaussianBernsteinGap] using
      flagshipSimultaneous_scalarBounds.gaussianBernsteinGap_le
  · simpa [
      FlagshipFourComponentAssembly.anytimeGap,
      FlagshipFourComponentAssembly.derived] using
      flagshipAnytimeUniformBoundaryMass_le_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (horizon := n)
        hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar
  · simpa [FlagshipFourComponentAssembly.derived] using
      FlagshipSimultaneousAssembly.derived.prefixKernelContributionNonnegative

/--
The four-component flagship assembled bound, obtained from scalar component
inequalities rather than an externally supplied certificate.
-/
theorem flagshipFourComponent_population_le_bound_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    (FlagshipFourComponentAssembly.user n hn).populationRisk ≤
      flagshipBound
        (FlagshipFourComponentAssembly.user n hn)
        (FlagshipFourComponentAssembly.derived lam n t) := by
  exact flagshipScalarAssembly_from_componentInequalities
    (FlagshipFourComponentAssembly.user n hn)
    (FlagshipFourComponentAssembly.derived lam n t)
    (flagshipFourComponent_scalarBounds_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)

/-- Certificate object for the four-component flagship assembly. -/
def flagshipFourComponent_certificate_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    FlagshipCertificate where
  user := FlagshipFourComponentAssembly.user n hn
  derived := FlagshipFourComponentAssembly.derived lam n t
  assembledBound :=
    flagshipFourComponent_population_le_bound_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

/--
The public four-component conclusion: the flagship population-risk certificate
plus the finite-horizon anytime-valid event certificate.
-/
structure FlagshipFourComponentConclusion {Ω : Type*} [MeasurableSpace Ω]
    (certificate : FlagshipCertificate)
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : Prop where
  flagship : flagshipConclusion certificate
  anytimeUniform :
    μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t n)
      ≤ anytimeVilleTailContribution lam n t

/-- The reviewer-facing flagship conclusion for the four-component assembly. -/
theorem flagshipFourComponent_conclusion_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    FlagshipFourComponentConclusion
      (flagshipFourComponent_certificate_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (n := n)
        hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)
      μ X sigma2 b lam t n := by
  refine ⟨?_, ?_⟩
  · exact pacBayesTestTimeFlagship_theorem
      (flagshipFourComponent_certificate_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (n := n)
        hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)
  · exact flagshipAnytimeUniformBoundaryMass_le_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (horizon := n)
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

end

end FormalSLT.TestTimeMeta
