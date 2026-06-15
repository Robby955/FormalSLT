/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.AnytimeVillePopulationDecomposition
import FormalSLT.TestTimeMeta.FlagshipSimultaneousAssembly

/-!
# Four-component flagship scalar assembly

This module extends the q092 simultaneous flagship assembly with the q093
anytime/Ville slot.  The McAllester, online/IID, and Bernstein components are
the existing q092 worked instance.  The fourth gap is the q093 boundary-event
mass, and the fourth contribution is the fixed-horizon Ville tail.

Scope: assemble the four real scalar slots into the flagship certificate.
Out of scope: the prefix-kernel slot, which remains zero in this rung.
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
  anytimeVilleBoundaryMass μ X sigma2 b lam t n

def populationRisk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : ℝ :=
  FlagshipSimultaneousAssembly.user.populationRisk +
    anytimeGap μ X sigma2 b lam t n

theorem populationRisk_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) :
    0 ≤ populationRisk μ X sigma2 b lam t n := by
  unfold populationRisk anytimeGap anytimeVilleBoundaryMass
  exact add_nonneg
    FlagshipSimultaneousAssembly.user.populationRiskNonnegative
    measureReal_nonneg

def user {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) :
    FlagshipUserSupplied where
  sampleSize := FlagshipSimultaneousAssembly.user.sampleSize
  targetConfidence := FlagshipSimultaneousAssembly.user.targetConfidence
  delta := FlagshipSimultaneousAssembly.user.delta
  lossWidth := FlagshipSimultaneousAssembly.user.lossWidth
  empiricalRisk := empiricalRisk
  populationRisk := populationRisk μ X sigma2 b lam t n
  positiveSampleSize := FlagshipSimultaneousAssembly.user.positiveSampleSize
  deltaPositive := FlagshipSimultaneousAssembly.user.deltaPositive
  confidenceNonnegative := FlagshipSimultaneousAssembly.user.confidenceNonnegative
  lossWidthNonnegative := FlagshipSimultaneousAssembly.user.lossWidthNonnegative
  empiricalRiskNonnegative := FlagshipSimultaneousAssembly.user.empiricalRiskNonnegative
  populationRiskNonnegative := populationRisk_nonnegative μ X sigma2 b lam t n

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

theorem populationDecomposition_holds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) :
    (user μ X sigma2 b lam t n).populationRisk ≤
      (user μ X sigma2 b lam t n).empiricalRisk +
        mcAllesterGap +
        onlineGap +
        gaussianBernsteinGap +
        anytimeGap μ X sigma2 b lam t n +
        0 := by
  have hbase := FlagshipSimultaneousAssembly.populationDecomposition_holds
  unfold user populationRisk empiricalRisk mcAllesterGap onlineGap
    gaussianBernsteinGap anytimeGap
  dsimp
  linarith [hbase]

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
  · simpa [FlagshipFourComponentAssembly.derived] using
      FlagshipSimultaneousAssembly.mcAllesterContribution_pos
  · simpa [FlagshipFourComponentAssembly.derived] using
      FlagshipSimultaneousAssembly.onlineContribution_pos
  · simpa [FlagshipFourComponentAssembly.derived] using
      FlagshipSimultaneousAssembly.bernsteinContribution_pos
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
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    FlagshipScalarComponentBounds
      (FlagshipFourComponentAssembly.user μ X sigma2 b lam t n)
      (FlagshipFourComponentAssembly.derived lam n t)
      FlagshipFourComponentAssembly.mcAllesterGap
      FlagshipFourComponentAssembly.onlineGap
      FlagshipFourComponentAssembly.gaussianBernsteinGap
      (FlagshipFourComponentAssembly.anytimeGap μ X sigma2 b lam t n)
      0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FlagshipFourComponentAssembly.populationDecomposition_holds
      μ X sigma2 b lam t n
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
      anytimeVilleContribution_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (n := n)
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
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    (FlagshipFourComponentAssembly.user μ X sigma2 b lam t n).populationRisk ≤
      flagshipBound
        (FlagshipFourComponentAssembly.user μ X sigma2 b lam t n)
        (FlagshipFourComponentAssembly.derived lam n t) := by
  exact flagshipScalarAssembly_from_componentInequalities
    (FlagshipFourComponentAssembly.user μ X sigma2 b lam t n)
    (FlagshipFourComponentAssembly.derived lam n t)
    (flagshipFourComponent_scalarBounds_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)

/-- Certificate object for the four-component flagship assembly. -/
def flagshipFourComponent_certificate_from_incrementModel
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
    FlagshipCertificate where
  user := FlagshipFourComponentAssembly.user μ X sigma2 b lam t n
  derived := FlagshipFourComponentAssembly.derived lam n t
  assembledBound :=
    flagshipFourComponent_population_le_bound_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

/-- The reviewer-facing flagship conclusion for the four-component assembly. -/
theorem flagshipFourComponent_conclusion_from_incrementModel
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
    flagshipConclusion
      (flagshipFourComponent_certificate_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (n := n)
        hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar) :=
  pacBayesTestTimeFlagship_theorem
    (flagshipFourComponent_certificate_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)

end

end FormalSLT.TestTimeMeta
