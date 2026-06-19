/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipFourComponentAssembly
import FormalSLT.TestTimeMeta.PrefixKernelPopulationDecomposition

/-!
# Five-component flagship scalar assembly

This module fills the last zero slot of the flagship assembly. The four-component
rung (`FlagshipFourComponentAssembly`) certifies the McAllester, online/IID,
Bernstein, and anytime/Ville gaps simultaneously but leaves the prefix-kernel
slot at zero. Here the prefix-kernel slot is filled with the genuine
sharp-McDiarmid lower-tail deviation radius produced through the prefix/tail
conditional-kernel disintegration, so all five flagship gaps are non-vacuous in a
single shared certificate.

## Construction

The shared instance sums two real worked instances, the same way
`FlagshipSimultaneousAssembly` sums its three component instances:

* the four-component shared instance, whose population risk decomposes into the
  McAllester, online, Bernstein, and Ville gaps;
* `PrefixKernelDecompWorkedExample`, whose population risk is a genuine integral
  average over the homogeneous Dirac product and whose only gap is the
  sharp-McDiarmid deviation radius.

The total population risk is the sum of the two real population risks, the total
empirical risk is the sum of the two empirical risks, and the prefix-kernel gap is
the real deviation radius. No `R ≤ Rhat + penalty` hypothesis is threaded through
the statement: every gap is the conclusion of a component inequality.

## Non-vacuity

`flagshipFiveComponent_five_slots_positive` shows all five derived contributions
are strictly positive at the worked instance, and `flagshipFiveComponent_*` route
the assembled bound through `flagshipScalarAssembly_from_componentInequalities`
and the reviewer-facing flagship theorem.

## Current boundaries

The first four slots inherit the finite-horizon anytime model of the
four-component rung. The prefix-kernel slot is finite-sample
(`n = 1` worked statistic). This is the full five-slot simultaneous rung, not an
infinite-time confidence sequence.

Sources for this lane: McDiarmid 1989; Boucheron-Lugosi-Massart 2013 §6; the
component sources cited in the four-component and prefix-kernel modules.
-/

namespace FormalSLT.TestTimeMeta

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

noncomputable section

namespace FlagshipFiveComponentAssembly

/-- McAllester gap inherited from the four-component shared instance. -/
def mcAllesterGap : ℝ := FlagshipFourComponentAssembly.mcAllesterGap

/-- Online/IID gap inherited from the four-component shared instance. -/
def onlineGap : ℝ := FlagshipFourComponentAssembly.onlineGap

/-- Bernstein/Gaussian gap inherited from the four-component shared instance. -/
def gaussianBernsteinGap : ℝ := FlagshipFourComponentAssembly.gaussianBernsteinGap

/-- Anytime/Ville gap: the finite-horizon running-max boundary-event mass. -/
def anytimeGap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : ℝ :=
  FlagshipFourComponentAssembly.anytimeGap μ X sigma2 b lam t n

/-- Prefix-kernel gap: the real sharp-McDiarmid deviation radius. -/
def prefixGap : ℝ := PrefixKernelDecompWorkedExample.deviationRadius

/-- Total empirical risk: four-component empirical risk plus prefix-kernel empirical risk. -/
def empiricalRisk : ℝ :=
  FlagshipFourComponentAssembly.empiricalRisk +
    PrefixKernelDecompWorkedExample.empiricalRisk

/-- Total population risk: four-component population risk plus prefix-kernel
population risk. Both summands are genuine integral averages. -/
def populationRisk : ℝ :=
  FlagshipFourComponentAssembly.populationRisk +
    PrefixKernelDecompWorkedExample.populationRisk

theorem populationRisk_nonnegative : 0 ≤ populationRisk := by
  unfold populationRisk
  have h1 := FlagshipFourComponentAssembly.populationRisk_nonnegative
  have h2 :
      0 ≤ PrefixKernelDecompWorkedExample.populationRisk := by
    rw [PrefixKernelDecompWorkedExample.populationRisk_eq]; norm_num
  linarith

theorem empiricalRisk_nonnegative : 0 ≤ empiricalRisk := by
  unfold empiricalRisk
  have h1 : 0 ≤ FlagshipFourComponentAssembly.empiricalRisk :=
    FlagshipSimultaneousAssembly.empiricalRisk_nonnegative
  have h2 :
      0 ≤ PrefixKernelDecompWorkedExample.empiricalRisk := by
    rw [PrefixKernelDecompWorkedExample.empiricalRisk_eq]; norm_num
  linarith

/-- Shared user inputs for the five-component instance. -/
def user (n : ℕ) (hn : 0 < n) : FlagshipUserSupplied where
  sampleSize := n
  targetConfidence := (FlagshipFourComponentAssembly.user n hn).targetConfidence
  delta := (FlagshipFourComponentAssembly.user n hn).delta
  lossWidth := (FlagshipFourComponentAssembly.user n hn).lossWidth
  empiricalRisk := empiricalRisk
  populationRisk := populationRisk
  positiveSampleSize := hn
  deltaPositive := (FlagshipFourComponentAssembly.user n hn).deltaPositive
  confidenceNonnegative := (FlagshipFourComponentAssembly.user n hn).confidenceNonnegative
  lossWidthNonnegative := (FlagshipFourComponentAssembly.user n hn).lossWidthNonnegative
  empiricalRiskNonnegative := empiricalRisk_nonnegative
  populationRiskNonnegative := populationRisk_nonnegative

/-- Shared derived contributions with all five slots filled by real quantities. -/
def derived (lam : ℝ) (n : ℕ) (t : ℝ) : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution :=
    (FlagshipFourComponentAssembly.derived lam n t).mcAllesterGeneralWidthContribution
  onlineIidContribution :=
    (FlagshipFourComponentAssembly.derived lam n t).onlineIidContribution
  bernsteinOrGaussianContribution :=
    (FlagshipFourComponentAssembly.derived lam n t).bernsteinOrGaussianContribution
  anytimeVilleContribution :=
    (FlagshipFourComponentAssembly.derived lam n t).anytimeVilleContribution
  prefixKernelContribution := prefixGap
  mcAllesterGeneralWidthContributionNonnegative :=
    (FlagshipFourComponentAssembly.derived lam n t).mcAllesterGeneralWidthContributionNonnegative
  onlineIidContributionNonnegative :=
    (FlagshipFourComponentAssembly.derived lam n t).onlineIidContributionNonnegative
  bernsteinOrGaussianContributionNonnegative :=
    (FlagshipFourComponentAssembly.derived lam n t).bernsteinOrGaussianContributionNonnegative
  anytimeVilleContributionNonnegative :=
    (FlagshipFourComponentAssembly.derived lam n t).anytimeVilleContributionNonnegative
  prefixKernelContributionNonnegative := by
    unfold prefixGap; norm_num [PrefixKernelDecompWorkedExample.deviationRadius]

/--
The five-slot population-risk decomposition.

The total population risk is bounded by the total empirical risk plus the four
inherited gaps plus the real prefix-kernel deviation radius. The four-component
inequality controls the four-component summand; the prefix-kernel worked example
controls the prefix-kernel summand.
-/
theorem populationDecomposition_holds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) (hn : 0 < n) :
    (user n hn).populationRisk ≤
      (user n hn).empiricalRisk +
        mcAllesterGap +
        onlineGap +
        gaussianBernsteinGap +
        anytimeGap μ X sigma2 b lam t n +
        prefixGap := by
  have hfour := FlagshipFourComponentAssembly.populationDecomposition_holds
    μ X sigma2 b lam t n hn
  have hprefix := PrefixKernelDecompWorkedExample.populationDecomposition_holds
  have hprefix' :
      PrefixKernelDecompWorkedExample.populationRisk ≤
        PrefixKernelDecompWorkedExample.empiricalRisk + prefixGap := by
    unfold prefixGap
    simpa [add_assoc] using hprefix
  have hfour' :
      FlagshipFourComponentAssembly.populationRisk ≤
        FlagshipFourComponentAssembly.empiricalRisk +
          mcAllesterGap + onlineGap + gaussianBernsteinGap +
          anytimeGap μ X sigma2 b lam t n := by
    simpa [FlagshipFourComponentAssembly.user, mcAllesterGap, onlineGap,
      gaussianBernsteinGap, anytimeGap, add_assoc] using hfour
  unfold user populationRisk empiricalRisk
  dsimp
  linarith [hfour', hprefix']

end FlagshipFiveComponentAssembly

/-- All five derived flagship contributions are strictly positive at the worked instance. -/
theorem flagshipFiveComponent_five_slots_positive (lam : ℝ) (n : ℕ) (t : ℝ) :
    0 < (FlagshipFiveComponentAssembly.derived lam n t).mcAllesterGeneralWidthContribution ∧
      0 < (FlagshipFiveComponentAssembly.derived lam n t).onlineIidContribution ∧
      0 < (FlagshipFiveComponentAssembly.derived lam n t).bernsteinOrGaussianContribution ∧
      0 < (FlagshipFiveComponentAssembly.derived lam n t).anytimeVilleContribution ∧
      0 < (FlagshipFiveComponentAssembly.derived lam n t).prefixKernelContribution := by
  obtain ⟨hmc, honline, hbern, hville⟩ := flagshipFourComponent_four_slots_positive lam n t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [FlagshipFiveComponentAssembly.derived] using hmc
  · simpa [FlagshipFiveComponentAssembly.derived] using honline
  · simpa [FlagshipFiveComponentAssembly.derived] using hbern
  · simpa [FlagshipFiveComponentAssembly.derived] using hville
  · unfold FlagshipFiveComponentAssembly.derived FlagshipFiveComponentAssembly.prefixGap
    norm_num [PrefixKernelDecompWorkedExample.deviationRadius]

/--
Scalar component bounds for the five-slot shared instance: every gap is bounded by
its matching derived contribution, and the population decomposition is the
five-term inequality assembled from the four-component and prefix-kernel routes.
-/
theorem flagshipFiveComponent_scalarBounds_from_incrementModel
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
      (FlagshipFiveComponentAssembly.user n hn)
      (FlagshipFiveComponentAssembly.derived lam n t)
      FlagshipFiveComponentAssembly.mcAllesterGap
      FlagshipFiveComponentAssembly.onlineGap
      FlagshipFiveComponentAssembly.gaussianBernsteinGap
      (FlagshipFiveComponentAssembly.anytimeGap μ X sigma2 b lam t n)
      FlagshipFiveComponentAssembly.prefixGap := by
  have hfour := flagshipFourComponent_scalarBounds_from_incrementModel
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
    (lam := lam) (t := t) (n := n)
    hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FlagshipFiveComponentAssembly.populationDecomposition_holds
      μ X sigma2 b lam t n hn
  · simpa [FlagshipFiveComponentAssembly.user, FlagshipFiveComponentAssembly.derived,
      FlagshipFiveComponentAssembly.mcAllesterGap] using hfour.mcAllesterGap_le
  · simpa [FlagshipFiveComponentAssembly.derived,
      FlagshipFiveComponentAssembly.onlineGap] using hfour.onlineGap_le
  · simpa [FlagshipFiveComponentAssembly.derived,
      FlagshipFiveComponentAssembly.gaussianBernsteinGap] using hfour.gaussianBernsteinGap_le
  · simpa [FlagshipFiveComponentAssembly.derived,
      FlagshipFiveComponentAssembly.anytimeGap] using hfour.anytimeGap_le
  · show FlagshipFiveComponentAssembly.prefixGap ≤
        (FlagshipFiveComponentAssembly.derived lam n t).prefixKernelContribution
    exact le_rfl

/--
The five-component flagship assembled bound, obtained from the scalar component
inequalities rather than an externally supplied certificate.
-/
theorem flagshipFiveComponent_population_le_bound_from_incrementModel
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
    (FlagshipFiveComponentAssembly.user n hn).populationRisk ≤
      flagshipBound
        (FlagshipFiveComponentAssembly.user n hn)
        (FlagshipFiveComponentAssembly.derived lam n t) := by
  exact flagshipScalarAssembly_from_componentInequalities
    (FlagshipFiveComponentAssembly.user n hn)
    (FlagshipFiveComponentAssembly.derived lam n t)
    (flagshipFiveComponent_scalarBounds_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)

/-- Certificate object for the five-component flagship assembly. -/
def flagshipFiveComponent_certificate_from_incrementModel
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
  user := FlagshipFiveComponentAssembly.user n hn
  derived := FlagshipFiveComponentAssembly.derived lam n t
  assembledBound :=
    flagshipFiveComponent_population_le_bound_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (n := n)
      hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar

/--
The public five-component conclusion: the flagship population-risk certificate,
the finite-horizon anytime-valid event certificate, and the witness that all five
derived contributions are strictly positive.
-/
structure FlagshipFiveComponentConclusion {Ω : Type*} [MeasurableSpace Ω]
    (certificate : FlagshipCertificate)
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (n : ℕ) : Prop where
  flagship : flagshipConclusion certificate
  anytimeUniform :
    μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t n)
      ≤ anytimeVilleTailContribution lam n t
  fiveSlotsPositive :
    0 < certificate.derived.mcAllesterGeneralWidthContribution ∧
      0 < certificate.derived.onlineIidContribution ∧
      0 < certificate.derived.bernsteinOrGaussianContribution ∧
      0 < certificate.derived.anytimeVilleContribution ∧
      0 < certificate.derived.prefixKernelContribution

/-- The reviewer-facing flagship conclusion for the five-component assembly. -/
theorem flagshipFiveComponent_conclusion_from_incrementModel
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
    FlagshipFiveComponentConclusion
      (flagshipFiveComponent_certificate_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (n := n)
        hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)
      μ X sigma2 b lam t n := by
  refine ⟨?_, ?_, ?_⟩
  · exact pacBayesTestTimeFlagship_theorem
      (flagshipFiveComponent_certificate_from_incrementModel
        (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
        (lam := lam) (t := t) (n := n)
        hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar)
  · exact flagshipAnytimeUniformBoundaryMass_le_from_incrementModel
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (t := t) (horizon := n)
      hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter hvar
  · exact flagshipFiveComponent_five_slots_positive lam n t

end

end FormalSLT.TestTimeMeta
