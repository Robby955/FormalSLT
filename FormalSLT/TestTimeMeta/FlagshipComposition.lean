import FormalSLT.TestTimeMeta.Flagship

/-!
# Component-to-flagship composition bridge

This module is the q064 bridge from the checked component surfaces to q063's
paper-ready `FlagshipCertificate` API.  It keeps q063's readable contribution
names, but makes the main contribution values canonical outputs of the lower
theorems:

* q061 general-width McAllester compiler gives the McAllester square-root
  contribution;
* q059 iid online-to-PAC conversion gives the regret-plus-deviation
  contribution;
* q062 finite-dimensional Gaussian KL plus the q060 Bernstein path gives the
  Bernstein/Gaussian PAC-Bayes contribution.
* q084 anytime Ville route gives the fixed-horizon sub-Gamma tail
  contribution.

The prefix-kernel slot is still explicit because its flagship component route
remains separate from this bridge.  The final flagship scalar
assembly is not a one-line external certificate: q066 derives it from a risk
decomposition and per-component inequalities.
-/

namespace FormalSLT.TestTimeMeta

open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.OnlineToPAC
open MeasureTheory ProbabilityTheory

noncomputable section

/-- Canonical q061 McAllester contribution stored in the q063 flagship slot. -/
def flagshipMcAllesterContribution {ι Z : Type*}
    (spec : PACBayesCertificateSpec ι Z) : ℝ :=
  mcAllesterPenalty spec.sampleSize spec.complexityBound

/-- Canonical q059 online contribution: finite regret rate plus iid deviation radius. -/
def flagshipOnlineIidContribution {T : ℕ}
    (input : BoundedLossRegretConversionInput T) (regretRate : ℝ) : ℝ :=
  regretRate + input.deviationBound

/-- Canonical q062/q060 Gaussian-Bernstein contribution from a continuous spec. -/
def flagshipGaussianBernsteinContribution
    {d : ℕ}
    (spec : ContinuousPriorPosteriorSpec (GaussianParameterSpace d)) : ℝ :=
  bernsteinPACBayesPenalty spec

/--
Derive the q063 McAllester contribution from q061's general-width compiler
soundness theorem.
-/
theorem flagshipMcAllesterContribution_from_compileGeneralWidth
    {ι Z : Type*}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (spec : PACBayesCertificateSpec ι Z)
    (lossBound : ℝ)
    (hn : 0 < spec.sampleSize)
    (hdataLaw : IsPMF spec.dataLaw)
    (hprior : IsFullSupportPMF spec.prior)
    (hcomplexityBound : 0 < spec.complexityBound)
    (hdelta : 0 < spec.delta)
    (hlossBound : 0 ≤ lossBound)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ spec.loss i z ∧ spec.loss i z ≤ lossBound) :
    0 ≤ flagshipMcAllesterContribution spec := by
  have _hcompiler : PACBayesCertificateCompiler.compileGeneralWidth lossBound spec :=
    PACBayesCertificateCompiler.compileGeneralWidth_sound
      spec lossBound hn hdataLaw hprior hcomplexityBound hdelta hlossBound hloss
  unfold flagshipMcAllesterContribution mcAllesterPenalty
  exact Real.sqrt_nonneg _

/--
Derive the q063 online contribution from q059's iid online-to-PAC conversion.

The q059 theorem supplies the pointwise online-to-PAC inequality outside the
iid deviation bad event; this wrapper exposes the corresponding nonnegative
additive contribution stored in `FlagshipDerivedContributions`.
-/
theorem flagshipOnlineIidContribution_from_iidRegretConversion
    {T : ℕ} (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (input : BoundedLossRegretConversionInput T)
    (X : Fin T → Ω → ℝ) (ω : Ω) {eps : ℝ}
    (regretRate : ℝ)
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧
        input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧
        input.empiricalLoss t ≤ input.lossBound)
    (hpopulationEq :
      ∀ t : Fin T, input.populationLoss t = ∫ x, X t x ∂μ)
    (hempiricalEq :
      ∀ t : Fin T, input.empiricalLoss t = X t ω)
    (hdeviationRadius : eps ≤ input.deviationBound)
    (hnotBad :
      ω ∉ FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent μ X eps)
    (hregret :
      averageEmpiricalLoss input ≤
        input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ))
    (hregretRate : input.regretBound / (T : ℝ) ≤ regretRate)
    (hregretRateNonnegative : 0 ≤ regretRate)
    (hdeviationBoundNonnegative : 0 ≤ input.deviationBound) :
    0 ≤ flagshipOnlineIidContribution input regretRate := by
  have _honline :
      averagePopulationLoss input ≤
        input.comparatorEmpiricalLoss + regretRate + input.deviationBound :=
    onlineToPACContribution_from_iidRegretConversion
      hT μ input X ω regretRate hlossBound hpopulationBounded hempiricalBounded
      hpopulationEq hempiricalEq hdeviationRadius hnotBad hregret hregretRate
  unfold flagshipOnlineIidContribution
  linarith

/--
Derive the q063 Gaussian/Bernstein contribution from the q062 finite Gaussian
measure/KL backend and the q060 analytic Bernstein route.
-/
theorem flagshipGaussianBernsteinContribution_from_sphericalGaussian
    {d : ℕ}
    {Z : Type*} [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (spec : ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (control : ContinuousKLControl (GaussianParameterSpace d))
    (posterior prior : SphericalGaussianParams d)
    (p : Z → ℝ) (hp : IsPMF p) (X : Z → ℝ)
    {b sigma2 eps : ℝ}
    (hb : 0 < b) (hsigma2 : 0 < sigma2) (heps : 0 ≤ eps)
    (hX_nonneg : ∀ z, 0 ≤ X z)
    (hX_bound : ∀ z, X z ≤ b)
    (hvariance :
      BernsteinAnalytic.finiteCenteredSecondMoment p X = sigma2)
    (hspecVariance : spec.varianceBound = sigma2)
    (hspecPrior : spec.prior = sphericalGaussianMeasure prior)
    (hspecPosterior : spec.posterior = sphericalGaussianMeasure posterior)
    (hcontrolPrior : control.prior = sphericalGaussianMeasure prior)
    (hcontrolPosterior : control.posterior = sphericalGaussianMeasure posterior)
    (hklClosed : control.kl = sphericalGaussianKL posterior prior)
    (hclosedBound : sphericalGaussianKL posterior prior ≤ vitaleTotalBound control)
    (hklBound :
      vitaleTotalBound control + spec.confidencePenalty ≤ spec.complexityBound)
    (hpenalty :
      spec.populationRisk ≤ spec.empiricalRisk + flagshipGaussianBernsteinContribution spec) :
    spec.populationRisk ≤
      spec.empiricalRisk + flagshipGaussianBernsteinContribution spec := by
  exact bernsteinBound_sphericalGaussian
    (n := n) hn spec control posterior prior p hp X hb hsigma2 heps
    hX_nonneg hX_bound hvariance hspecVariance hspecPrior hspecPosterior
    hcontrolPrior hcontrolPosterior hklClosed hclosedBound hklBound hpenalty

/-- Component-derived q063 contribution bundle. -/
def flagshipDerivedContributionsOfComponents
    {ι Z : Type*} {T d : ℕ}
    (mcAllesterSpec : PACBayesCertificateSpec ι Z)
    (onlineInput : BoundedLossRegretConversionInput T)
    (onlineRegretRate : ℝ)
    (gaussianBernsteinSpec :
      ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (anytimeLam anytimeBoundary : ℝ)
    (anytimeHorizon : ℕ)
    (prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hprefix : 0 ≤ prefixKernelContribution) :
    FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution :=
    flagshipMcAllesterContribution mcAllesterSpec
  onlineIidContribution :=
    flagshipOnlineIidContribution onlineInput onlineRegretRate
  bernsteinOrGaussianContribution :=
    flagshipGaussianBernsteinContribution gaussianBernsteinSpec
  anytimeVilleContribution :=
    anytimeVilleTailContribution anytimeLam anytimeHorizon anytimeBoundary
  prefixKernelContribution := prefixKernelContribution
  mcAllesterGeneralWidthContributionNonnegative := hmcAllester
  onlineIidContributionNonnegative := honline
  bernsteinOrGaussianContributionNonnegative := hgaussianBernstein
  anytimeVilleContributionNonnegative := by
    dsimp [anytimeVilleTailContribution]
    exact (Real.exp_pos _).le
  prefixKernelContributionNonnegative := hprefix

/-- Field audit theorem for the component-derived q063 contribution bundle. -/
theorem flagshipDerivedContributions_from_components
    {ι Z : Type*} {T d : ℕ}
    (mcAllesterSpec : PACBayesCertificateSpec ι Z)
    (onlineInput : BoundedLossRegretConversionInput T)
    (onlineRegretRate : ℝ)
    (gaussianBernsteinSpec :
      ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (anytimeLam anytimeBoundary : ℝ)
    (anytimeHorizon : ℕ)
    (prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hprefix : 0 ≤ prefixKernelContribution) :
    let derived :=
      flagshipDerivedContributionsOfComponents
        mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
        hmcAllester honline hgaussianBernstein hprefix
    derived.mcAllesterGeneralWidthContribution =
        flagshipMcAllesterContribution mcAllesterSpec ∧
      derived.onlineIidContribution =
        flagshipOnlineIidContribution onlineInput onlineRegretRate ∧
      derived.bernsteinOrGaussianContribution =
        flagshipGaussianBernsteinContribution gaussianBernsteinSpec ∧
      derived.anytimeVilleContribution =
        anytimeVilleTailContribution anytimeLam anytimeHorizon anytimeBoundary ∧
      derived.prefixKernelContribution = prefixKernelContribution := by
  simp [flagshipDerivedContributionsOfComponents]

/--
Scalar component inequalities used to assemble the q063 flagship bound.

The leading field decomposes the target population risk into five component
gaps.  The remaining fields bound each gap by the corresponding component slot
in `FlagshipDerivedContributions`.
-/
structure FlagshipScalarComponentBounds
    (user : FlagshipUserSupplied)
    (derived : FlagshipDerivedContributions)
    (mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ) :
    Prop where
  populationDecomposition :
    user.populationRisk ≤
      user.empiricalRisk +
        mcAllesterGap +
        onlineGap +
        gaussianBernsteinGap +
        anytimeGap +
        prefixGap
  mcAllesterGap_le :
    mcAllesterGap ≤
      user.lossWidth * derived.mcAllesterGeneralWidthContribution
  onlineGap_le :
    onlineGap ≤ derived.onlineIidContribution
  gaussianBernsteinGap_le :
    gaussianBernsteinGap ≤ derived.bernsteinOrGaussianContribution
  anytimeGap_le :
    anytimeGap ≤ derived.anytimeVilleContribution
  prefixGap_le :
    prefixGap ≤ derived.prefixKernelContribution

/--
Derive q063's assembled scalar flagship bound from component inequalities.
-/
theorem flagshipScalarAssembly_from_componentInequalities
    (user : FlagshipUserSupplied)
    (derived : FlagshipDerivedContributions)
    {mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ}
    (bounds :
      FlagshipScalarComponentBounds user derived
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap) :
    user.populationRisk ≤ flagshipBound user derived := by
  unfold flagshipBound
  linarith [
    bounds.populationDecomposition,
    bounds.mcAllesterGap_le,
    bounds.onlineGap_le,
    bounds.gaussianBernsteinGap_le,
    bounds.anytimeGap_le,
    bounds.prefixGap_le]

/-- Construct a q063 flagship certificate from component-derived contributions. -/
def flagshipCertificateOfComponents
    {ι Z : Type*} {T d : ℕ}
    (user : FlagshipUserSupplied)
    (mcAllesterSpec : PACBayesCertificateSpec ι Z)
    (onlineInput : BoundedLossRegretConversionInput T)
    (onlineRegretRate : ℝ)
    (gaussianBernsteinSpec :
      ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (anytimeLam anytimeBoundary : ℝ)
    (anytimeHorizon : ℕ)
    (prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hprefix : 0 ≤ prefixKernelContribution)
    (mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ)
    (scalarBounds :
      FlagshipScalarComponentBounds user
        (flagshipDerivedContributionsOfComponents
          mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
          anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
          hmcAllester honline hgaussianBernstein hprefix)
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap) :
    FlagshipCertificate where
  user := user
  derived :=
    flagshipDerivedContributionsOfComponents
      mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
      anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
      hmcAllester honline hgaussianBernstein hprefix
  assembledBound :=
    flagshipScalarAssembly_from_componentInequalities
      user
      (flagshipDerivedContributionsOfComponents
        mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
        hmcAllester honline hgaussianBernstein hprefix)
      scalarBounds

/--
The component-assembled q063 certificate satisfies the flagship theorem without
an externally supplied scalar assembly certificate.
-/
theorem flagshipCertificate_from_components
    {ι Z : Type*} {T d : ℕ}
    (user : FlagshipUserSupplied)
    (mcAllesterSpec : PACBayesCertificateSpec ι Z)
    (onlineInput : BoundedLossRegretConversionInput T)
    (onlineRegretRate : ℝ)
    (gaussianBernsteinSpec :
      ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (anytimeLam anytimeBoundary : ℝ)
    (anytimeHorizon : ℕ)
    (prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hprefix : 0 ≤ prefixKernelContribution)
    (mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ)
    (scalarBounds :
      FlagshipScalarComponentBounds user
        (flagshipDerivedContributionsOfComponents
          mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
          anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
          hmcAllester honline hgaussianBernstein hprefix)
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap) :
    flagshipConclusion
      (flagshipCertificateOfComponents
        user mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
        hmcAllester honline hgaussianBernstein hprefix
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap
        scalarBounds) := by
  exact pacBayesTestTimeFlagship_theorem
    (flagshipCertificateOfComponents
      user mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
      anytimeLam anytimeBoundary anytimeHorizon prefixKernelContribution
      hmcAllester honline hgaussianBernstein hprefix
      mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap
      scalarBounds)

end

end FormalSLT.TestTimeMeta
