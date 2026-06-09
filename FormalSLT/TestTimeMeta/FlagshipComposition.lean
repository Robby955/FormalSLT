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

The anytime and prefix-kernel slots are still explicit because their flagship
component routes remain separate from this bridge.  The final flagship scalar
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
    (anytimeContribution prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hanytime : 0 ≤ anytimeContribution)
    (hprefix : 0 ≤ prefixKernelContribution) :
    FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution :=
    flagshipMcAllesterContribution mcAllesterSpec
  onlineIidContribution :=
    flagshipOnlineIidContribution onlineInput onlineRegretRate
  bernsteinOrGaussianContribution :=
    flagshipGaussianBernsteinContribution gaussianBernsteinSpec
  anytimeVilleContribution := anytimeContribution
  prefixKernelContribution := prefixKernelContribution
  mcAllesterGeneralWidthContributionNonnegative := hmcAllester
  onlineIidContributionNonnegative := honline
  bernsteinOrGaussianContributionNonnegative := hgaussianBernstein
  anytimeVilleContributionNonnegative := hanytime
  prefixKernelContributionNonnegative := hprefix

/-- Field audit theorem for the component-derived q063 contribution bundle. -/
theorem flagshipDerivedContributions_from_components
    {ι Z : Type*} {T d : ℕ}
    (mcAllesterSpec : PACBayesCertificateSpec ι Z)
    (onlineInput : BoundedLossRegretConversionInput T)
    (onlineRegretRate : ℝ)
    (gaussianBernsteinSpec :
      ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (anytimeContribution prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hanytime : 0 ≤ anytimeContribution)
    (hprefix : 0 ≤ prefixKernelContribution) :
    let derived :=
      flagshipDerivedContributionsOfComponents
        mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeContribution prefixKernelContribution
        hmcAllester honline hgaussianBernstein hanytime hprefix
    derived.mcAllesterGeneralWidthContribution =
        flagshipMcAllesterContribution mcAllesterSpec ∧
      derived.onlineIidContribution =
        flagshipOnlineIidContribution onlineInput onlineRegretRate ∧
      derived.bernsteinOrGaussianContribution =
        flagshipGaussianBernsteinContribution gaussianBernsteinSpec ∧
      derived.anytimeVilleContribution = anytimeContribution ∧
      derived.prefixKernelContribution = prefixKernelContribution := by
  simp [flagshipDerivedContributionsOfComponents]

/--
Scalar component inequalities used to assemble the q063 flagship bound.

The first field decomposes the target population risk into five component
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
    (anytimeContribution prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hanytime : 0 ≤ anytimeContribution)
    (hprefix : 0 ≤ prefixKernelContribution)
    (mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ)
    (scalarBounds :
      FlagshipScalarComponentBounds user
        (flagshipDerivedContributionsOfComponents
          mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
          anytimeContribution prefixKernelContribution
          hmcAllester honline hgaussianBernstein hanytime hprefix)
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap) :
    FlagshipCertificate where
  user := user
  derived :=
    flagshipDerivedContributionsOfComponents
      mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
      anytimeContribution prefixKernelContribution
      hmcAllester honline hgaussianBernstein hanytime hprefix
  assembledBound :=
    flagshipScalarAssembly_from_componentInequalities
      user
      (flagshipDerivedContributionsOfComponents
        mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeContribution prefixKernelContribution
        hmcAllester honline hgaussianBernstein hanytime hprefix)
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
    (anytimeContribution prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ flagshipGaussianBernsteinContribution gaussianBernsteinSpec)
    (hanytime : 0 ≤ anytimeContribution)
    (hprefix : 0 ≤ prefixKernelContribution)
    (mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ)
    (scalarBounds :
      FlagshipScalarComponentBounds user
        (flagshipDerivedContributionsOfComponents
          mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
          anytimeContribution prefixKernelContribution
          hmcAllester honline hgaussianBernstein hanytime hprefix)
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap) :
    flagshipConclusion
      (flagshipCertificateOfComponents
        user mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeContribution prefixKernelContribution
        hmcAllester honline hgaussianBernstein hanytime hprefix
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap
        scalarBounds) := by
  exact pacBayesTestTimeFlagship_theorem
    (flagshipCertificateOfComponents
      user mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
      anytimeContribution prefixKernelContribution
      hmcAllester honline hgaussianBernstein hanytime hprefix
      mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap
      scalarBounds)

namespace FlagshipComponentWorkedExample

def onlineInput : BoundedLossRegretConversionInput 1 where
  lossBound := 1
  populationLoss := fun _ => 0
  empiricalLoss := fun _ => 0
  comparatorEmpiricalLoss := 0
  regretBound := 0
  deviationBound := (1 : ℝ) / 25

def onlineRegretRate : ℝ := 0

def onlineX : Fin 1 → Unit → ℝ := fun _ _ => 0

theorem onlinePopulationEq :
    ∀ t : Fin 1, onlineInput.populationLoss t =
      ∫ x, onlineX t x ∂(0 : Measure Unit) := by
  intro t
  simp [onlineInput, onlineX]

theorem onlineEmpiricalEq :
    ∀ t : Fin 1, onlineInput.empiricalLoss t = onlineX t () := by
  intro t
  simp [onlineInput, onlineX]

theorem onlineNotBad :
    () ∉ FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent
      (0 : Measure Unit) onlineX ((1 : ℝ) / 100) := by
  simp [FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent,
    FormalSLT.Probability.IIDConcentration.iidPopulationMinusEmpiricalSum,
    onlineX]

theorem onlineContributionNonnegative :
    0 ≤ flagshipOnlineIidContribution onlineInput onlineRegretRate := by
  exact flagshipOnlineIidContribution_from_iidRegretConversion
    (T := 1)
    (by norm_num)
    (0 : Measure Unit)
    onlineInput
    onlineX
    ()
    (eps := (1 : ℝ) / 100)
    onlineRegretRate
    (by norm_num [onlineInput])
    (by
      intro t
      fin_cases t
      norm_num [onlineInput])
    (by
      intro t
      fin_cases t
      norm_num [onlineInput])
    onlinePopulationEq
    onlineEmpiricalEq
    (by norm_num [onlineInput])
    onlineNotBad
    (by norm_num [averageEmpiricalLoss, averageFin, onlineInput])
    (by norm_num [onlineRegretRate, onlineInput])
    (by norm_num [onlineRegretRate])
    (by norm_num [onlineInput])

def gaussianPrior : SphericalGaussianParams 1 where
  mean := fun _ => 0
  variance := 1
  variance_pos := by norm_num

def gaussianPosterior : SphericalGaussianParams 1 where
  mean := fun _ => 0
  variance := 1
  variance_pos := by norm_num

def gaussianSpec : ContinuousPriorPosteriorSpec (GaussianParameterSpace 1) where
  prior := sphericalGaussianMeasure gaussianPrior
  posterior := sphericalGaussianMeasure gaussianPosterior
  sampleSize := 1
  lossBound := 1
  empiricalRisk := 0
  populationRisk := 0
  varianceBound := (1 : ℝ) / 4
  klBound := 0
  confidencePenalty := 0
  complexityBound := 1
  pacPenalty := (9 : ℝ) / 200

def gaussianControl : ContinuousKLControl (GaussianParameterSpace 1) where
  prior := sphericalGaussianMeasure gaussianPrior
  posterior := sphericalGaussianMeasure gaussianPosterior
  kl := 0
  vitaleBound := 0
  dimensionPenalty := 0
  localRadiusPenalty := 0

def bernsteinLaw : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

def bernsteinX : Fin 2 → ℝ := fun z => if z = 0 then 0 else 1

theorem bernsteinLaw_isPMF : IsPMF bernsteinLaw := by
  refine ⟨?_, ?_⟩
  · intro z
    norm_num [bernsteinLaw]
  · simp [bernsteinLaw]

theorem bernsteinX_nonnegative : ∀ z, 0 ≤ bernsteinX z := by
  intro z
  fin_cases z <;> norm_num [bernsteinX, Fin.ext_iff]

theorem bernsteinX_bound : ∀ z, bernsteinX z ≤ 1 := by
  intro z
  fin_cases z <;> norm_num [bernsteinX, Fin.ext_iff]

theorem bernsteinVariance :
    BernsteinAnalytic.finiteCenteredSecondMoment bernsteinLaw bernsteinX =
      (1 : ℝ) / 4 := by
  norm_num [BernsteinAnalytic.finiteCenteredSecondMoment,
    BernsteinAnalytic.finiteMean, bernsteinLaw, bernsteinX, Fin.sum_univ_two]

theorem gaussianKL_zero :
    sphericalGaussianKL gaussianPosterior gaussianPrior = 0 := by
  rw [sphericalGaussianKL_eq_closedForm]
  norm_num [gaussianPrior, gaussianPosterior, squaredMeanDistance,
    sphericalGaussianKLClosedForm]

theorem gaussianBernsteinRiskBound :
    gaussianSpec.populationRisk ≤
      gaussianSpec.empiricalRisk + flagshipGaussianBernsteinContribution gaussianSpec := by
  exact flagshipGaussianBernsteinContribution_from_sphericalGaussian
    (d := 1)
    (Z := Fin 2)
    (n := 1)
    (by norm_num)
    gaussianSpec
    gaussianControl
    gaussianPosterior
    gaussianPrior
    bernsteinLaw
    bernsteinLaw_isPMF
    bernsteinX
    (b := 1)
    (sigma2 := (1 : ℝ) / 4)
    (eps := 0)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    bernsteinX_nonnegative
    bernsteinX_bound
    bernsteinVariance
    (by norm_num [gaussianSpec])
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (by
      rw [gaussianKL_zero]
      norm_num [gaussianControl])
    (by
      rw [gaussianKL_zero]
      norm_num [gaussianControl, vitaleTotalBound])
    (by norm_num [gaussianSpec, gaussianControl, vitaleTotalBound])
    (by norm_num [gaussianSpec, flagshipGaussianBernsteinContribution,
      bernsteinPACBayesPenalty])

theorem gaussianBernsteinContributionNonnegative :
    0 ≤ flagshipGaussianBernsteinContribution gaussianSpec := by
  norm_num [flagshipGaussianBernsteinContribution, gaussianSpec,
    bernsteinPACBayesPenalty]

theorem mcAllesterContributionNonnegative :
    0 ≤ flagshipMcAllesterContribution BoundedRegressionStub.spec := by
  exact flagshipMcAllesterContribution_from_compileGeneralWidth
    BoundedRegressionStub.spec
    BoundedRegressionStub.spec.lossBound
    (by norm_num [BoundedRegressionStub.spec])
    BoundedRegressionStub.dataLaw_isPMF
    BoundedRegressionStub.prior_isFullSupportPMF
    (by norm_num [BoundedRegressionStub.spec])
    (by norm_num [BoundedRegressionStub.spec])
    (by norm_num [BoundedRegressionStub.spec])
    (by
      intro i z
      simpa [BoundedRegressionStub.spec] using
        BoundedRegressionStub.loss_mem_unitInterval i z)

def derived : FlagshipDerivedContributions :=
  flagshipDerivedContributionsOfComponents
    BoundedRegressionStub.spec
    onlineInput
    onlineRegretRate
    gaussianSpec
    0
    0
    mcAllesterContributionNonnegative
    onlineContributionNonnegative
    gaussianBernsteinContributionNonnegative
    (by norm_num)
    (by norm_num)

def empiricalRisk : ℝ := (3 : ℝ) / 25

def lossWidth : ℝ := 1

def componentBoundSide : ℝ :=
  empiricalRisk +
    lossWidth * flagshipMcAllesterContribution BoundedRegressionStub.spec +
    flagshipOnlineIidContribution onlineInput onlineRegretRate +
    flagshipGaussianBernsteinContribution gaussianSpec +
    0 +
    0

def user : FlagshipUserSupplied where
  sampleSize := BoundedRegressionStub.spec.sampleSize
  targetConfidence := (19 : ℝ) / 20
  delta := (1 : ℝ) / 20
  lossWidth := lossWidth
  empiricalRisk := empiricalRisk
  populationRisk := componentBoundSide
  positiveSampleSize := by norm_num [BoundedRegressionStub.spec]
  deltaPositive := by norm_num
  confidenceNonnegative := by norm_num
  lossWidthNonnegative := by norm_num [lossWidth]
  empiricalRiskNonnegative := by norm_num [empiricalRisk]
  populationRiskNonnegative := by
    unfold componentBoundSide
    have hmc := mcAllesterContributionNonnegative
    have honline := onlineContributionNonnegative
    have hgaussian := gaussianBernsteinContributionNonnegative
    norm_num [empiricalRisk, lossWidth]
    nlinarith

theorem scalarComponentBounds :
    FlagshipScalarComponentBounds user derived
      (user.lossWidth * derived.mcAllesterGeneralWidthContribution)
      derived.onlineIidContribution
      derived.bernsteinOrGaussianContribution
      derived.anytimeVilleContribution
      derived.prefixKernelContribution := by
  refine ⟨?_, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  unfold user componentBoundSide derived flagshipDerivedContributionsOfComponents
    empiricalRisk lossWidth
  rfl

theorem flagshipComponentWorkedExample_scalarAssembly :
    user.populationRisk ≤ flagshipBound user derived := by
  exact flagshipScalarAssembly_from_componentInequalities
    user derived scalarComponentBounds

/-- Component-derived q064 worked flagship certificate. -/
def certificate : FlagshipCertificate :=
  flagshipCertificateOfComponents
    user
    BoundedRegressionStub.spec
    onlineInput
    onlineRegretRate
    gaussianSpec
    0
    0
    mcAllesterContributionNonnegative
    onlineContributionNonnegative
    gaussianBernsteinContributionNonnegative
    (by norm_num)
    (by norm_num)
    (user.lossWidth * derived.mcAllesterGeneralWidthContribution)
    derived.onlineIidContribution
    derived.bernsteinOrGaussianContribution
    derived.anytimeVilleContribution
    derived.prefixKernelContribution
    scalarComponentBounds

def flagshipComponentWorkedExampleConclusion : Prop :=
  flagshipConclusion certificate

/-- The worked q064 certificate instantiates the component-to-flagship bridge. -/
theorem flagshipComponentWorkedExample_certificate :
    flagshipComponentWorkedExampleConclusion := by
  exact flagshipCertificate_from_components
    user
    BoundedRegressionStub.spec
    onlineInput
    onlineRegretRate
    gaussianSpec
    0
    0
    mcAllesterContributionNonnegative
    onlineContributionNonnegative
    gaussianBernsteinContributionNonnegative
    (by norm_num)
    (by norm_num)
    (user.lossWidth * derived.mcAllesterGeneralWidthContribution)
    derived.onlineIidContribution
    derived.bernsteinOrGaussianContribution
    derived.anytimeVilleContribution
    derived.prefixKernelContribution
    scalarComponentBounds

end FlagshipComponentWorkedExample

end

end FormalSLT.TestTimeMeta
