import FormalSLT.TestTimeMeta.Assumptions
import FormalSLT.PACBayesKL
import FormalSLT.PACBayes.Compiler
import FormalSLT.PACBayes.GaussianKL
import FormalSLT.OnlineToPAC.CesaBianchi
import FormalSLT.OnlineToPAC.IIDConcentration
import FormalSLT.PACBayes.BernsteinBound
import FormalSLT.AnytimeValid.SubGaussianCS

/-!
# Composition lemmas for the PAC-Bayes test-time meta-theorem

These lemmas route the narrowed q053, q055/q059, q056, and q084 surfaces into
the q057 named-assumption interface. The narrowing is explicit: q053 is the
unit-interval compiler route, the old q055 wrapper is conditional on a deviation
gate, the q059 wrapper derives the finite-time iid deviation gate from the
bad-event complement, q056 is certificate-form continuous-prior Bernstein
PAC-Bayes, and q084 is the conditional sub-gamma extractor surface.
-/

namespace FormalSLT.TestTimeMeta

open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.OnlineToPAC
open FormalSLT.AnytimeValid
open MeasureTheory ProbabilityTheory

noncomputable section

/--
q053 contribution wrapper for the unit-interval McAllester compiler route.

Indirection layer: `hcontribution` is a supplied nonnegative scalar slot; the
compiler call records the dependency, not a derived scalar value.
-/
theorem mcAllesterCompilerContribution_from_unitIntervalCompiler
    {ι Z : Type*}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (spec : PACBayesCertificateSpec ι Z)
    (hn : 0 < spec.sampleSize)
    (hdataLaw : IsPMF spec.dataLaw)
    (hprior : IsFullSupportPMF spec.prior)
    (hcomplexityBound : 0 < spec.complexityBound)
    (hdelta : 0 < spec.delta)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ spec.loss i z ∧ spec.loss i z ≤ 1)
    {contribution : ℝ} (hcontribution : 0 ≤ contribution) :
    0 ≤ contribution := by
  have _ :=
    PACBayesCertificateCompiler.compile_sound
      spec hn hdataLaw hprior hcomplexityBound hdelta hloss
  exact hcontribution

/-- q055 contribution wrapper for finite-time online-to-PAC conversion. -/
theorem onlineToPACContribution_from_regretConversion
    {T : ℕ} (hT : 0 < T)
    (input : BoundedLossRegretConversionInput T)
    (regretRate : ℝ)
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧
        input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧
        input.empiricalLoss t ≤ input.lossBound)
    (hdeviation :
      averagePopulationLoss input ≤ averageEmpiricalLoss input + input.deviationBound)
    (hregret :
      averageEmpiricalLoss input ≤
        input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ))
    (hregretRate : input.regretBound / (T : ℝ) ≤ regretRate) :
    averagePopulationLoss input ≤
      input.comparatorEmpiricalLoss + regretRate + input.deviationBound := by
  exact cesaBianchiConconiGentile2004_boundedLoss_iid_highProbability
    hT input regretRate hlossBound hpopulationBounded hempiricalBounded
    hdeviation hregret hregretRate

/-- q059 contribution wrapper for iid-derived finite-time online-to-PAC conversion. -/
theorem onlineToPACContribution_from_iidRegretConversion
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
    (hregretRate : input.regretBound / (T : ℝ) ≤ regretRate) :
    averagePopulationLoss input ≤
      input.comparatorEmpiricalLoss + regretRate + input.deviationBound := by
  exact cesaBianchi_iid
    hT μ input X ω regretRate hlossBound hpopulationBounded hempiricalBounded
    hpopulationEq hempiricalEq hdeviationRadius hnotBad hregret hregretRate

/--
q056 contribution wrapper for continuous-prior Bernstein certificates.

Indirection layer: the final risk inequality is the certificate premise
`hpenalty`; this wrapper routes the continuous-certificate gates into the shared
composition interface.
-/
theorem bernsteinContribution_from_continuousCertificate
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ)
    (control : ContinuousKLControl Θ)
    (hsamePrior : spec.prior = control.prior)
    (hsamePosterior : spec.posterior = control.posterior)
    (hvariance : 0 ≤ spec.varianceBound)
    (hkl : control.kl ≤ vitaleTotalBound control)
    (hklBound :
      vitaleTotalBound control + spec.confidencePenalty ≤ spec.complexityBound)
    (hpenalty :
      spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec) :
    spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec := by
  exact bernsteinPACBayes_continuousPriorPosterior_certificate
    spec control hsamePrior hsamePosterior hvariance hkl hklBound hpenalty

/--
q062 contribution wrapper for concrete spherical Gaussian continuous certificates.

Indirection layer: the final risk inequality is the certificate premise
`hpenalty`; the Gaussian work here derives the KL gate used by the wrapper.
-/
theorem bernsteinContribution_from_sphericalGaussianCertificate
    {d : ℕ}
    (spec : ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (control : ContinuousKLControl (GaussianParameterSpace d))
    (posterior prior : SphericalGaussianParams d)
    (hspecPrior : spec.prior = sphericalGaussianMeasure prior)
    (hspecPosterior : spec.posterior = sphericalGaussianMeasure posterior)
    (hcontrolPrior : control.prior = sphericalGaussianMeasure prior)
    (hcontrolPosterior : control.posterior = sphericalGaussianMeasure posterior)
    (hvariance : 0 ≤ spec.varianceBound)
    (hklClosed : control.kl = sphericalGaussianKL posterior prior)
    (hklGaussian : sphericalGaussianKL posterior prior ≤ vitaleTotalBound control)
    (hklBound :
      vitaleTotalBound control + spec.confidencePenalty ≤ spec.complexityBound)
    (hpenalty :
      spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec) :
    spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec := by
  have hkl :=
    vitaleContinuousKL_sphericalGaussian
      control posterior prior hcontrolPrior hcontrolPosterior hklClosed hklGaussian
  have hsamePrior : spec.prior = control.prior := by
    rw [hspecPrior, hcontrolPrior]
  have hsamePosterior : spec.posterior = control.posterior := by
    rw [hspecPosterior, hcontrolPosterior]
  exact bernsteinPACBayes_continuousPriorPosterior_certificate
    spec control hsamePrior hsamePosterior hvariance hkl hklBound hpenalty

/-- q084 canonical anytime Ville tail contribution for a fixed horizon and boundary. -/
def anytimeVilleTailContribution (lam : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-lam * (n : ℝ) * t)

/--
q084 contribution wrapper for the conditional sub-gamma extractor route.

The extractor layer supplies the one-step sub-gamma supermartingale obligation;
the anytime slot stores the Ville tail mass bound produced from that process.
-/
theorem anytimeVilleContribution_from_subGammaExtractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (h_condSubGamma_step : ∀ k,
      μ[subGammaExponentialProcess X sigma2 b lam (k + 1) | ℱ k]
        ≤ᵐ[μ] subGammaExponentialProcess X sigma2 b lam k)
    (h_exponential_boundary :
      {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
        ⊆
      {ω | Real.exp (lam * (n : ℝ) * t)
          ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω}) :
    μ.real {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ≤ anytimeVilleTailContribution lam n t := by
  simpa [anytimeVilleTailContribution] using
    ville_inequality_subGamma_running_mean_of_condSubGamma
      h_adapted h_integrable h_condSubGamma_step h_exponential_boundary

end

end FormalSLT.TestTimeMeta
