import FormalSLT.TestTimeMeta.Assumptions
import FormalSLT.PACBayesKL
import FormalSLT.PACBayes.Compiler
import FormalSLT.PACBayes.GaussianKL
import FormalSLT.OnlineToPAC.CesaBianchi
import FormalSLT.OnlineToPAC.IIDConcentration
import FormalSLT.PACBayes.BernsteinBound
import FormalSLT.Concentration.SubGamma.Extractor

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
open FormalSLT.Concentration.SubGamma
open MeasureTheory ProbabilityTheory

noncomputable section

/-- q053 contribution wrapper for the unit-interval McAllester compiler route. -/
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

/-- q056 contribution wrapper for continuous-prior Bernstein certificates. -/
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

/-- q062 contribution wrapper for concrete spherical Gaussian continuous certificates. -/
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

/-- q084 contribution wrapper for the conditional sub-gamma extractor. -/
theorem anytimeVilleContribution_from_subGammaExtractor
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    {X : Ω → ℝ}
    {b σ2 contribution : ℝ}
    (hb_pos : 0 < b)
    (hσ_nonneg : 0 ≤ σ2)
    (hX_meas : Measurable[m₀] X)
    (hX_int : Integrable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hcenter : μ[X | m] =ᵐ[μ] 0)
    (hvar : μ[fun ω => X ω ^ 2 | m] ≤ᵐ[μ] fun _ => σ2)
    (hcontribution : 0 ≤ contribution) :
    0 ≤ contribution := by
  have _ :=
    condSubGammaMGF_of_bounded_centered_condVariance
      (m₀ := m₀) (μ := μ) (m := m) (X := X) (b := b) (σ2 := σ2)
      hb_pos hσ_nonneg hX_meas hX_int hbound hcenter hvar
  exact hcontribution

end

end FormalSLT.TestTimeMeta
