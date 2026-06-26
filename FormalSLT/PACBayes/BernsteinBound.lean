import FormalSLT.PACBayesBernstein
import FormalSLT.PACBayes.BernsteinAnalytic
import FormalSLT.PACBayes.ContinuousPriorPosterior
import FormalSLT.PACBayes.GaussianKL
import FormalSLT.PACBayes.VitaleAnalytic

/-!
# Bernstein PAC-Bayes continuous-prior certificate

This module gives the first q056 Bernstein PAC-Bayes certificate surface for
continuous priors and posteriors. It keeps the variance-control, KL-control, and
high-probability Bernstein gates explicit. It does not prove the analytic
Bernstein concentration inequality or the analytic Vitale covering lemma.

The q060 addendum keeps the certificate theorem and adds
`bernsteinBound_analytic`, which routes through the analytic Gaussian KL closed
form in `VitaleAnalytic` and the finite iid Bernstein theorem in
`BernsteinAnalytic`. The probabilistic PAC-Bayes gate remains explicit: this
module composes verified analytic inputs with the q056 certificate surface; it
does not construct arbitrary continuous Gaussian measures.

References: Tolstikhin and Seldin (2013), "PAC-Bayes-Empirical-Bernstein
Inequality"; Alquier, Ridgway, Chopin (2016), "On the Properties of
Variational Approximations of Gibbs Posteriors".
-/

namespace FormalSLT.PACBayes

open MeasureTheory
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein

/-- Bernstein PAC-Bayes penalty data supplied by a continuous certificate. -/
def bernsteinPACBayesPenalty
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ) : ℝ :=
  spec.pacPenalty

/--
Continuous-prior Bernstein PAC-Bayes certificate.

The theorem is a certificate-form statement: it consumes explicit
variance-control, continuous KL, and Bernstein high-probability gates and emits
the final risk bound. It is not a finite-hypothesis theorem and does not replace
the analytic continuous PAC-Bayes proof still needed upstream.

Indirection layer: `hpenalty` is the final PAC-Bayes inequality for the supplied
continuous certificate; this theorem records the KL and variance gates around
that certificate rather than deriving a new posterior-risk inequality.
-/
theorem bernsteinPACBayes_continuousPriorPosterior_certificate
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ)
    (control : ContinuousKLControl Θ)
    (hsamePrior : spec.prior = control.prior)
    (hsamePosterior : spec.posterior = control.posterior)
    (hvariance : 0 ≤ spec.varianceBound)
    (hkl : control.kl ≤ vitaleTotalBound control)
    (hklBound : vitaleTotalBound control + spec.confidencePenalty ≤ spec.complexityBound)
    (hpenalty :
      spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec) :
    spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec := by
  have _ := hsamePrior
  have _ := hsamePosterior
  have _ := hvariance
  have hcontinuousKL := vitaleContinuousKL_certificate control hkl
  have _ : control.kl + spec.confidencePenalty ≤ spec.complexityBound := by
    linarith
  exact hpenalty

/--
Finite fixed-sample PAC-Bayes Bernstein posterior-risk bound.

This is the finite hypothesis-class analogue of the Bernstein flagship slot:
the posterior risk bound is derived from the finite PAC-Bayes Bernstein
change-of-measure adapter, rather than supplied as a premise.
-/
theorem finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda scale alpha : ℝ}
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω)
    (hconf :
      priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω
        ≤ Real.exp alpha) :
    posteriorRisk ρ riskFn ≤
      posteriorEmpiricalRisk ρ (empiricalRiskFn ω) +
        (klDiv ρ π + alpha) / lambda +
        lambda * posteriorMarginVarianceProxy ρ varianceProxy /
          (2 * (1 - scale * lambda)) := by
  have hgap :=
    posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le
      hρ hπ hlambda hscale riskFn empiricalRiskFn varianceProxy ω hconf
  unfold posteriorGeneralizationGap at hgap
  linarith

/--
Delta-shaped finite PAC-Bayes Bernstein posterior-risk bound.

The good-sample certificate is the same `1 / delta` prior-moment bound used by
`finitePACBayesBernstein_fixedLambda_badEventMass_le_delta`; this theorem gives
the corresponding posterior-risk inequality on such a sample.
-/
theorem finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le_inv_delta
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda scale delta : ℝ}
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (hdelta : 0 < delta)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω)
    (hconf :
      priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω
        ≤ 1 / delta) :
    posteriorRisk ρ riskFn ≤
      posteriorEmpiricalRisk ρ (empiricalRiskFn ω) +
        (klDiv ρ π + Real.log (1 / delta)) / lambda +
        lambda * posteriorMarginVarianceProxy ρ varianceProxy /
          (2 * (1 - scale * lambda)) := by
  have hconf_exp :
      priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω
        ≤ Real.exp (Real.log (1 / delta)) := by
    rw [Real.exp_log (div_pos zero_lt_one hdelta)]
    exact hconf
  exact finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le
    hρ hπ hlambda hscale riskFn empiricalRiskFn varianceProxy ω hconf_exp

/--
Analytic q060 Bernstein PAC-Bayes composition.

This widens the q056 certificate by deriving the continuous KL gate from the
equal-variance Gaussian closed-form calculation and by requiring an actual
finite iid Bernstein tail theorem instance for the scalar bounded observable.
The final PAC-Bayes risk gate is still an explicit premise, matching the q056
certificate discipline.
-/
theorem bernsteinBound_analytic
    {Θ : Type*} [MeasurableSpace Θ]
    {Z : Type*} [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (spec : ContinuousPriorPosteriorSpec Θ)
    (control : ContinuousKLControl Θ)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p) (X : Z → ℝ)
    {b sigma2 eps : ℝ}
    (hb : 0 < b) (hsigma2 : 0 < sigma2) (heps : 0 ≤ eps)
    (hX_nonneg : ∀ z, 0 ≤ X z)
    (hX_bound : ∀ z, X z ≤ b)
    (hvariance :
      BernsteinAnalytic.finiteCenteredSecondMoment p X = sigma2)
    (hspecVariance : spec.varianceBound = sigma2)
    {posteriorMean priorMean gaussianVariance : ℝ}
    (hgaussianVariance : 0 < gaussianVariance)
    (hklClosed :
      control.kl =
        gaussianGaussianKL posteriorMean priorMean gaussianVariance gaussianVariance)
    (hclosedBound :
      (posteriorMean - priorMean) ^ (2 : Nat) / (2 * gaussianVariance) ≤
        vitaleTotalBound control)
    (hsamePrior : spec.prior = control.prior)
    (hsamePosterior : spec.posterior = control.posterior)
    (hklBound :
      vitaleTotalBound control + spec.confidencePenalty ≤ spec.complexityBound)
    (hpenalty :
      spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec) :
    spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec := by
  have hbernstein :=
    BernsteinAnalytic.bernstein_iid_bounded_upper_tail
      (n := n) hn p hp X hb hsigma2 heps hX_nonneg hX_bound hvariance
  have hkl :=
    vitaleContinuousKL_analytic_gaussian_equalVariance
      control hgaussianVariance hklClosed hclosedBound
  have hvariance_nonneg : 0 ≤ spec.varianceBound := by
    rw [hspecVariance]
    exact hsigma2.le
  exact bernsteinPACBayes_continuousPriorPosterior_certificate
    spec control hsamePrior hsamePosterior hvariance_nonneg hkl hklBound hpenalty

/--
Analytic q062 Bernstein PAC-Bayes composition for concrete spherical Gaussian
prior/posterior measures.

Compared with `bernsteinBound_analytic`, this theorem uses the finite-
dimensional Gaussian measure/KL backend directly. The final PAC-Bayes risk gate
remains explicit, matching the q056 certificate discipline.
-/
theorem bernsteinBound_sphericalGaussian
    {d : ℕ}
    {Z : Type*} [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (spec : ContinuousPriorPosteriorSpec (GaussianParameterSpace d))
    (control : ContinuousKLControl (GaussianParameterSpace d))
    (posterior prior : SphericalGaussianParams d)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p) (X : Z → ℝ)
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
      spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec) :
    spec.populationRisk ≤ spec.empiricalRisk + bernsteinPACBayesPenalty spec := by
  have hbernstein :=
    BernsteinAnalytic.bernstein_iid_bounded_upper_tail
      (n := n) hn p hp X hb hsigma2 heps hX_nonneg hX_bound hvariance
  have hkl :=
    vitaleContinuousKL_sphericalGaussian
      control posterior prior hcontrolPrior hcontrolPosterior hklClosed hclosedBound
  have hvariance_nonneg : 0 ≤ spec.varianceBound := by
    rw [hspecVariance]
    exact hsigma2.le
  have hsamePrior : spec.prior = control.prior := by
    rw [hspecPrior, hcontrolPrior]
  have hsamePosterior : spec.posterior = control.posterior := by
    rw [hspecPosterior, hcontrolPosterior]
  exact bernsteinPACBayes_continuousPriorPosterior_certificate
    spec control hsamePrior hsamePosterior hvariance_nonneg hkl hklBound hpenalty

end FormalSLT.PACBayes
