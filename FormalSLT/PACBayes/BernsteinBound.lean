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
