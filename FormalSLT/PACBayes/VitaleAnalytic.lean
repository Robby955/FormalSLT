import FormalSLT.PACBayes.VitaleLemma
import FormalSLT.PACBayes.GaussianKL
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Analytic Vitale/Gaussian KL surface

This module widens the q056 continuous-prior certificate by adding the analytic
Gaussian-Gaussian closed-form KL calculation used by the worked continuous
PAC-Bayes examples.

The general non-Gaussian continuous KL theorem is deliberately not claimed
here: constructing Radon-Nikodym derivatives and KL integrals for arbitrary
continuous prior/posterior pairs needs a larger measure-theory development.
Instead, the general interface keeps the analytic upper-bound hypothesis
visible. The q062 spherical Gaussian bridge uses concrete finite-dimensional
Gaussian measures from `GaussianKL`; the older scalar equal-variance helper is
retained for compatibility with q060-era examples.

Citation audit status:

* Bernstein (1924), "On a modification of Chebyshev's inequality and of the
  error formula of Laplace" has no DOI/arXiv in the checked citation and was
  reported by `scripts/citation_audit.py` as `WARN_UNVERIFIABLE`.
* Richard A. Vitale, "The Wills functional and Gaussian processes", Annals of
  Probability 24(4):2172--2178, 1996, DOI `10.1214/aop/1041903224`, passed the
  same audit through Crossref. The q060 prompt named "Vitale (1990)", but this
  checked reference is the Gaussian-process/Wills-functional source that
  resolves under the cited DOI; no 1990 identifier is fabricated here.
-/

namespace FormalSLT.PACBayes

open MeasureTheory Real

noncomputable section

/-- Closed-form KL expression for one-dimensional Gaussian posteriors and priors.

The parameters are posterior mean/variance followed by prior mean/variance.
This is the usual scalar formula
`1/2 * (σq²/σp² + (μp-μq)^2/σp² - 1 + log(σp²/σq²))`, represented as a real
arithmetic expression rather than as a constructed Gaussian-measure KL. -/
def gaussianGaussianKL (posteriorMean priorMean posteriorVariance priorVariance : ℝ) : ℝ :=
  (posteriorVariance / priorVariance +
      (priorMean - posteriorMean) ^ (2 : Nat) / priorVariance -
      1 +
      Real.log (priorVariance / posteriorVariance)) /
    2

/-- Equal-variance Gaussian-Gaussian KL collapses to the squared mean gap over
twice the common variance. -/
theorem gaussianGaussianKL_equalVariance_closedForm
    {posteriorMean priorMean variance : ℝ} (hvariance : 0 < variance) :
    gaussianGaussianKL posteriorMean priorMean variance variance =
      (posteriorMean - priorMean) ^ (2 : Nat) / (2 * variance) := by
  have hne : variance ≠ 0 := ne_of_gt hvariance
  unfold gaussianGaussianKL
  rw [div_self hne, Real.log_one]
  field_simp [hne]
  ring

/-- Analytic Vitale/KL control in the equal-variance Gaussian worked case.

Compared with `vitaleContinuousKL_certificate`, this theorem does not take the
final `kl ≤ vitaleTotalBound` inequality directly. It derives that inequality
from the Gaussian closed-form KL identity plus a verified real upper bound on
that closed form. -/
theorem vitaleContinuousKL_analytic_gaussian_equalVariance
    {Θ : Type*} [MeasurableSpace Θ]
    (control : ContinuousKLControl Θ)
    {posteriorMean priorMean variance : ℝ} (hvariance : 0 < variance)
    (hklClosed :
      control.kl = gaussianGaussianKL posteriorMean priorMean variance variance)
    (hclosedBound :
      (posteriorMean - priorMean) ^ (2 : Nat) / (2 * variance) ≤ vitaleTotalBound control) :
    control.kl ≤ vitaleTotalBound control := by
  rw [hklClosed, gaussianGaussianKL_equalVariance_closedForm hvariance]
  exact hclosedBound

/-- Analytic Vitale/KL control for concrete finite-dimensional spherical Gaussian measures.

The prior and posterior fields of `control` are actual Gaussian measures on
`Fin d → ℝ`; the KL value is the q062 closed-form Gaussian KL backend. -/
theorem vitaleContinuousKL_sphericalGaussian
    {d : ℕ}
    (control : ContinuousKLControl (GaussianParameterSpace d))
    (posterior prior : SphericalGaussianParams d)
    (hprior : control.prior = sphericalGaussianMeasure prior)
    (hposterior : control.posterior = sphericalGaussianMeasure posterior)
    (hklClosed : control.kl = sphericalGaussianKL posterior prior)
    (hclosedBound : sphericalGaussianKL posterior prior ≤ vitaleTotalBound control) :
    control.kl ≤ vitaleTotalBound control := by
  have _ := hprior
  have _ := hposterior
  rw [hklClosed]
  exact hclosedBound

end

end FormalSLT.PACBayes
