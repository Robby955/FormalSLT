/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.GaussianMeasureKL
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Time-uniform spherical-Gaussian PAC-Bayes bound

This module specializes the continuous process-level PAC-Bayes theorem to the
repository's finite-dimensional spherical Gaussian measures.  The abstract
measure-theoretic `klDiv` penalty is replaced by the explicit closed form

`(d * (posteriorVariance / priorVariance - 1 +
    log (priorVariance / posteriorVariance)) +
    squaredMeanDistance posteriorMean priorMean / priorVariance) / 2`.

The Gaussian probability-measure instances, posterior-to-prior absolute
continuity, log-likelihood-ratio integrability, and KL identification are all
discharged by the measure-theoretic Gaussian bridge.  The score-process and
Fubini integrability assumptions remain explicit.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FormalSLT.PACBayes.TimeUniformGaussian

open TimeUniformContinuous

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Failure event for the spherical-Gaussian specialization, with the Gaussian
KL penalty written in the repository's explicit finite-dimensional closed
form. -/
def timeUniformSphericalGaussianPACBayesUpperFailure {d : ℕ}
    (prior posterior : SphericalGaussianParams d)
    (score : GaussianParameterSpace d → ℕ → Ω → ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    sphericalGaussianKLClosedForm posterior prior + Real.log (1 / delta)
      ≤ ∫ θ, score θ n ω ∂sphericalGaussianMeasure posterior}

/-- The explicit spherical-Gaussian failure event is exactly the abstract
continuous PAC-Bayes failure event for the corresponding Gaussian measures. -/
theorem timeUniformSphericalGaussianPACBayesUpperFailure_eq_continuous
    {d : ℕ} (prior posterior : SphericalGaussianParams d)
    (score : GaussianParameterSpace d → ℕ → Ω → ℝ) (delta : ℝ) :
    timeUniformSphericalGaussianPACBayesUpperFailure
        prior posterior score delta =
      timeUniformContinuousPACBayesUpperFailure
        (sphericalGaussianMeasure prior)
        (sphericalGaussianMeasure posterior) score delta := by
  ext ω
  simp [timeUniformSphericalGaussianPACBayesUpperFailure,
    timeUniformContinuousPACBayesUpperFailure,
    sphericalGaussianMeasure_klDiv_toReal_eq,
    sphericalGaussianKL_eq_closedForm]

/--
End-to-end time-uniform PAC-Bayes bound for spherical Gaussian priors and
posteriors.

With probability at least `1 - delta`, at every positive time the posterior
average score is below the explicit spherical-Gaussian KL penalty plus
`log (1 / delta)`.  The theorem derives Gaussian absolute continuity and
log-likelihood-ratio integrability rather than requesting them from callers.
-/
theorem timeUniformSphericalGaussianPACBayes_bound
    {d : ℕ} {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    (prior posterior : SphericalGaussianParams d)
    (score : GaussianParameterSpace d → ℕ → Ω → ℝ) {delta : ℝ}
    (hδ : 0 < delta)
    (h_adapted_mix :
      StronglyAdapted ℱ
        (continuousExponentialMixtureProcess
          (sphericalGaussianMeasure prior) score))
    (h_integrable_mix :
      ∀ n, Integrable
        (continuousExponentialMixtureProcess
          (sphericalGaussianMeasure prior) score n) μ)
    (hM_int_next :
      ∀ n, Integrable
        (fun p : GaussianParameterSpace d × Ω =>
          Real.exp (score p.1 (n + 1) p.2))
        ((sphericalGaussianMeasure prior).prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × GaussianParameterSpace d =>
            Real.exp (score p.2 (n + 1) p.1))
          ((μ.restrict s).prod (sphericalGaussianMeasure prior)))
    (hM_int_current :
      ∀ n, Integrable
        (fun p : Ω × GaussianParameterSpace d =>
          Real.exp (score p.2 n p.1))
        (μ.prod (sphericalGaussianMeasure prior)))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × GaussianParameterSpace d =>
            Real.exp (score p.2 n p.1))
          ((μ.restrict s).prod (sphericalGaussianMeasure prior)))
    (hfixed :
      ∀ᵐ θ ∂sphericalGaussianMeasure prior,
        Supermartingale (fun n ω => Real.exp (score θ n ω)) ℱ μ)
    (hscore_zero : ∀ θ ω, score θ 0 ω = 0)
    (hexp_int :
      ∀ n ω, Integrable (fun θ => Real.exp (score θ n ω))
        (sphericalGaussianMeasure prior))
    (hscore_int :
      ∀ n ω, Integrable (fun θ => score θ n ω)
        (sphericalGaussianMeasure posterior)) :
    μ.real (timeUniformSphericalGaussianPACBayesUpperFailure
      prior posterior score delta) ≤ delta := by
  rw [timeUniformSphericalGaussianPACBayesUpperFailure_eq_continuous]
  exact timeUniformContinuousPACBayes_bound
    (sphericalGaussianMeasure prior)
    (sphericalGaussianMeasure posterior)
    (sphericalGaussianMeasure_absolutelyContinuous posterior prior)
    score hδ h_adapted_mix h_integrable_mix hM_int_next
    hM_int_next_restrict hM_int_current hM_int_current_restrict hfixed
    hscore_zero hexp_int hscore_int
    (integrable_llr_diagonalGaussianMeasure
      posterior.toDiagonal prior.toDiagonal)

end

end FormalSLT.PACBayes.TimeUniformGaussian
