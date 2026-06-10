import FormalSLT.PACBayes.VitaleLemma

/-!
# Continuous prior/posterior PAC-Bayes certificate

This module records the continuous-prior/posterior certificate data used by the
Bernstein PAC-Bayes bound. The prior and posterior are measures on an arbitrary
measurable parameter space. The high-probability PAC-Bayes gate is supplied as
an explicit hypothesis; it is not derived in this file.
-/

namespace FormalSLT.PACBayes

open MeasureTheory

/-- Continuous-prior PAC-Bayes certificate data. -/
structure ContinuousPriorPosteriorSpec (Θ : Type*) [MeasurableSpace Θ] where
  prior : Measure Θ
  posterior : Measure Θ
  sampleSize : ℕ
  lossBound : ℝ
  empiricalRisk : ℝ
  populationRisk : ℝ
  varianceBound : ℝ
  klBound : ℝ
  confidencePenalty : ℝ
  complexityBound : ℝ
  pacPenalty : ℝ

/-- Complexity term after adding the confidence penalty. -/
def continuousPriorPosteriorComplexity
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ) : ℝ :=
  spec.klBound + spec.confidencePenalty

/-- PAC risk upper side for the continuous prior/posterior certificate. -/
def continuousPriorPosteriorBound
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ) : ℝ :=
  spec.empiricalRisk + spec.pacPenalty

/--
Continuous prior/posterior PAC-Bayes certificate, conditional on explicit KL
and high-probability PAC gates.

The theorem does not assume a finite hypothesis class. It also does not derive
the high-probability gate; that gate is the hypothesis `hpacGate`.
-/
theorem continuousPriorPosterior_certificate_of_kl
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ)
    (hcomplexity :
      continuousPriorPosteriorComplexity spec ≤ spec.complexityBound)
    (hpacGate :
      spec.populationRisk ≤ continuousPriorPosteriorBound spec) :
    spec.populationRisk ≤ continuousPriorPosteriorBound spec := by
  have _ := hcomplexity
  exact hpacGate

end FormalSLT.PACBayes
