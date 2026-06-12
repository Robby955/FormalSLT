import FormalSLT.AnytimeValid.SubGaussianCS

/-!
# Anytime-valid sub-Gamma confidence-sequence audit

This file forces elaboration of the anytime-valid confidence-sequence wrapper.
The printed axiom set should be exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open FormalSLT.AnytimeValid
open MeasureTheory

#print axioms nonneg_supermartingale_of_condSubGamma
#print axioms ville_inequality_subGamma_running_mean
#print axioms anytime_valid_confidence_sequence_subGamma

example :
    inSubGammaConfidenceInterval
      (X := fun _ : ℕ => fun _ : Unit => (0 : ℝ))
      (theta := 0) (sigma2 := 0) (b := 0) (delta := Real.exp (-1))
      1 () := by
  simp [inSubGammaConfidenceInterval, subGammaConfidenceLower,
    subGammaConfidenceUpper, runningMean, runningSum, subGammaWidth]
