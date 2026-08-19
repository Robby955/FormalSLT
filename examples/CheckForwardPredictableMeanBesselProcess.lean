import FormalSLT.AnytimeValid.ForwardPredictableMeanBesselProcess

/-!
# Predictable-mean forward-Bessel checks

This checker records the exact stochastic interface: `mean k` is measurable
with respect to the past filtration and is a version of `E[X k | F k]`.  The
endpoint controls the running average of these conditional means.  It does not
assert a new empirical-Bernstein inequality; the hybrid-Bessel step is the
pathwise envelope already checked for the fixed-mean process.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Examples.CheckForwardPredictableMeanBesselProcess

open FormalSLT.AnytimeValid

variable {Omega : Type*} [mOmega : MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {F : Filtration ℕ mOmega}

/-- Focused receipt for the all-time lower-tail boundary around the running
average of predictable conditional means. -/
theorem predictableMean_allTimeLowerBessel_receipt
    {X mean : ℕ → Omega → ℝ} {lam delta : ℝ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    mu.real
        (forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure
          X mean lam delta) ≤ delta :=
  forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_mass_le_delta
    hdelta hlam hlam1 hX_adapted hmean_adapted hX_unit hmean

#check forwardPredictableMeanEmpiricalBernsteinFactor_condExp_le_one
#check forwardPredictableMeanEmpiricalBernsteinProcess_eProcess_of_bounded
#check forwardPredictableMeanEmpiricalBernsteinLowerFactor_condExp_le_one
#check forwardPredictableMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#check forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope_le_process
#check forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_mass_le_delta
#check exists_forwardPredictableMeanEmpiricalBernsteinLowerBessel_event
#check forwardPredictableMeanEmpiricalBernsteinProcess_const_mean_eq
#check forwardPredictableMeanEmpiricalBernsteinLowerProcess_const_mean_eq
#check predictableMean_allTimeLowerBessel_receipt

#print axioms forwardPredictableMeanEmpiricalBernsteinFactor_condExp_le_one
#print axioms forwardPredictableMeanEmpiricalBernsteinProcess_eProcess_of_bounded
#print axioms forwardPredictableMeanEmpiricalBernsteinLowerFactor_condExp_le_one
#print axioms forwardPredictableMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#print axioms forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope_le_process
#print axioms forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_mass_le_delta
#print axioms exists_forwardPredictableMeanEmpiricalBernsteinLowerBessel_event
#print axioms forwardPredictableMeanEmpiricalBernsteinProcess_const_mean_eq
#print axioms forwardPredictableMeanEmpiricalBernsteinLowerProcess_const_mean_eq
#print axioms predictableMean_allTimeLowerBessel_receipt

end FormalSLT.Examples.CheckForwardPredictableMeanBesselProcess
