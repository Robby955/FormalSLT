import FormalSLT.AnytimeValid.PredictableVarianceProxy

/-!
# Predictable variance-proxy interface audit

Checks the typed empirical-Bernstein proxy contract, its fixed-tilt confidence
sequence wrapper, and the deterministic and lagged bounded constructions.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

#check IsPredictableVarianceProxy
#check @empiricalBernstein_confidence_sequence_of_proxy
#check @isPredictableVarianceProxy_const
#check @stronglyAdapted_regularizedLaggedSecondMomentProxy
#check @isPredictableVarianceProxy_regularizedLagged_of_condSecondMoment_le
#check @isPredictableVarianceProxy_regularizedLagged

#print axioms empiricalBernstein_confidence_sequence_of_proxy
#print axioms isPredictableVarianceProxy_const
#print axioms stronglyAdapted_regularizedLaggedSecondMomentProxy
#print axioms isPredictableVarianceProxy_regularizedLagged_of_condSecondMoment_le
#print axioms isPredictableVarianceProxy_regularizedLagged

example
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    {X : Nat -> Omega -> Real} {b lam delta : Real}
    (hdelta : 0 < delta)
    (hb : 0 < b) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : forall k, Measurable (X k))
    (hX_int : forall k, Integrable (X k) mu)
    (hX_adapted : IncrementAdapted F X)
    (hbound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= b)
    (hcenter : forall k, mu[X k | F k] =ᵐ[mu] 0) :
    mu.real
        (empiricalBernsteinUpperFailure
          X (constantVarianceProxy b) b lam delta) <= delta := by
  exact empiricalBernstein_confidence_sequence_of_proxy
    hdelta hb hlam hblam hX_meas hX_int hX_adapted hbound hcenter
    (isPredictableVarianceProxy_const hX_meas hbound)

example {Omega : Type*} (X : Nat -> Omega -> Real) (b : Real) (omega : Omega) :
    regularizedLaggedSecondMomentProxy X (b ^ 2) 0 omega = b ^ 2 := by
  simp [regularizedLaggedSecondMomentProxy]

example
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    {X : Nat -> Omega -> Real} {b lam delta : Real}
    (hdelta : 0 < delta)
    (hb : 0 < b) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : forall k, Measurable (X k))
    (hX_int : forall k, Integrable (X k) mu)
    (hX_adapted : IncrementAdapted F X)
    (hbound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= b)
    (hcenter : forall k, mu[X k | F k] =ᵐ[mu] 0) :
    mu.real
        (empiricalBernsteinUpperFailure X
          (regularizedLaggedSecondMomentProxy X (b ^ 2)) b lam delta) <= delta := by
  exact empiricalBernstein_confidence_sequence_of_proxy
    hdelta hb hlam hblam hX_meas hX_int hX_adapted hbound hcenter
    (isPredictableVarianceProxy_regularizedLagged hX_meas hX_adapted hbound)
