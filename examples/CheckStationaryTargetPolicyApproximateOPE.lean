import FormalSLT.StochasticDynamics.StationaryTargetPolicyApproximateOPE

/-!
# Approximate target-policy OPE API and axiom receipt

The event keeps the exact target-policy OPE boundary and adds only the
posterior average of a fixed pointwise residual envelope.  The event is fixed
before the path, tilt atom, posterior, and time are selected.  It does not
construct or select a candidate kernel, potential, invariant law, transition-
confidence event, or residual envelope.
-/

open FormalSLT.StochasticDynamics

/-- The approximate residual definition recovers zero from an exact supplied
target-policy Poisson equation. -/
example {Z A : Type*} [Fintype Z] [Fintype A]
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A)
    (potential : Z → ℝ)
    (hexact : IsExactTargetPolicyPoissonSolution
      P π stationary score potential) (z : Z) :
    approximateTargetPolicyPoissonResidual
        P π stationary score potential z = 0 := by
  unfold approximateTargetPolicyPoissonResidual targetPolicyPoissonDrift
  rw [hexact z]
  ring

#check stationaryTargetPolicyPredictableMean_eq_drift
#check stationaryTargetPolicyPosteriorResidualAverage
#check posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean_approximate
#check neg_stationaryTargetPolicyPosteriorResidualAverage_le
#check exists_stationaryApproximateTargetPolicyOPE_event

#print axioms stationaryTargetPolicyPredictableMean_eq_drift
#print axioms stationaryTargetPolicyPosteriorResidualAverage
#print axioms posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean_approximate
#print axioms neg_stationaryTargetPolicyPosteriorResidualAverage_le
#print axioms exists_stationaryApproximateTargetPolicyOPE_event
