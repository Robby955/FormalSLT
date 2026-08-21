import FormalSLT.StochasticDynamics.StationaryTargetPolicyEmpiricalFiniteDepthOPE

/-!
# Empirical-kernel finite-depth target-policy OPE API and axiom receipt

The candidate and depth are fixed before the event.  The theorem intersects
the signed-residual OPE event with an augmented empirical-transition event and
requires every augmented source row to be visited at the displayed horizon.
-/

open FormalSLT.StochasticDynamics

#check exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event

#print axioms exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event
