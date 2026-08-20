import FormalSLT.StochasticDynamics.StationaryTargetPolicyRobustFiniteDepthOPE

/-!
# Fixed-candidate finite-depth target-policy OPE API receipt

This checker covers every public declaration in the module.  The candidate
environment, reference laws, contraction and action-row total-variation
certificates, and depth are fixed before the one outer event.  The event is
simultaneous over path, finite tilt atom, posterior PMF, and time, but it does
not license data-dependent candidate or depth selection.
-/

open FormalSLT.StochasticDynamics

#check candidateTargetPolicyFiniteDepthPotential
#check finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le
#check exists_stationaryRobustCandidateFiniteDepthTargetPolicyOPE_event

#print axioms FormalSLT.StochasticDynamics.candidateTargetPolicyFiniteDepthPotential
#print axioms FormalSLT.StochasticDynamics.finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le
#print axioms FormalSLT.StochasticDynamics.exists_stationaryRobustCandidateFiniteDepthTargetPolicyOPE_event
