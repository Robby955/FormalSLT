import FormalSLT.Applications.RandomRefreshLoadPath

/-!
# Balanced twenty-state path checker

This checker exposes the complete public path-layer API and audits every
public theorem declaration.  The named path is an arithmetic witness only;
no statistical good-event membership is asserted here.
-/

open FormalSLT.StochasticDynamics
open FormalSLT.StochasticDynamics.RandomRefreshLoadModel
open FormalSLT.StochasticDynamics.RandomRefreshLoadPath

#check deBruijnVertex
#check successorCycleVertex
#check balancedPath
#check deBruijnVertex_periodic
#check successorCycleVertex_periodic
#check balancedPath_periodic
#check balancedPath_transitionVisitMass_mul_period
#check balancedPath_transitionEdgeMass_mul_period
#check balancedPath_empiricalTransitionFrequency_mul_period
#check balancedPath_transitionVisitMass
#check balancedPath_transitionEdgeMass
#check balancedPath_empiricalTransitionFrequency

#print axioms deBruijnVertex_periodic
#print axioms successorCycleVertex_periodic
#print axioms balancedPath_periodic
#print axioms balancedPath_transitionVisitMass_mul_period
#print axioms balancedPath_transitionEdgeMass_mul_period
#print axioms balancedPath_empiricalTransitionFrequency_mul_period
#print axioms balancedPath_transitionVisitMass
#print axioms balancedPath_transitionEdgeMass
#print axioms balancedPath_empiricalTransitionFrequency
