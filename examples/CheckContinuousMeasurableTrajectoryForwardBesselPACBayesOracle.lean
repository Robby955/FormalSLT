import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryForwardBesselPACBayesOracle

/-!
# Measurable-state growing-prefix PAC-Bayes oracle checks

These checks instantiate both the hypothesis and trajectory state spaces with
`Real`. They therefore audit the absence of hidden finite or countable
typeclass assumptions in the public trajectory endpoint.
-/

open FormalSLT.StochasticDynamics

#synth Infinite Real

#check continuousMeasurableTrajectoryGrowingPrefixArgmin
#check continuousMeasurableTrajectoryGrowingPrefixBoundary
#check continuousMeasurableTrajectoryGrowingPrefixLILEnvelope
#check exists_continuousMeasurableTrajectoryGrowingPrefixForwardBesselPACBayesOracle_event

#check (continuousMeasurableTrajectoryGrowingPrefixArgmin
  (Theta := Real) (Z := Real))
#check (continuousMeasurableTrajectoryGrowingPrefixBoundary
  (Theta := Real) (Z := Real))
#check (continuousMeasurableTrajectoryGrowingPrefixLILEnvelope
  (Theta := Real) (Z := Real))
#check (exists_continuousMeasurableTrajectoryGrowingPrefixForwardBesselPACBayesOracle_event
  (Theta := Real) (Z := Real))

#print axioms exists_continuousMeasurableTrajectoryGrowingPrefixForwardBesselPACBayesOracle_event
