import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryTwoSidedSingularFractionExactOptimalPACBayes

/-!
# Exact scalar-fraction measurable-trajectory checks

Both endpoints use arbitrary measurable state and hypothesis spaces. The
all-fractions endpoint permits an explicit admissible rational fraction; the
exact optimizer is noncomputable and is not an executable strategy selector.
-/

open FormalSLT.StochasticDynamics

#synth Infinite Real

#check continuousTrajectorySingularFractionBesselBoundary
#check exists_continuousMeasurableTrajectoryTwoSidedSingularFractionBesselPACBayes_allFractions_event
#check exists_continuousMeasurableTrajectoryTwoSidedSingularFractionExactOptimalPACBayes_event

#check (exists_continuousMeasurableTrajectoryTwoSidedSingularFractionBesselPACBayes_allFractions_event
  (Theta := Real) (Z := Real))
#check (exists_continuousMeasurableTrajectoryTwoSidedSingularFractionExactOptimalPACBayes_event
  (Theta := Real) (Z := Real))

#print axioms continuousTrajectorySingularFractionBesselBoundary
#print axioms exists_continuousMeasurableTrajectoryTwoSidedSingularFractionBesselPACBayes_allFractions_event
#print axioms exists_continuousMeasurableTrajectoryTwoSidedSingularFractionExactOptimalPACBayes_event
