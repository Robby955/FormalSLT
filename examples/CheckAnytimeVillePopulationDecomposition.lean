import FormalSLT.TestTimeMeta.AnytimeVillePopulationDecomposition

/-!
# Axiom audit for the anytime/Ville flagship slot
-/

open FormalSLT.TestTimeMeta

#print axioms anytimeVilleContribution_from_incrementModel
#print axioms anytimeVilleScalarBounds_from_incrementModel
#print axioms anytimeVilleFlagship_population_le_bound_from_incrementModel

#check @anytimeVilleBoundaryEvent
#check @anytimeVilleBoundaryMass
#check @anytimeVilleContribution_from_incrementModel
#check @anytimeVilleScalarBounds_from_incrementModel
#check @anytimeVilleFlagship_population_le_bound_from_incrementModel
