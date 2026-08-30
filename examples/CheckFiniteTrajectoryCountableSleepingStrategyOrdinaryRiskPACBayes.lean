import FormalSLT.StochasticDynamics.FiniteTrajectoryCountableSleepingStrategyOrdinaryRiskPACBayes

/-!
# Countable sleeping-strategy ordinary-risk checks

The generic theorem gives one event for a finite model posterior and a
posterior over the active prefix of a predeclared countable sleeping e-process
catalog.  The trajectory specialization converts its weighted conclusion to
ordinary encountered conditional prefix risk, with an explicit discrepancy
surcharge.  Both posteriors and the reporting time may be selected from the
observed path.

This remains confidence allocation over a catalog fixed before observation;
it is not coin betting, future risk, stationary risk, or population risk.
-/

open FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
open FormalSLT.StochasticDynamics

#check exists_finiteModelCountableSleepingEProcessPACBayes_event
#check exists_finiteTrajectoryCountableSleepingStrategyPACBayes_ordinaryPrefixRisk_event

#print axioms exists_finiteModelCountableSleepingEProcessPACBayes_event
#print axioms exists_finiteTrajectoryCountableSleepingStrategyPACBayes_ordinaryPrefixRisk_event
