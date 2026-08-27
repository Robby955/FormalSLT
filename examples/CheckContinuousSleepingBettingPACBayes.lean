import FormalSLT.PACBayes.ContinuousSleepingBettingPACBayes

/-!
# Executable sleeping-master continuous PAC-Bayes checks

The capstone mixes exact finite-prefix countable betting masters over an
arbitrary measurable hypothesis space. One common event supports every
reporting time and every eligible path-selected posterior. Its conclusion is
a posterior-average log-wealth bound, not yet an ordinary-risk certificate.
-/

open FormalSLT.PACBayes.ContinuousSleepingBettingPACBayes

#check continuousSleepingBettingMasterProcess
#check continuousSleepingBettingPACBayesExceptionalEvent
#check continuousSleepingBettingMasterProcess_eProcess
#check continuousSleepingBettingMasterProcess_pos
#check continuousSleepingBettingPACBayesExceptionalEvent_mass_le_delta
#check continuousSleepingBettingPACBayes_allPosteriors_of_not_mem
#check exists_continuousSleepingBettingPACBayes_event

#check (exists_continuousSleepingBettingPACBayes_event (Theta := Real))

#print axioms continuousSleepingBettingMasterProcess_eProcess
#print axioms continuousSleepingBettingMasterProcess_pos
#print axioms continuousSleepingBettingPACBayesExceptionalEvent_mass_le_delta
#print axioms continuousSleepingBettingPACBayes_allPosteriors_of_not_mem
#print axioms exists_continuousSleepingBettingPACBayes_event
