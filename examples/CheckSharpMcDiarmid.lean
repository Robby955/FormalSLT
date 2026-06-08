import FormalSLT.Concentration.SharpMcDiarmid
import FormalSLT.Azuma.GenGapTail

/-!
Axiom audit for the sharp (constant-2) McDiarmid bounded-differences theorems
and their generalization-gap specialization. Each prints the standard mathlib
classical axiom set `[propext, Classical.choice, Quot.sound]`, with no `sorry`,
no `admit`, and no project-specific axiom.
-/

#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp
#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_lower
#print axioms FormalSLT.Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp
#print axioms FormalSLT.Azuma.ExposureMartingale.genGap_tail_bound_sharp
