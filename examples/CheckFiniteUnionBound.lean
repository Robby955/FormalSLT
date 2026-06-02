import FormalSLT.Probability.FiniteUnionBound

/-!
# Finite union-bound checker

This file checks the finite measure-union skeleton used by later finite-class
and anytime-valid arguments.

```bash
lake env lean examples/CheckFiniteUnionBound.lean
```
-/

#check FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound
#print axioms FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound

#check FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_budget
#print axioms FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_budget

#check FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_const
#print axioms FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_const

#check FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_equalBudget
#print axioms FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_equalBudget

#check FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_cardInv
#print axioms FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_cardInv
