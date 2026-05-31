import FormalSLT.Concentration.SubGamma.Extractor
import FormalSLT.Concentration.SubGamma.BoundedExpIntegrable
import FormalSLT.Concentration.SubGamma.CondExpProduct
import FormalSLT.Concentration.SubGamma.CondJensen
import FormalSLT.Concentration.SubGamma.CondMarkov
import FormalSLT.Concentration.SubGamma.CondVarianceFromSquare

/-!
# Conditional sub-Gamma extractor audit

Checks the conditional sub-Gamma helper lemmas and the main extractor theorem.
Each `#print axioms` should report only
`[propext, Classical.choice, Quot.sound]`.

Run with:

```bash
lake env lean examples/CheckSubGammaExtractor.lean
```
-/

/-! ## Pointwise Bennett bound -/

#check @FormalSLT.Concentration.SubGamma.bennett_taylor_bound
#print axioms FormalSLT.Concentration.SubGamma.bennett_taylor_bound

#check @FormalSLT.Concentration.SubGamma.integrable_exp_mul_of_bounded
#print axioms FormalSLT.Concentration.SubGamma.integrable_exp_mul_of_bounded

/-! ## Conditional-expectation helpers -/

#check @FormalSLT.Concentration.SubGamma.condJensen_real
#print axioms FormalSLT.Concentration.SubGamma.condJensen_real

#check @FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
#print axioms FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left

#check @FormalSLT.Concentration.SubGamma.condExp_sq_eq_condVar_of_centered
#print axioms FormalSLT.Concentration.SubGamma.condExp_sq_eq_condVar_of_centered

#check @FormalSLT.Concentration.SubGamma.cond_markov_of_nonneg
#print axioms FormalSLT.Concentration.SubGamma.cond_markov_of_nonneg

/-! ## Main extractor -/

#check @FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance
#print axioms FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance
