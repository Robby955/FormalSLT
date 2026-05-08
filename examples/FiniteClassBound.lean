import FormalSLT

/-!
# Finite-class generalization bound

Shows how to instantiate the high-probability Rademacher bound
for a concrete finite hypothesis class.
-/

open FormalSLT.Rademacher.FiniteClassHighProb

-- The finite-class high-probability generalization bound says:
--
--   P(genGap ≥ 2B·√(2·log|H|/n) + ε) ≤ exp(-ε²n/(8B²))
--
-- This is Massart + Azuma composed.

#check genGap_highProb_finiteClass

-- To use this, you need:
--   1. A finite nonempty hypothesis class [Fintype ι] [Nonempty ι]
--   2. A probability measure μ on the data space
--   3. A loss function ℓ : ι → Z → ℝ bounded by B
--   4. Sample size n > 0
--   5. Tolerance ε ≥ 0
