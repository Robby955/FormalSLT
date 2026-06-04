import FormalSLT

/-!
# High-probability Rademacher bound

Checks the high-probability generalization bound combining
Rademacher symmetrization with sharp McDiarmid concentration.

**Theorem.** For finite class with loss bounded by B:

    P(genGap ≥ 2 · E[Rad_S] + ε) ≤ exp(-ε² n / (2B²))

The finite-class composition replaces E[Rad_S] with Massart's bound:

    P(genGap ≥ 2B · √(2 · log|H| / n) + ε) ≤ exp(-ε² n / (2B²))
-/

open FormalSLT.Rademacher.HighProbability

-- High-prob Rademacher: P(genGap ≥ 2·E[Rad] + ε) ≤ exp(-ε²n/(2B²))
#check genGap_highProb_rademacher

open FormalSLT.Rademacher.FiniteClassHighProb

-- Finite-class composition: Massart + sharp McDiarmid
#check genGap_highProb_finiteClass

open FormalSLT.Rademacher.Symmetrization

-- Rademacher symmetrization: E[genGap] ≤ 2·E[Rad]
#check expected_genGap_le_two_expected_empiricalRademacherComplexity

open FormalSLT.Azuma.ExposureMartingale

-- Sharp genGap tail: P(genGap ≥ E[genGap] + ε) ≤ exp(-ε²n/(2B²))
#check genGap_tail_bound_sharp_explicit
