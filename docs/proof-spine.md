# Proof Spine

The library proves VC-style ERM sample-complexity bounds through a finite
Rademacher/VC chain, then adds three application-facing extensions:
finite scalar contraction, finite-dimensional linear predictors, and finite
sub-Gaussian chaining infrastructure.

## Stage 1: Definitions

**Risk.lean** defines population risk and empirical risk:

```
populationRisk μ ℓ i = ∫ z, ℓ i z ∂μ
empiricalRisk ℓ S i = (1/n) · Σ_k ℓ i (S k)
```

**GhostSample.lean** defines the generalization gap as the worst-case difference:

```
genGap μ ℓ S = sup_i (populationRisk μ ℓ i - empiricalRisk ℓ S i)
```

**Rademacher.FiniteSample** defines empirical Rademacher complexity:

```
empiricalRademacherComplexity ℓ S = E_σ [sup_i (1/n) Σ_k σ_k · ℓ i (S k)]
```

where σ are uniform Rademacher signs.

## Stage 2: Symmetrization

**Rademacher.Symmetrization** proves:

```
E_S[genGap μ ℓ S] ≤ 2 · E_S[empiricalRademacherComplexity ℓ S]
```

The proof uses:
1. Ghost sample introduction (independent copy S')
2. Replace population risk with empirical risk on S' (unbiased)
3. Rademacher sign injection (signs are symmetric)
4. Decoupling (drop S' dependence)

## Stage 3: Concentration (sharp McDiarmid)

**Azuma.GenGapTail** routes the exposure martingale through the checked sharp
McDiarmid product-kernel theorem and proves:

```
P_S(genGap μ ℓ S - E[genGap] ≥ ε) ≤ exp(-ε²·n / (2B²))
```

The proof constructs a Doob exposure martingale:
1. Define M_k = E[genGap | S₁,...,Sₖ]
2. Show bounded differences: |M_k - M_{k-1}| ≤ 2B/n (ghost sample replacement)
3. Use the conditional-range MGF and sharp product-kernel tail

## Stage 4: High-Probability Composition

**Rademacher.HighProbability** combines Stages 2 and 3:

```
P_S(genGap μ ℓ S ≥ 2·E_S[Rad(ℓ,S)] + ε) ≤ exp(-ε²·n / (2B²))
```

This is the structural backbone: any upper bound on E[Rad] becomes a high-probability generalization bound.

## Stage 5: Massart and Effective Class

**Rademacher.Massart** proves Massart's finite-class bound:

```
empiricalRademacherComplexity ℓ S ≤ B · √(2·log|H| / n)
```

**VC.Rademacher** introduces the *effective class* — the set of distinct loss vectors on a sample — and proves:

```
empiricalRademacherComplexity ℓ S ≤ B · √(2·log(effectiveClass.card) / n)
```

This strictly improves on Massart when hypotheses agree on the sample.

## Stage 6: VC-Style Sample Complexity

**VC.SauerShelah** converts the binomial-sum Sauer-Shelah bound to closed form:

```
shatterCoeff(n,d) ≤ (en/d)^d
```

**VC.SampleComplexity** composes everything:

1. Sauer-Shelah: effectiveClass.card ≤ (en/d)^d
2. Effective-class Massart: Rad ≤ B·√(2d·log(en/d)/n)
3. High-prob Rademacher: P(genGap ≥ 2B·√(...) + ε) ≤ exp(...)
4. Two-sided: P(uniformDev ≥ ...) ≤ 2·exp(...)
5. ERM: P(excessRisk ≥ ...) ≤ 2·exp(...)

## Stage 7: Finite contraction

**Rademacher.Contraction** proves the scalar finite-sample contraction
theorem:

```
Rad_S(φ ∘ F) ≤ L · Rad_S(F)
```

The proof isolates the algebraic comparison lemma, proves the one-coordinate
replacement step, iterates that step over all sample coordinates, and then
wraps the result in `empiricalRademacherComplexity`. The theorem is scoped to
finite samples, finite classes, scalar real-valued functions, and Lipschitz
transforms with `φ 0 = 0`.

## Stage 8: Linear predictors

**Rademacher.LinearPredictor** proves the finite-dimensional Euclidean linear
predictor bound:

```
Rad_S({x ↦ ⟪w, x⟫ : ‖w‖ ≤ R})
  ≤ R · n⁻¹ · sqrt(Σᵢ ‖xᵢ‖²)
```

It also proves the bounded-input corollary:

```
‖xᵢ‖ ≤ B  ⇒  Rad_S(F) ≤ R · B / sqrt(n)
```

This is the bridge from the abstract finite-class spine to a recognizable
finite-dimensional model family.

## Stage 9: Sub-Gaussian chaining and scoped entropy integrals

**Covering.FiniteSubGaussianChaining** builds finite stochastic-process
infrastructure:

1. finite ε-nets with nearest-net projections;
2. MGF control for finite sub-Gaussian increments;
3. finite-max entropy bounds from MGF assumptions;
4. multiscale chaining decompositions over finite net sequences;
5. finite Dudley-style entropy sums and dyadic entropy-budget wrappers.

`Covering.ContinuousDudley` then checks continuous entropy-integral and `iSup`
endpoints for finite outcome spaces under explicit antitonicity, integrability,
separable-terminal, modulus, and boundary hypotheses. The general construction
of arbitrary measurable suprema and a measure-side chaining budget remains
open; those are not consequences of the scoped integral endpoint.

## What makes this non-trivial

The Rademacher route is more complex than the direct Hoeffding-union approach:

| Approach | Steps | What it gives |
|----------|-------|---------------|
| Hoeffding + union | 2 | exp(-2ε²n) / \|H\| → sample complexity O(log\|H\|/ε²) |
| Rademacher route | 6 stages, ~20 lemmas | Adapts to effective class, connects to VC, generalizes to continuous losses |

The Rademacher route proves the same finite-class bound but through machinery
that now supports contraction, linear predictors, finite chaining, and scoped
entropy-integral endpoints. Unrestricted infinite-class empirical-process
theory still requires additional measurable-supremum and separability
constructions.
