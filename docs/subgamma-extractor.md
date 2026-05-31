# Conditional Sub-Gamma Extractor

This note records the checked conditional sub-Gamma MGF layer in
`FormalSLT.Concentration.SubGamma`.

## Main theorem

`FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance`
proves the following Lean-level interface:

if a real-valued increment `X` is a.s. bounded by `b`, conditionally centered
with respect to a sub-sigma-algebra `m`, and has conditional second moment at
most `σ²`, then its conditional exponential moment is bounded by the
sub-Gamma expression

```text
exp(σ² * λ^2 / (2 * (1 - b * λ / 3)))
```

in the regime `0 ≤ λ` and `b * λ < 3`.

## Module layout

| Module | Role |
|---|---|
| `Concentration.SubGamma.BennettBound` | pointwise Bennett Taylor bound |
| `Concentration.SubGamma.BoundedExpIntegrable` | exponential integrability from boundedness |
| `Concentration.SubGamma.CondExpProduct` | bounded-factor conditional-expectation product rule |
| `Concentration.SubGamma.CondJensen` | conditional Jensen helper |
| `Concentration.SubGamma.CondMarkov` | conditional Markov helper |
| `Concentration.SubGamma.CondVarianceFromSquare` | centered second moment as variance proxy |
| `Concentration.SubGamma.Extractor` | final conditional sub-Gamma MGF extractor |

## Verification

```bash
lake build FormalSLT
lake env lean examples/CheckSubGammaExtractor.lean
```

The checker prints the axiom profile for the pointwise Bennett lemma,
conditional-expectation helpers, and the extractor theorem. The expected axiom
set is:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

This layer proves a conditional MGF extraction theorem. It does not state a
full sequential concentration theorem, choose a filtration, or prove an
anytime-valid bound by itself. Those statements can build on this extractor
once their martingale and measurability hypotheses are supplied.
