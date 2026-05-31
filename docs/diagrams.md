# Theorem-Dependency Diagrams

Visual companion to [`theorem-map.md`](./theorem-map.md). The README uses the
checked-in SVG asset; this page keeps Mermaid versions for readers who want to
scan the proof graph directly on GitHub.

## Core finite-class spine

```mermaid
%%{init: {'flowchart': {'rankSpacing': 42, 'nodeSpacing': 24}, 'theme':'neutral'}}%%
flowchart BT
    risk["Risk / ERM<br/>populationRisk, empiricalRisk"]
    ghost["Ghost sample<br/>genGap, piMeasure"]
    rad["Empirical Rademacher<br/>Rad(H,S)"]
    sym["Symmetrization<br/><b>E[genGap] <= 2 E[Rad]</b>"]
    azuma["Azuma genGap tail<br/><b>exp(-eps^2 n / 8B^2)</b>"]
    hpr["High-probability Rademacher"]
    massart["Massart finite-class<br/><b>Rad <= B sqrt(2 log card(H) / n)</b>"]
    finite_hp["Finite-class high-probability bound"]
    udev["Uniform deviation"]
    erm["ERM excess-risk tail"]
    sauer["Sauer-Shelah<br/><b>sum C(n,k) <= (en/d)^d</b>"]
    effective["Effective-class Massart"]
    binary["Binary VC bridge<br/>0-1 loss patterns"]
    vc_rad["VC pointwise Rademacher"]
    vc_erm["VC-style ERM excess-risk tail"]

    risk --> ghost --> sym
    rad --> sym
    sym --> hpr
    azuma --> hpr
    hpr --> finite_hp
    massart --> finite_hp
    finite_hp --> udev --> erm
    massart --> effective
    binary --> effective
    sauer --> vc_rad
    effective --> vc_rad
    vc_rad --> vc_erm
    hpr --> vc_erm
    erm --> vc_erm

    classDef capstone fill:#111827,stroke:#2563eb,color:#f9fafb,stroke-width:2px;
    class vc_erm capstone
```

## Extensions now attached to the spine

```mermaid
%%{init: {'flowchart': {'rankSpacing': 40, 'nodeSpacing': 24}, 'theme':'neutral'}}%%
flowchart LR
    rad["Empirical Rademacher<br/>finite sample"]
    contraction["Finite scalar contraction<br/>Rad(phi o F) <= L Rad(F)"]
    linear["Finite-dimensional linear predictors<br/>Rad <= R/n sqrt(sum ||x_i||^2)"]
    covering["Finite covering numbers<br/>epsilon-net peeling"]
    two_scale["Two-scale finite chaining"]
    subg_max["Finite sub-Gaussian max<br/>MGF -> E sup bound"]
    finite_chain["Finite multiscale chaining<br/>projection-pair entropy budgets"]
    dudley_budget["Finite Dudley-style entropy-budget wrappers<br/>dyadic radius schedule"]

    rad --> contraction
    rad --> linear
    rad --> covering --> two_scale
    subg_max --> finite_chain --> dudley_budget
    covering --> finite_chain

    classDef foundation fill:#ecfeff,stroke:#0891b2,color:#164e63;
    classDef verified fill:#f0fdf4,stroke:#16a34a,color:#14532d;
    class rad foundation;
    class contraction,linear,covering,two_scale,subg_max,finite_chain,dudley_budget verified;
```

## Finite Dudley ladder

The chaining layer is deliberately finite. The current endpoint is a finite
dyadic entropy-budget statement, which is the right foundation before moving
toward integral comparisons.

```mermaid
flowchart TD
    mgf["Finite sub-Gaussian increment MGF"]
    max_log["Finite-max entropy budget<br/>(log |T| + q) / lambda"]
    max_sqrt["Optimized finite max<br/>sqrt(2 sigma^2 log |T|)"]
    nets["Finite nets and nearest projections"]
    pairs["Realized projection-pair families"]
    chain["Finite multiscale chaining decomposition"]
    sum["Finite Dudley-style entropy sum"]
    dyadic["Geometric radius schedule"]
    budget["Per-scale entropy-budget wrapper"]
    future["Next: finite discrete entropy-bound refinement"]

    mgf --> max_log --> max_sqrt
    nets --> pairs --> chain
    max_sqrt --> chain --> sum --> dyadic --> budget --> future
```

## Where each definition first appears

```mermaid
flowchart LR
    Risk["Risk.lean<br/>populationRisk, empiricalRisk"]
    ERM["ERM.lean<br/>ermPolicy, excessRisk"]
    GhostSample["GhostSample.lean<br/>genGap, piMeasure"]
    RadFS["Rademacher/FiniteSample.lean<br/>empiricalRademacherComplexity"]
    VCDim["VC/Dimension.lean<br/>shatters, vcDim"]
    VCRad["VC/Rademacher.lean<br/>effectiveClass"]
    VCBridge["VC/PACBridge.lean<br/>binaryClassTrace"]
    Chain["Covering/FiniteSubGaussianChaining.lean<br/>FiniteNet, finiteSup, entropy budgets"]

    Risk --> ERM
    Risk --> GhostSample
    GhostSample --> RadFS
    VCDim --> VCRad
    VCDim --> VCBridge
    RadFS --> VCRad
```

## See also

- [`theorem-map.md`](./theorem-map.md) for exact theorem names and statements.
- [`proof-spine.md`](./proof-spine.md) for a narrative walkthrough.
- [`assumptions-and-nonclaims.md`](./assumptions-and-nonclaims.md) for scope and assumptions.
- [`intuition.md`](./intuition.md) for plain-English explanations.
