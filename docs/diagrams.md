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

## Unit-interval Dudley example

```mermaid
flowchart LR
    unit["UnitInterval = [0,1]"]
    tb["TotallyBounded Set.univ"]
    half["half mesh<br/>3 centers, radius 1/4"]
    quarter["quarter mesh<br/>5 centers, radius 1/8"]
    process["Rademacher linear process<br/>X(b,t)=sign(b)*t"]
    mgf["increment MGF"]
    inc["projection-pair increment<br/>sqrt(log 15)"]
    projected["projected quarter-mesh Dudley bound"]
    supplied["supplied supremum bound<br/>E[sup] <= projected bound"]

    unit --> tb
    unit --> half --> inc
    unit --> quarter --> inc
    process --> mgf --> inc --> projected --> supplied

    classDef index fill:#eff6ff,stroke:#2563eb,color:#1e3a8a;
    classDef checked fill:#f0fdf4,stroke:#16a34a,color:#14532d;
    class unit,tb index;
    class half,quarter,process,mgf,inc,projected,supplied checked;
## Conditional concentration toolkit

The concentration layer now has both the conditional sub-gamma MGF extractor
(`Concentration.SubGamma.*`) and the sharp bounded-differences route through
the exposure martingale.

```mermaid
flowchart TD
    bounded["Bounded increment<br/>|X| ≤ b a.s."]
    center["Conditional centering<br/>μ[X | m] = 0"]
    var["Conditional second moment<br/>μ[X² | m] ≤ σ²"]
    bennett["Bennett-Taylor pointwise inequality<br/>exp(λx) ≤ 1 + λx + λ²x²/(2(1−bλ/3))"]
    toolkit["Conditional-expectation toolkit<br/>Jensen, Markov, product, variance-from-square"]
    extractor["<b>Conditional sub-gamma MGF extractor</b><br/>μ[exp(λX) | m] ≤ exp(σ²λ²/(2(1−bλ/3))) on b·λ &lt; 3"]
    sharp["Sharp McDiarmid genGap tail<br/><b>exp(-eps^2 n / 2B^2)</b>"]

    bounded --> extractor
    center --> extractor
    var --> extractor
    bennett --> extractor
    toolkit --> extractor
    bounded --> sharp
    center --> sharp
    toolkit --> sharp

    classDef verified fill:#f5f3ff,stroke:#7c3aed,color:#3b0764;
    classDef future fill:#f8fafc,stroke:#94a3b8,color:#475569,stroke-dasharray: 5 4;
    class bennett,toolkit,extractor,sharp verified;
```

## Total-bounded Dudley boundary adapters

The finite Dudley entropy-budget layer now feeds a chain of total-bounded
boundary adapters (`Covering.TotalBoundedDudley`). Each step discharges more of
the continuous-boundary hypotheses from finite, checkable data; the continuous
Dudley entropy integral remains the open endpoint.

```mermaid
flowchart TD
    budgets["Finite Dudley entropy budgets<br/>dyadic radius schedule"]
    netsched["Total-bounded dyadic finite-net schedules<br/>projected-sup / projected finite-net wrappers"]
    interval["Truncated interval-integral entropy comparison"]
    supplied["Supplied-supremum boundary adapter<br/>explicit terminal approximation error"]
    skeleton["Finite-skeleton / dense-net boundary adapter<br/>separability + terminal projection errors"]
    epsilonized["Epsilonized finite-choice boundary adapter<br/>every ε > 0 dischargeable"]
    eliminate["ε-elimination under uniform global finite budget"]
    separable["Separable-terminal Dudley boundary adapter"]
    pathwise["Pathwise terminal-modulus constructor<br/>+ finite-cover/pathwise-modulus bridge"]
    future["Next: continuous Dudley entropy-integral theorem<br/>(open)"]

    budgets --> netsched --> interval
    interval --> supplied --> epsilonized
    interval --> skeleton --> epsilonized
    epsilonized --> eliminate --> separable
    skeleton --> separable
    pathwise --> separable
    separable -.-> future

    classDef verified fill:#f0fdf4,stroke:#16a34a,color:#14532d;
    classDef future fill:#f8fafc,stroke:#94a3b8,color:#475569,stroke-dasharray: 5 4;
    class budgets,netsched,interval,supplied,skeleton,epsilonized,eliminate,separable,pathwise verified;
    class future future;
```

## PAC-Bayes finite confidence layer

The PAC-Bayes lane runs from the KL/Donsker-Varadhan change of measure through
a finite Catoni-style bound to a finite-grid McAllester peeling wrapper for
posterior-dependent penalties.

```mermaid
flowchart TD
    kl["KL / Donsker-Varadhan<br/>finite change of measure"]
    mgf["Finite iid product MGF bridge"]
    catoni["Bounded-loss MGF + Markov<br/>finite Catoni-style bound"]
    payoff["Closed high-confidence good-event payoff"]
    fixed["Fixed-budget McAllester square-root corollary"]
    peeling["<b>Finite-grid McAllester peeling</b><br/>posterior-dependent penalty"]
    optimized["Optimized finite-grid wrapper"]
    future["Next: all-real-λ / continuous-posterior extensions<br/>(open)"]

    kl --> mgf --> catoni --> payoff --> fixed --> peeling --> optimized
    optimized -.-> future

    classDef verified fill:#f0fdf4,stroke:#16a34a,color:#14532d;
    classDef future fill:#f8fafc,stroke:#94a3b8,color:#475569,stroke-dasharray: 5 4;
    class kl,mgf,catoni,payoff,fixed,peeling,optimized verified;
    class future future;
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
