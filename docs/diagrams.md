# Theorem-family diagrams

Visual companion to [`theorem-map.md`](./theorem-map.md). The README embeds the
checked-in SVG hero ([`theorem-chain.svg`](./theorem-chain.svg)); this page
holds four detailed Mermaid diagrams that render directly on GitHub.

All four diagrams are conceptual theorem-family maps, not literal import
graphs. Exact assumptions live in the theorem signatures and the checker files
under [`examples/`](../examples). Solid nodes are machine-checked surfaces;
dashed slate nodes marked "(open)" are genuinely open work. Status is encoded
in the label and stroke style, not in color alone.

## A. Architecture and public imports

The intended dependency direction from [`ARCHITECTURE.md`](../ARCHITECTURE.md).
This is a rule for new and refactored code, not a claim that every legacy
import already follows it; mathematically necessary cross-subject imports are
narrow and documented in module docstrings.

[Open the static architecture view.](./architecture-flowchart.svg)

```mermaid
%%{init: {'theme': 'neutral', 'flowchart': {'rankSpacing': 46, 'nodeSpacing': 30}}}%%
flowchart TD
    found["Probability / LinearAlgebra / core definitions<br/>Risk, ERM, UniformConvergence"]
    conc["Concentration / Azuma"]
    subjects["Rademacher / VC / Covering / Stability /<br/>PACBayes / AnytimeValid"]
    apps["StochasticDynamics / OnlineToPAC / Statistics"]
    meta["TestTimeMeta<br/>application-level compositions"]

    found --> conc --> subjects --> apps --> meta

    classDef foundation fill:#eff6ff,stroke:#1d4ed8,color:#1e3a8a;
    classDef checked fill:#ecfdf5,stroke:#0f766e,color:#134e4a;
    classDef endpointNode fill:#fffbeb,stroke:#b45309,color:#78350f;
    class found foundation;
    class conc,subjects,apps checked;
    class meta endpointNode;
```

Public topic umbrellas: `FormalSLT.PACBayes`, `FormalSLT.VC`,
`FormalSLT.Sequential`, and `FormalSLT.StochasticDynamics` re-export their
subject surfaces; `FormalSLT.lean` is the whole-library build umbrella.

## B. Classical learning, entropy, and localization

The finite learning spine and the metric-entropy lane. The sharp McDiarmid
bound shown is two-sided. The localized lane is a checked but conservative
finite union-bound route; it is not a completed nonconservative
random-threshold fast-rate theorem.

```mermaid
%%{init: {'theme': 'neutral', 'flowchart': {'rankSpacing': 42, 'nodeSpacing': 26}}}%%
flowchart TD
    risk["Risk / ERM<br/>finite product samples"]
    ghost["Ghost samples<br/>genGap, piMeasure"]
    rad["Empirical Rademacher complexity"]
    sym["Symmetrization<br/>E[genGap] ≤ 2 E[Rad]"]
    mcd["Sharp McDiarmid, two-sided<br/>2 exp(−2 ε² / Σ cₖ²)"]
    hp["High-probability Rademacher bound"]
    massart["Massart finite-class bound"]
    fc["Finite-class high-probability bounds"]
    sauer["Sauer–Shelah +<br/>binary trace bridge"]
    vcb["VC bounds + ERM sample complexity"]
    contraction["Contraction, 1-Lipschitz +<br/>linear predictors"]
    nets["Finite nets + sub-Gaussian maxima"]
    chain["Multiscale chaining + entropy sums"]
    adapters["Integral comparison + boundary adapters<br/>total-bounded, separable-terminal"]
    dudleyend["Checked continuous entropy-integral endpoints<br/>under explicit stated hypotheses"]
    megen["Metric-entropy generalization<br/>mean + high probability"]
    localized["Localized finite-class Bernstein wrappers<br/>conservative union-bound route"]
    dudleyopen["Arbitrary measurable-supremum /<br/>non-finite-outcome Dudley (open)"]

    risk --> ghost --> sym
    rad --> sym
    rad --> massart
    rad --> contraction
    rad --> localized
    mcd --> hp
    sym --> hp
    massart --> fc
    hp --> fc
    sauer --> vcb
    massart --> vcb
    hp --> vcb
    nets --> chain
    chain --> adapters
    adapters --> dudleyend
    sym --> megen
    chain --> megen
    hp --> megen
    dudleyend -.-> dudleyopen

    classDef foundation fill:#eff6ff,stroke:#1d4ed8,color:#1e3a8a;
    classDef checked fill:#ecfdf5,stroke:#0f766e,color:#134e4a;
    classDef endpointNode fill:#fffbeb,stroke:#b45309,color:#78350f;
    classDef open fill:#f8fafc,stroke:#64748b,color:#334155,stroke-dasharray:6 4;
    class risk,ghost foundation;
    class rad,sym,mcd,hp,massart,fc,sauer,contraction,nets,chain,adapters,localized checked;
    class vcb,dudleyend,megen endpointNode;
    class dudleyopen open;
```

The localized wrappers consume finite Bernstein tails and finite union bounds
over the localized class; the algebraic centered-moment interfaces name the
whole-supremum obligation without discharging it.

## C. PAC-Bayes and empirical Bernstein

The classical change-of-measure branch contains fixed-tilt Catoni bounds and
fixed-budget or finite-predeclared-grid McAllester bounds. The separate-event
empirical-variance plus risk route assumes `n ≥ 2`, `0 < η · n < 2(n − 1)`,
and `0 < λ < 3n`; it uses separate `deltaVariance` and `deltaRisk` budgets,
supports separately weighted finite `η` and `λ` catalogs, and has two KL
appearances in the final bound. The joint route instead uses one predeclared
weighted finite `(t, η)` catalog and one shared event. Its entry may be selected
after seeing the sample and posterior, with one KL term plus that entry's
catalog-weighted confidence allocation. Those routes are fixed-sample and
finite-IID. The separate reverse-exchangeability route turns prefix means and
Bessel variances into reverse martingales, controls every prefix in each
dyadic epoch, and stitches the epochs into one infinite-IID event valid for
every `n >= 2`. All catalogs are declared before the sample is observed.

```mermaid
%%{init: {'theme': 'neutral', 'flowchart': {'rankSpacing': 42, 'nodeSpacing': 26}}}%%
flowchart TD
    subgraph scope["FIXED SAMPLE &middot; FINITE IID &middot; FINITE PREDECLARED CATALOGS"]
        kl["KL / Donsker–Varadhan<br/>finite change of measure"]
        pmgf["Finite product MGF bridge"]
        catoni["Catoni bounded-loss bound"]
        mcallester["McAllester fixed budget +<br/>finite-grid peeling"]
        bern["Bernstein route<br/>indicator variance, low-risk self-bound,<br/>weighted tilt catalogs"]
        bessel["Bessel empirical variance<br/>pairwise identity, IID unbiasedness"]
        matching["Random-matching lower-tail MGF"]
        varevent["Fixed-tilt variance event<br/>simultaneous over finite posteriors"]
        riskevent["Separate bounded-loss Bernstein<br/>risk event"]
        ebrisk["Observable empirical-Bernstein risk bound<br/>failure budget deltaVariance + deltaRisk"]
        tilt["Finite exponential change of measure<br/>coordinate + product identities"]
        jointmgf["Retained-Bennett joint<br/>mean/variance MGF"]
        jointcat["One-event weighted finite joint (t, η) catalog<br/>one KL term at the selected entry"]
        zerores["Balanced zero-residual endpoint"]
        xires["Exact attained ξ residual endpoint<br/>zero, v = 1/4, and interior branches"]
        sqrtbound["Closed-form logarithmic-grid endpoint<br/>5/4 square-root + 5/2 linear constants"]
    end
    countablemaster["Support-aware countable weighted master<br/>Nat-indexed (t, η), positive-weight prior moments"]
    countableposterior["Finite-posterior exact-ξ selector<br/>Nat-indexed tilt-pair catalog"]
    reversebessel["Reverse Bessel martingale<br/>leave-one-coordinate conditional identity"]
    reversejoint["Reverse joint mean/variance<br/>exponential submartingale + maximal bound"]
    reversegrid["Reverse dyadic-scale epoch endpoint<br/>all prefixes, all finite posteriors"]
    stitched["All-sample-size empirical-Bernstein event<br/>5/2 square-root + 5 linear constants"]
    allreal["All-real tilt optimization (open)"]
    continuousEB["Measurable/continuous-hypothesis<br/>all-sample-size extension (open)"]
    forwardEB["Forward exact-Bessel e-process +<br/>optional-stopping API (open)"]

    kl --> pmgf
    pmgf --> catoni
    catoni --> mcallester
    kl --> bern
    pmgf --> bern
    bessel --> matching
    matching --> varevent
    kl --> varevent
    pmgf --> riskevent
    varevent --> ebrisk
    riskevent --> ebrisk
    bessel --> tilt
    tilt --> jointmgf
    jointmgf --> jointcat
    jointcat --> zerores
    zerores --> xires
    zerores --> sqrtbound
    jointmgf --> countablemaster
    countablemaster --> countableposterior
    bessel --> reversebessel
    matching --> reversejoint
    reversebessel --> reversejoint
    reversejoint --> reversegrid
    reversegrid --> stitched
    jointcat -.-> allreal
    stitched -.-> continuousEB
    stitched -.-> forwardEB

    classDef checked fill:#ecfdf5,stroke:#0f766e,color:#134e4a;
    classDef endpointNode fill:#fffbeb,stroke:#b45309,color:#78350f;
    classDef open fill:#f8fafc,stroke:#64748b,color:#334155,stroke-dasharray:6 4;
    class kl,pmgf,catoni,bern,bessel,matching,varevent,riskevent,tilt,jointmgf,jointcat,countablemaster,countableposterior,reversebessel,reversejoint checked;
    class mcallester,ebrisk,zerores,xires,sqrtbound,reversegrid,stitched endpointNode;
    class allreal,continuousEB,forwardEB open;
```

The finite joint route thresholds one prior-and-catalog master mixture, so the
selected entry may depend on the sample and the posterior while paying one KL
term. Its closed-form endpoint fixes the dyadic grid in advance through
`Nat.clog 2 n` and proves the optimizer coverage inside Lean; it does not assume
a sample- or posterior-dependent grid choice. The checked countable foundation
controls every positive-weight prior moment through one support-aware master
event. Its downstream layer applies the finite Donsker–Varadhan and residual
theorems to a sample- and finite-posterior-selected natural-number entry on
that same event. The stitched endpoint instead uses a telescoping confidence
allocation across reverse dyadic epochs and one finite-prefix/infinite-product
measure bridge. It is an offline all-sample-size theorem, not a forward
e-process or optional-stopping result. The variance events
bound the posterior average of per-hypothesis variances; they do not bound the
variance of the posterior-averaged loss.

## D. Anytime-valid, Markov, and composition

The sequential lane, the finite Markov lane, and the composition surfaces.
The empirical-Bernstein confidence sequence uses a predictable
conditional-variance proxy, not the exact Bessel sample variance.

```mermaid
%%{init: {'theme': 'neutral', 'flowchart': {'rankSpacing': 42, 'nodeSpacing': 26}}}%%
flowchart TD
    condmgf["Conditional MGF<br/>sub-Gamma extractor"]
    supermart["Nonnegative supermartingales<br/>exponential processes"]
    ville["Ville maximal inequality"]
    eproc["e-processes<br/>Type-I control, optional continuation"]
    cs["Confidence sequences<br/>mixture, optimized-λ, dyadic-epoch, betting,<br/>empirical-Bernstein (predictable proxy)"]
    score["Score e-process + prior mixture"]
    tiltmix["Finite weighted hypothesis--tilt master<br/>one Ville event, selected atom"]
    pathwise["Pathwise PAC-Bayes compiler<br/>one event, all posteriors, all times"]
    tu["Time-uniform PAC-Bayes endpoints<br/>process-level finite tilt + finite-class IID<br/>+ spherical Gaussian"]
    pathlaw["Finite transition PMFs<br/>Ionescu–Tulcea path laws"]
    markovrisk["Markov conditional-risk certificates<br/>prequential risk, sharp 1/4 variance proxy"]
    markovpb["Markov prequential PAC-Bayes<br/>fixed tilt 0 &lt; λ &lt; 3, finite catalog"]
    otp["Online-to-PAC conversion<br/>explicit regret + deviation hypotheses"]
    stats["Statistics interfaces<br/>estimation, Fisher information,<br/>Cramér–Rao, exponential families"]
    pbc["Fixed-sample PAC-Bayes components<br/>(diagram C)"]
    prefix["Prefix-kernel deviation<br/>sharp McDiarmid"]
    ttm["TestTimeMeta five-slot composition<br/>McAllester · online/IID · Bernstein/Gaussian<br/>anytime/Ville · prefix-kernel"]
    markovopen1["Same-trajectory-trained or predictable<br/>Markov learners (open)"]
    markovopen2["Random initial laws, continuous state,<br/>stationary or mixing risk (open)"]
    otpopen["Algorithm-specific online<br/>regret theorem (open)"]

    condmgf --> supermart
    supermart --> ville
    ville --> eproc
    ville --> cs
    eproc --> score
    eproc --> tiltmix
    score --> pathwise
    tiltmix --> pathwise
    ville --> pathwise
    pathwise --> tu
    pathlaw --> markovrisk
    cs --> markovrisk
    markovrisk --> markovpb
    tu --> markovpb
    otp --> ttm
    cs --> ttm
    pbc --> ttm
    prefix --> ttm
    markovpb -.-> markovopen1
    markovpb -.-> markovopen2
    otp -.-> otpopen

    classDef checked fill:#ecfdf5,stroke:#0f766e,color:#134e4a;
    classDef sequential fill:#f5f3ff,stroke:#6d28d9,color:#4c1d95;
    classDef endpointNode fill:#fffbeb,stroke:#b45309,color:#78350f;
    classDef open fill:#f8fafc,stroke:#64748b,color:#334155,stroke-dasharray:6 4;
    class condmgf,pathlaw,markovrisk,otp,stats,pbc,prefix checked;
    class supermart,ville,eproc,cs,score,tiltmix,pathwise sequential;
    class tu,markovpb,ttm endpointNode;
    class markovopen1,markovopen2,otpopen open;
```

The statistics interfaces preserve the hypotheses of the Mathlib results they
expose; they are shown without arrows because no theorem family above depends
on them.

The five TestTimeMeta slots are McAllester, online/IID, Bernstein/Gaussian,
anytime/Ville, and the sharp-McDiarmid prefix-kernel deviation.

## Nonclaims

These diagrams do not claim more than the theorem signatures state:

- The fixed-time random-matching score is not an e-process.
- Terminal random matchings at different sample sizes are not projectively
  nested.
- The checked countable master and selector use a finite hypothesis type and
  finite posterior over a predeclared natural-number catalog; they are not a
  countable-hypothesis posterior, all-real tilt optimizer, or time-uniform
  process.
- The finite time-uniform tilt master selects one declared atom; it is not a
  countable mixture, an arbitrary joint hypothesis--tilt posterior, an all-real
  tilt optimizer, or an i.i.d. loss specialization.
- The generic forward time-uniform PAC-Bayes endpoints do not imply the
  exact-Bessel result. The checked exact-Bessel all-sample-size theorem instead
  uses offline reverse epochs and does not provide optional-stopping semantics.
- The posterior average of per-hypothesis variances is not the variance of
  the posterior-averaged loss.
- The checked Dudley boundary adapters are not an unrestricted
  arbitrary-measurable-supremum theory.
- The Gaussian time-uniform endpoints cover fixed spherical-Gaussian
  prior/posterior pairs and finite declared catalogs, not every posterior or
  every real tilt.
- The Markov certificates do not cover same-trajectory training, random
  initial laws, continuous state spaces, or stationary/mixing risk unless a
  theorem explicitly says so.
- No diagram on this page makes a novelty or priority claim; adjacent work is
  surveyed in [`related-work.md`](./related-work.md).

## See also

- [`frontier-diagram.svg`](./frontier-diagram.svg) for a static checked-versus-open overview.
- [`theorem-map.md`](./theorem-map.md) for exact theorem names and statements.
- [`proof-spine.md`](./proof-spine.md) for a narrative walkthrough.
- [`assumptions-and-nonclaims.md`](./assumptions-and-nonclaims.md) for the
  full scope statement.
- [`intuition.md`](./intuition.md) for plain-English explanations.
