# FormalSLT

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Docs](https://github.com/Robby955/FormalSLT/actions/workflows/docs.yml/badge.svg?branch=main)](https://robby955.github.io/FormalSLT/)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-905b958-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

[![theorems and lemmas](https://img.shields.io/badge/theorems%2Flemmas-4%2C232-brightgreen.svg)](#verification)
[![FormalSLT modules](https://img.shields.io/badge/FormalSLT%20modules-291-blue.svg)](#use-the-library)
[![Lean lines](https://img.shields.io/badge/Lean%20lines-154%2C217-brightgreen.svg)](#verification)
[![Zero sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#verification)
[![Axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-brightgreen.svg)](#verification)

The `154,217` count covers the library and examples, including the 4,867-line
generated data-definition module `FormalSLT/Applications/ControlledQueueData.lean`.

FormalSLT is a Lean 4 library for **machine-checked statistical learning under
adaptive and dependent data**. Its main results connect empirical-Bernstein
PAC-Bayes bounds, anytime-valid inference, prefix-dependent trajectories,
Poisson equations, contraction, and empirical transition certificates.

[Start with the research guide](https://robby955.github.io/FormalSLT/) ·
[search by mathematical concept](https://robby955.github.io/FormalSLT/theorems/) ·
[browse Lean declarations](https://robby955.github.io/FormalSLT/search.html) ·
[read the theorem map](./docs/theorem-map.md)

FormalSLT v0.1.0 was tagged on May 8, 2026; it has no GitHub Release or DOI.
The larger theorem program is integrated in the v0.2 release candidate, but
`v0.2.0` is **not released**: no v0.2 tag, GitHub Release, archived artifact, or
DOI is asserted. See the [candidate record](./docs/releases/v0.2.0.md) and
[changelog](./CHANGELOG.md).

## Choose a result

Proof status and literature status are separate. **PROVED** means Lean closes
the stated signature; **CONDITIONAL** flags a material supplied certificate or
open premise; **OPEN** means the endpoint is absent. **REPRODUCTION**,
**SPECIALIZATION**, and **DERIVED VARIANT** describe agreement with prior
mathematics. A theorem can be both **PROVED** and a **DERIVED VARIANT**. The
theorem signature, not the prose, is authoritative, and the repository makes no
novelty or priority claim without a versioned literature audit.

| If you need | Start with | Essential boundary | Status |
|---|---|---|---|
| IID empirical-Bernstein PAC-Bayes for every sample size <code>n ≥ 2</code> | <code>FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event</code> | Finite-valued IID observations; offline reverse stitching; no optional-stopping claim | **PROVED · DERIVED VARIANT** |
| Adaptive finite-state trajectory inference with a selected width tending to zero | <code>FormalSLT.StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event</code> | Deterministic start; fixed finite score catalog; countable confidence allocation is not itself a master e-process | **PROVED · DERIVED VARIANT** |
| Adaptive inference on arbitrary measurable state and hypothesis spaces | <code>FormalSLT.StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event</code> | Deterministic start; finite tilt catalog; supplied jointly measurable score family | **PROVED · DERIVED VARIANT** |
| Stationary risk for a known contracting finite kernel | <code>FormalSLT.StochasticDynamics.exists_stationaryPoissonDepthSelection_allTime_vanishing_event</code> | Supplied invariant law, strict contraction, and a uniform centered row-risk oscillation bound | **PROVED · CONDITIONAL INPUTS · LITERATURE AUDIT PENDING** |
| Same-trajectory certification with an unknown finite kernel | <code>FormalSLT.StochasticDynamics.exists_selectedCanonicalEmpiricalStationaryCatalog_event</code> | Predeclared finite candidates; every source row visited; strict selected contraction for uniqueness | **PROVED · LITERATURE AUDIT PENDING** |

The [scope ledger](./docs/assumptions-and-nonclaims.md) records the full
assumption and nonclaim boundary.

## Three result families

### 1. All-sample-size empirical-Bernstein PAC-Bayes

One posterior-independent event on an infinite IID path space controls every
sample size `n ≥ 2` and every admissible posterior measure, using Bessel sample
variance and measure-theoretic KL. This endpoint is offline: it is not a forward
e-process and does not authorize optional stopping. The separate forward route
uses predictable residuals; its hybrid Bessel expression is a checked pointwise
lower envelope, not itself an e-process.

[Endpoint](./FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean) ·
[checker](./examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean) ·
[positive-KL receipt](./examples/CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean)

### 2. Adaptive trajectory inference

The finite-state endpoint supports path- and time-dependent posterior selection
over a score and tilt catalog fixed before scoring, with a selected boundary
tending to zero. A second endpoint supports arbitrary measurable state and
hypothesis spaces under a joint score-measurability contract. Both target
encountered prefix-conditional risk, not stationary risk or predictors invented
after observing their scored outcomes.

[Finite-state endpoint](./FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.lean) ·
[measurable endpoint](./FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean) ·
[trajectory receipt](./examples/CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.lean)

### 3. Stationary Poisson and unknown-kernel certification

The stationary layer combines prequential bounds with finite-depth Poisson
corrections. The known-kernel result requires a supplied invariant law,
contraction, and oscillation bound. The unknown-kernel result adds same-path
transition confidence over predeclared candidates. Normalized radii require
positive limiting row frequencies; candidate-budget convergence also requires
empirical discrepancy convergence. Invariant-law uniqueness requires a strict
contraction certificate, and the chosen finite invariant PMF is a witness, not
an executable stationary solver.

[Known-kernel endpoint](./FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.lean) ·
[unknown-kernel endpoint](./FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean) ·
[informative receipt](./examples/CheckEmpiricalStationaryCatalogInformative.lean)

![FormalSLT flagship theorem chain](./docs/theorem-chain.svg)

This diagram is a theorem-family map, not a literal import graph. Solid nodes
name checked surfaces; conditional and open nodes state real boundaries.

## Read FormalSLT from your field

| Reader | Route |
|---|---|
| Statistics and ML | [Bounds, assumptions, receipts, and matched benchmarks](https://robby955.github.io/FormalSLT/readers/stats-ml/) |
| Probability | [e-processes, path laws, Poisson equations, and contraction](https://robby955.github.io/FormalSLT/readers/probability/) |
| Lean | [Topic imports, theorem names, and source organization](https://robby955.github.io/FormalSLT/readers/lean/) |
| Verification | [Axiom receipts, statement-fidelity gates, and release checks](https://robby955.github.io/FormalSLT/readers/verification/) |

For exhaustive detail, use the [concept index](./docs/INDEX.md),
[theorem map](./docs/theorem-map.md), [literature ledger](./docs/LITERATURE.md),
and [proof frontier](./docs/proof-frontier.md).

## Current boundaries

| Boundary | Current status |
|---|---|
| Arbitrary measurable hypotheses for IID empirical-Bernstein PAC-Bayes | **PROVED**, with finite-valued observations |
| Arbitrary measurable states and hypotheses for prefix trajectories | **PROVED**, with deterministic start and finite predeclared tilts |
| Countable tilt master e-process | **PROVED** for finite hypotheses and fixed conditional means |
| Countable finite-state trajectory selector | **PROVED** by confidence allocation; not claimed to be a countable master e-process |
| Unknown finite transition kernel | **PROVED** under positive row visits and declared candidate semantics |
| Sharp constant-one LIL boundary floor | **CONDITIONAL** on the explicit open <code>FairSignUpperLIL</code> premise and bounded normalized ratio |
| All-real or arbitrary predictable tilt optimization | **OPEN** |
| Continuous-state stationary Poisson certification | **OPEN** |

## Use the library

FormalSLT uses Lean 4.32.2 and Mathlib 4.32.2. Prefer one supported topic
import over the root convenience umbrella:

```lean
import FormalSLT.PACBayes
import FormalSLT.Sequential
import FormalSLT.StochasticDynamics
import FormalSLT.VC
```

The [candidate API policy](./docs/api-stability.md) endorses 19 declarations.
Each topic has an isolated checker under
[examples/stable_imports](./examples/stable_imports); application declarations
are not part of that compatibility promise.

For the released v0.1 API:

```lean
require «formal-slt» from git
  "https://github.com/Robby955/FormalSLT.git" @ "v0.1.0"
```

For the exact tested v0.2 theorem/API candidate at this documentation
checkpoint:

```lean
require «formal-slt» from git
  "https://github.com/Robby955/FormalSLT.git" @
  "e3acdaf5687408c202e7557cded7158292cd83d1"
```

That SHA is the latest recorded exact-head hosted-CI checkpoint, not a release
tag or DOI-backed artifact. Until `v0.2.0` exists, pin an exact tested candidate
commit rather than moving `main`.

```bash
lake exe cache get
lake build FormalSLT
make api
make downstream
```

`make downstream` builds a separate Lake package with one concrete module for
each supported topic import.

## Applications

Applications are opt-in through `import FormalSLT.Applications`:

- [20-state random-refresh load application](./docs/random-refresh-load-application.md)
- [24-state controlled-queue design and evidence ledger](./docs/controlled-queue-application-design.md)
- [controlled-queue protocol and commands](./applications/controlled_queue/README.md)

The controlled-queue repository contains checked retrospective and known-kernel
receipts plus a frozen prospective protocol. It contains **no fresh prospective
trace, receipt, or numerical result**. The oracle true-kernel and fixed-range
comparison rows are arithmetic-only `PLANNED_NOT_CHECKED` noncertificates; their
`1/20` entries are planned allocations, not checked outer-mass bounds. The named
retrospective suffix histogram now bounds the sharp structured pathwise boundary
by the exact observable endpoint `0.068710707605557... < 0.069`. For every fixed
admissible parameter in the
well-specified one-parameter refresh family, under the path law started at
`(action = 1, state = 1)`, Lean bounds by `1/20` the outer mass of the paths on
which that histogram occurs while the displayed risk conclusion fails. This is
pointwise in the fixed parameter and unconditional under that fixed-initial
path law; it is not coverage conditional on the histogram or one event
simultaneous over all parameters. The named deterministic path is not proved to
lie in a particular good event, and refresh-family well-specification is an
assumption rather than a tested conclusion.

## Verification

The curated public theorem surface reports only
`[propext, Classical.choice, Quot.sound]`. The checked library and examples have
no executable `sorry`, `admit`, custom axiom, or custom constant declarations.

```bash
lake exe cache get
lake build FormalSLT
make examples
make tutorials
make api
make downstream
python3 scripts/generate_badge_counts.py --check
python3 scripts/check_doc_anchors.py --self-test
git diff --check
```

The [release checklist](./docs/public-release-checklist.md) records the complete
exact-SHA gate, including statement fidelity, application code-freeze checks,
repository-tool tests, documentation generation, and fresh tag-install smoke.

## Provenance and citation

The [source map](./docs/references.md) records mathematical sources; the
[literature ledger](./docs/LITERATURE.md) records agreement, differences, and
review requirements; [related work](./docs/related-work.md) records other formal
libraries. Lean theorem signatures and checker files remain authoritative.

An earlier verifier-gated route built on FormalSLT was accepted at the ICML 2026
AI for Math workshop: [*From Agents to Axioms: Verifier-Gated Lean Formalization
for Statistical Learning Theory*](https://openreview.net/pdf?id=EsEqPLc0ef).

Use [CITATION.cff](./CITATION.cff) for the current software citation. A v0.2 DOI
is citable only after the archival deposit and GitHub Release are published and
the DOI resolves to the exact tagged artifact.

## Contributing

Read [CONTRIBUTING.md](./CONTRIBUTING.md) and
[Good first issues](./docs/good-first-issues.md). New public theorems require a
focused checker, `#print axioms` receipt, explicit scope, and repository gates.

## License

MIT. See [LICENSE](./LICENSE).
