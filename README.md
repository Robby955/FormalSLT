# FormalSLT

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Docs](https://github.com/Robby955/FormalSLT/actions/workflows/docs.yml/badge.svg?branch=main)](https://robby955.github.io/FormalSLT/)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-905b958-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

**Machine-checked learning theory for adaptive and dependent data.**

FormalSLT is a Lean 4 library for PAC-Bayes bounds, anytime-valid inference,
adaptive trajectories, and stationary-risk certification. Public results come
with Lean source, focused checker files, and explicit assumptions.

[Research guide](https://robby955.github.io/FormalSLT/) ·
[Install](#use-the-library) ·
[Browse by concept](https://robby955.github.io/FormalSLT/theorems/) ·
[Verify](#verification)

FormalSLT v0.2 is being prepared from `main`. It is not released yet;
`v0.1.0` remains the latest tagged version. See the
[v0.2 candidate record](./docs/releases/v0.2.0.md) for the exact release
boundary.

## What is proved

The results below are checked in Lean. Some applications require supplied
certificates; the [scope ledger](./docs/assumptions-and-nonclaims.md) records
the complete assumptions, nonclaims, and open endpoints.

### Empirical-Bernstein PAC-Bayes at every sample size

One event on an infinite IID path controls every sample size `n ≥ 2` and every
admissible posterior. The bound uses Bessel sample variance and
measure-theoretic KL divergence.

**Boundary:** this is an offline all-sample-size result, not an optional-stopping
claim. The separate forward route uses predictable residuals.

[Lean source](./FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean) ·
[checker](./examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean) ·
[positive-KL example](./examples/CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean)

### Adaptive trajectory inference

The finite-state result permits path- and time-dependent posterior selection
from score and tilt catalogs fixed before scoring, with a selected width that
tends to zero. A second result handles arbitrary measurable state and
hypothesis spaces under a joint measurability contract.

**Boundary:** both results start from a deterministic initial state and target
prefix-conditional risk. They do not turn predictors chosen after observing
their scored outcomes into valid candidates.

[finite-state source](./FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.lean) ·
[measurable-space source](./FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean) ·
[informative checker](./examples/CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.lean)

### Stationary risk with known and unknown kernels

The stationary layer combines prequential bounds with finite-depth Poisson
corrections. One route handles a known contracting finite kernel. Another adds
same-trajectory transition confidence over a predeclared finite candidate
family.

**Boundary:** the known-kernel route takes an invariant law, contraction, and
oscillation certificate as inputs. The unknown-kernel route requires positive
row visits and strict selected contraction; it does not estimate an arbitrary
kernel without structure or coverage conditions.

[known-kernel source](./FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.lean) ·
[unknown-kernel source](./FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean) ·
[informative checker](./examples/CheckEmpiricalStationaryCatalogInformative.lean)

The [theorem map](./docs/theorem-map.md) lists the supported endpoints and their
exact Lean names.

## Flagship application: a controlled queue

The main application is a 24-state, two-action controlled queue with a frozen,
replayable trace. In the declared one-parameter refresh family, the
transition-confidence calculation replaces the generic 4,608-coordinate
construction with one persistence-hit count. On the retrospective trace, Lean
proves that a rational endpoint whose decimal expansion begins
`0.068710707605557...` is below `69/1000`. For each fixed admissible refresh
parameter, Lean also bounds by `1/20` the outer mass of paths that reproduce
that histogram while violating the displayed risk conclusion.

This is a retrospective demonstration under the stated refresh-family model.
It is not a prospective result, a family-membership test, or a guarantee for
arbitrary unknown kernels.

[Application overview](./applications/controlled_queue/README.md) ·
[design and evidence ledger](./docs/controlled-queue-application-design.md) ·
[checked receipt](./FormalSLT/Applications/ControlledQueueSharpStructuredRetrospectiveReceipt.lean)

Applications are opt-in through `import FormalSLT.Applications`; they are not
part of the stable topic-import promise.

## Use the library

FormalSLT uses Lean 4.32.2 and Mathlib 4.32.2. The four supported topic imports
are:

```lean
import FormalSLT.PACBayes
import FormalSLT.Sequential
import FormalSLT.StochasticDynamics
import FormalSLT.VC
```

Use the latest tagged release for stable work:

```lean
require «formal-slt» from git
  "https://github.com/Robby955/FormalSLT.git" @ "v0.1.0"
```

To test the merged v0.2 candidate before release, pin its exact integration
commit rather than moving `main`:

```lean
require «formal-slt» from git
  "https://github.com/Robby955/FormalSLT.git" @
  "660b03a4f5003acb4337b5c9f3aab21218ff31fc"
```

In the downstream Lake project, run:

```bash
lake update
lake exe cache get
lake build
```

Repository maintainers can run `make downstream` from a FormalSLT checkout to
exercise the bundled external-consumer fixture.

The [API policy](./docs/api-stability.md) defines the 19 candidate v0.2
declarations and the compatibility rules.

## Find what you need

- **Statistics and ML:** [bounds, assumptions, and receipts](https://robby955.github.io/FormalSLT/readers/stats-ml/)
- **Probability:** [e-processes, path laws, and Poisson equations](https://robby955.github.io/FormalSLT/readers/probability/)
- **Lean:** [imports, theorem names, and source layout](https://robby955.github.io/FormalSLT/readers/lean/)
- **Verification:** [axioms, fidelity gates, and release checks](https://robby955.github.io/FormalSLT/readers/verification/)
- **Search:** [concept index](./docs/INDEX.md) · [declaration search](https://robby955.github.io/FormalSLT/search.html)

## Verification

[![theorems and lemmas](https://img.shields.io/badge/theorems%2Flemmas-4%2C232-brightgreen.svg)](#verification)
[![FormalSLT modules](https://img.shields.io/badge/FormalSLT%20modules-291-blue.svg)](#verification)
[![Lean lines](https://img.shields.io/badge/Lean%20lines-154%2C217-brightgreen.svg)](#verification)

The line count covers the library and examples, including the generated
controlled-queue data module. The curated public theorem surface reports only
`[propext, Classical.choice, Quot.sound]`. The checked library and examples
contain no executable `sorry` or `admit`, no custom axiom or constant
declarations, and no uses of `native_decide`.

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

The [release checklist](./docs/public-release-checklist.md) contains the full
exact-SHA gate, including statement-fidelity, application, artifact, and
fresh-tag installation checks.

## Scope, sources, and citation

The [scope ledger](./docs/assumptions-and-nonclaims.md) distinguishes proved,
conditional, and open endpoints. The [literature ledger](./docs/LITERATURE.md)
records agreement and differences with prior mathematics; the
[source map](./docs/references.md) and [related-work guide](./docs/related-work.md)
record mathematical and formalization provenance. Lean signatures and checker
files remain authoritative.

An earlier paper based on FormalSLT was accepted to the ICML 2026 AI for Math
workshop:
[*From Agents to Axioms: Verifier-Gated Lean Formalization for Statistical Learning Theory*](https://openreview.net/pdf?id=EsEqPLc0ef).

Use [CITATION.cff](./CITATION.cff) for the current software citation. A v0.2 DOI
will be citable only after the exact tagged artifact, GitHub Release, and
archival deposit are published.

## Contributing

Read [CONTRIBUTING.md](./CONTRIBUTING.md) and
[Good first issues](./docs/good-first-issues.md). New public theorems need a
focused checker, an axiom receipt, and explicit scope.

## License

MIT. See [LICENSE](./LICENSE).
