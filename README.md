# FormalSLT

[![CI](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Robby955/FormalSLT/actions/workflows/ci.yml)
[![Docs](https://github.com/Robby955/FormalSLT/actions/workflows/docs.yml/badge.svg?branch=main)](https://robby955.github.io/FormalSLT/)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-905b958-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

[![theorems and lemmas](https://img.shields.io/badge/theorems%2Flemmas-4%2C217-brightgreen.svg)](#checked-surfaces)
[![FormalSLT modules](https://img.shields.io/badge/FormalSLT%20modules-290-blue.svg)](#module-map)
[![Lean lines](https://img.shields.io/badge/Lean%20lines-153%2C453-brightgreen.svg)](#audit-commands)
[![Zero sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#audit-commands)
[![Axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-brightgreen.svg)](#audit-commands)

The Lean-line badge follows the repository-wide library-plus-examples count.
That total includes the 4,867-line generated
`FormalSLT/Applications/ControlledQueueData.lean` exact-table module; those
lines are generated definitions and data, not hand-written theorem source.

FormalSLT is a Lean 4 library for **machine-checked statistical learning under
adaptive and dependent data**. Its main results connect empirical-Bernstein
PAC-Bayes bounds, anytime-valid inference, prefix-dependent trajectories,
Poisson equations, contraction, and empirical transition certificates.

[Start with the research guide](https://robby955.github.io/FormalSLT/) ·
[Search by mathematical concept](https://robby955.github.io/FormalSLT/theorems/) ·
[Browse declaration docs](https://robby955.github.io/FormalSLT/search.html) ·
[Read the theorem map](./docs/theorem-map.md)

FormalSLT v0.1.0 was tagged on May 8, 2026; no GitHub Release or DOI was issued
for that version. The larger theorem program is now integrated in the v0.2
release candidate, while the public release artifact is being prepared. See
the [changelog](./CHANGELOG.md) and [v0.2.0 candidate
record](./docs/releases/v0.2.0.md). Until the v0.2 tag exists, pin an exact
commit rather than treating <code>main</code> as a compatibility promise.

## Classification

FormalSLT uses two independent labels.

| Axis | Labels | Meaning |
|---|---|---|
| Proof closure | **PROVED**, **CONDITIONAL**, **OPEN** | Whether Lean closes the stated claim, whether a substantive certificate or unproved premise remains an input, or whether the theorem is absent |
| Literature fidelity | **REPRODUCTION**, **SPECIALIZATION**, **DERIVED VARIANT** | How the checked endpoint relates to the mathematical source |

A theorem can be both **PROVED** and a **DERIVED VARIANT**. Ordinary hypotheses
in a theorem signature are not hidden; **CONDITIONAL** is used when the public
application claim materially relies on a supplied certificate or an explicitly
unproved proposition. FormalSLT makes no novelty or priority claim without a
versioned literature audit.

## Checked surfaces

### Choose your theorem

| If you need | Start with | Essential boundary | Status |
|---|---|---|---|
| IID empirical-Bernstein PAC-Bayes for every sample size <code>n ≥ 2</code> | <code>FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event</code> | Finite-valued IID observations; offline reverse stitching; no optional-stopping claim | **PROVED · DERIVED VARIANT** |
| Adaptive finite-state trajectory inference with a selected width tending to zero | <code>FormalSLT.StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event</code> | Deterministic start; fixed finite score catalog; countable confidence allocation is not itself a master e-process | **PROVED · DERIVED VARIANT** |
| Adaptive inference on arbitrary measurable state and hypothesis spaces | <code>FormalSLT.StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event</code> | Deterministic start; finite tilt catalog; supplied jointly measurable score family | **PROVED · DERIVED VARIANT** |
| Stationary risk for a known contracting finite kernel | <code>FormalSLT.StochasticDynamics.exists_stationaryPoissonDepthSelection_allTime_vanishing_event</code> | Supplied invariant law, strict contraction, and a uniform centered row-risk oscillation bound | **PROVED · CONDITIONAL INPUTS · LITERATURE AUDIT PENDING** |
| Same-trajectory certification with an unknown finite kernel | <code>FormalSLT.StochasticDynamics.exists_selectedCanonicalEmpiricalStationaryCatalog_event</code> | Predeclared finite candidates; every source row visited; strict selected contraction for uniqueness | **PROVED · LITERATURE AUDIT PENDING** |

The curated discovery catalog is in the
[concept index](./docs/INDEX.md) and [theorem map](./docs/theorem-map.md).
The [scope ledger](./docs/assumptions-and-nonclaims.md) is authoritative for
boundaries that do not fit in this table.

### 1. All-sample-size empirical-Bernstein PAC-Bayes

The offline IID endpoint gives one posterior-independent event on an infinite
product path space. Outside it, every <code>n ≥ 2</code> and every admissible
posterior measure satisfy a square-root-plus-linear empirical-Bernstein bound
using the posterior integral of each hypothesis's Bessel sample variance and
one measure-theoretic KL term.

- Endpoint:
  [ContinuousInfiniteEmpiricalBernsteinStitch.lean](./FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean)
- Axiom and statement checker:
  [CheckContinuousInfiniteEmpiricalBernsteinStitch.lean](./examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean)
- Positive-KL continuous receipt:
  [CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean](./examples/CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean)
- Identical-input numerical benchmark:
  [empirical_bernstein_flagship.md](./benchmark/output/empirical_bernstein_flagship.md)

This theorem is all-sample-size but offline: it is not a forward e-process and
does not authorize optional stopping. A separate forward lane proves the actual
predictable-residual e-process, finite and countable tilt mixtures, and a
finite-hypothesis selected boundary tending to zero. Its hybrid Bessel
expression is a checked pointwise lower envelope of that e-process, not itself
claimed to be an e-process.

### 2. Adaptive trajectory inference

For a full-prefix probability kernel, a score may encode a fixed-in-advance
online prediction rule and inspect the complete available prefix before the
next outcome. FormalSLT derives the encountered one-step conditional risk and
the predictable residual process, then places every time, posterior, and
declared tilt atom under one common outer-mass guarantee.

The finite-state countable-allocation endpoint permits path- and time-dependent
posterior selection and proves the prescribed selected boundary tends to zero.
The measurable endpoint instead permits arbitrary measurable state and
hypothesis spaces under one joint score-measurability contract.

- Finite-state vanishing endpoint:
  [TrajectoryEmpiricalBernsteinPACBayesCountable.lean](./FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.lean)
- Informative trajectory receipt:
  [CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.lean](./examples/CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.lean)
- Arbitrary-state and arbitrary-hypothesis endpoint:
  [ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean](./FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean)
- Measurability checker:
  [CheckContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean](./examples/CheckContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.lean)

“Adaptive” does not mean that new predictors may be invented after their
scored outcomes. The target is encountered prefix-conditional risk, not
stationary risk, multistep prediction, or target-policy value.

### 3. Stationary Poisson and unknown-kernel certification

The stationary lane converts prequential trajectory bounds into stationary-risk
certificates. It formalizes Poisson telescoping, finite-depth potentials,
geometric truncation residuals, computable finite Dobrushin coefficients, and
confidence-allocated depth selection. For a known contracting finite kernel,
the selected stationary boundary tends to zero under a supplied uniform bound
on each score's centered row-risk oscillation.

The unknown-kernel lane adds coordinatewise empirical transition confidence,
row and whole-kernel total-variation certificates, finite invariant-law
existence, robust candidate transfer, and a same-trajectory finite
candidate/depth catalog. Candidate choice can occur after the path only within
the catalog fixed before scoring.

A separate countable geometric transition-tilt extension gives one
outer-mass event over every natural-number atom and an explicit selected
coordinate boundary tending to zero. Normalized row radii additionally require
positive limiting row-visit frequencies. A selected candidate-kernel budget
tends to zero only when its empirical row discrepancies also tend to zero; the
theorem is not an unconditional kernel-consistency claim.

- Known-kernel depth selection:
  [StationaryPoissonDepthSelection.lean](./FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.lean)
- Known-kernel checker:
  [CheckStationaryPoissonDepthSelection.lean](./examples/CheckStationaryPoissonDepthSelection.lean)
- Empirical transition confidence:
  [EmpiricalTransitionConfidence.lean](./FormalSLT/StochasticDynamics/EmpiricalTransitionConfidence.lean)
- Countable transition confidence:
  [EmpiricalTransitionConfidenceCountable.lean](./FormalSLT/StochasticDynamics/EmpiricalTransitionConfidenceCountable.lean)
- Countable transition checker:
  [CheckEmpiricalTransitionConfidenceCountable.lean](./examples/CheckEmpiricalTransitionConfidenceCountable.lean)
- Unknown-kernel stationary catalog:
  [EmpiricalStationaryCatalog.lean](./FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean)
- Statement and axiom checker:
  [CheckEmpiricalStationaryCatalog.lean](./examples/CheckEmpiricalStationaryCatalog.lean)
- Informative catalog receipt:
  [CheckEmpiricalStationaryCatalogInformative.lean](./examples/CheckEmpiricalStationaryCatalogInformative.lean)

Unvisited rows are not normalized. The chosen finite invariant PMF is a
noncomputable witness, not an executable stationary solver. Invariant-law
uniqueness requires a strict Dobrushin or candidate-TV contraction certificate.

## The theorem chain

![FormalSLT flagship theorem chain](./docs/theorem-chain.svg)

This is a logical theorem-family map, not a literal import graph. Solid nodes
name checked surfaces. Conditional and open nodes state real boundaries rather
than planned marketing claims.

## Read FormalSLT from your field

| Reader | Route |
|---|---|
| Statistics and ML | [Bounds, assumptions, receipts, and matched benchmarks](https://robby955.github.io/FormalSLT/readers/stats-ml/) |
| Probability | [e-processes, path laws, Poisson equations, and contraction](https://robby955.github.io/FormalSLT/readers/probability/) |
| Lean | [Topic imports, theorem names, and source organization](https://robby955.github.io/FormalSLT/readers/lean/) |
| Verification | [Axiom receipts, statement-fidelity gates, and release checks](https://robby955.github.io/FormalSLT/readers/verification/) |

For exhaustive detail, use:

- [Intuition](./docs/intuition.md)
- [Theorem map](./docs/theorem-map.md)
- [Assumptions and nonclaims](./docs/assumptions-and-nonclaims.md)
- [Literature and theorem-fidelity ledger](./docs/LITERATURE.md)
- [Mathematical sources](./docs/references.md)
- [Related formalizations](./docs/related-work.md)
- [Proof frontier](./docs/proof-frontier.md)

## Scope boundaries

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

## Module map

Use one topic import rather than the whole root umbrella:

    import FormalSLT.PACBayes
    import FormalSLT.Sequential
    import FormalSLT.StochasticDynamics
    import FormalSLT.VC

Each topic has an isolated smoke checker under
[examples/stable_imports](./examples/stable_imports). The root
<code>import FormalSLT</code> remains useful for exploration but is not the
recommended dependency boundary.

Supporting families include:

- <code>FormalSLT.Probability</code>, <code>Concentration</code>, and
  <code>AnytimeValid</code>
- <code>FormalSLT.Rademacher</code>, <code>VC</code>, and
  <code>Covering</code>
- <code>FormalSLT.PACBayes</code>
- <code>FormalSLT.StochasticDynamics</code>
- <code>FormalSLT.Stability</code>, <code>OnlineToPAC</code>, and
  <code>Statistics</code>

The checked [20-state random-refresh load application](./docs/random-refresh-load-application.md)
and the staged [24-state controlled-queue application](./docs/controlled-queue-application-design.md)
are available through the opt-in <code>import FormalSLT.Applications</code>
umbrella. The queue layer includes typed generated kernels and policies,
bounded fixed scores, overlap and ratio certificates, a universal centered
row-risk envelope `D = 1`, candidate target-kernel contraction, canonical
finite-state invariant witnesses, and a fixed-nominal-candidate twelve-atom
OPE event. A separate structured-confidence module embeds the three candidates
in the arbitrary-parameter refresh family `gamma in [0,1)` and gives one
time-uniform scalar event whose hit-probability discrepancy equals every
physical-row TV discrepancy. For the nominal environment, queue-threshold
target-policy index `1`,
and nominal-model fixed-predictor index `2`, a separate checked module gives an
explicit 24-state invariant PMF, proves equality to the canonical catalog
witness, and evaluates stationary Brier risk exactly as
`4338268437 / 67816493056 < 13 / 200`. The aligned known-kernel receipt fixes
depth `12`, tilt `1/16`, and the realized initial observation `(1, 1)`; its
independently reconstructed suffix histogram yields a selected endpoint below
`7/100` in Lean. The theorem does not prove named-path good-event membership or
unconditional coverage for the simulator's random first observation. The
empirical-kernel event uses a fresh full-support transition-coordinate prior,
requires every augmented row to be visited, and is numerically vacuous on the
current trace. The structured scalar event avoids that 4,608-coordinate
allocation. Its OPE composition now preallocates all `3 x 7` candidate--depth
atoms and permits pathwise candidate, depth, risk-tilt, persistence-tilt,
posterior, and time selection inside a single `19/20` outer-mass event.
The prospective protocol, independent trace/receipt tooling, and generic Lean
histogram reduction are frozen. The registration handoff uses a version-one
binding that omits OSF's not-yet-created final GUID; the completed registration
response supplies that GUID, the archived-file metadata target must match it,
and the metadata size and SHA-256 must match the exact binding bytes. The pre-beacon
`make verify-controlled-queue-structured-ope-code-freeze` gate checks them
without fetching a beacon or creating a prospective artifact. No fresh
prospective trace, receipt, or numerical result exists. After immutable public
registration and one authorized generation, the ordered
`make verify-controlled-queue-structured-ope-prospective-receipt` gate is
required; the result and matched comparisons must be reported regardless of
outcome.
Application-specific declarations are not part of the 19-name v0.2
compatibility promise.

## Installation

FormalSLT uses Lean 4.32.2 and Mathlib 4.32.2.

For the released v0.1 API:

    require FormalSLT from git
      "https://github.com/Robby955/FormalSLT.git" @ "v0.1.0"

For the historical controlled-queue code-freeze checkpoint (before the OSF
final-GUID cross-binding correction):

    require FormalSLT from git
      "https://github.com/Robby955/FormalSLT.git" @
        "5eae99f5f217edc7b44bd81dda6fde2a946effda"

Then import one of the topic umbrellas above. The exact v0.2 tag will replace
the snapshot instruction only after protected-tag gates, downstream builds,
matched identity receipts, the GitHub Release, and DOI publication are
complete.

### Supported topic imports

The candidate v0.2 public boundaries are:

- `FormalSLT.PACBayes`
- `FormalSLT.Sequential`
- `FormalSLT.StochasticDynamics`
- `FormalSLT.VC`

The 19 endorsed declarations and compatibility rules are documented in
[Public API stability](./docs/api-stability.md). The rest of the transitive
namespace remains available but is not covered by the v0.2 compatibility
promise.

Until the `v0.2.0` release exists, pin an exact tested commit instead of moving
`main`. For example, the historical controlled-queue code-freeze checkpoint can
be consumed from another Lake package with:

```lean
require «formal-slt» from git
  "https://github.com/Robby955/FormalSLT.git" @
  "5eae99f5f217edc7b44bd81dda6fde2a946effda"
```

That checkpoint is suitable for theorem/application inspection, not for the
irreversible OSF registration. Registration requires the later reviewed
code-freeze checkpoint containing the final-GUID cross-binding correction.

The compatibility commitment starts at the `v0.2.0` tag. The repository also
contains a separate path-dependent consumer under `tests/downstream/`; it
builds one concrete module through each public topic import.

## Audit commands

The short local verification loop is:

```bash
lake exe cache get
lake build FormalSLT
make examples
make tutorials
make api
make downstream
python3 -m pip install -r requirements-dev.txt
make verify-controlled-queue-structured-ope-code-freeze
make python-tests
make check-controlled-queue-model
make check-controlled-queue-trace
make check-controlled-queue-known-kernel-receipt
bash scripts/check_axioms.sh
bash scripts/check_witness_quality.sh
FIDELITY_BASE_REF=origin/main bash scripts/check_statement_fidelity.sh
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/generate_theorem_index.py --check
python3 scripts/generate_badge_counts.py --check
python3 scripts/check_doc_anchors.py --self-test
git ls-files -z -- '*.md' '*.mdx' | \
  xargs -0 python3 scripts/check_doc_anchors.py
git diff --check
```

The public axiom gate reports only

- `[propext, Classical.choice, Quot.sound]` for the curated public theorem
  surface;
- the root build, recursive example sweep, tutorials, public API snapshot,
  v0.1 replay, downstream consumer, and repository-tool self-tests finish
  successfully;
- the controlled-queue code-freeze gate checks the frozen protocol,
  generator/verifier lanes, and both generated-Lean branches without creating
  a prospective artifact;
- changed theorem statements pass the fail-closed fidelity scan against the
  selected base revision;
- the proof-debt scans find no executable `sorry`, `admit`, or custom axiom;
- generated proof-frontier, badge, and documentation anchors are current; and
- `git diff --check` reports no whitespace errors.

There are no <code>sorry</code>, <code>admit</code>, or custom-axiom
declarations in the checked library and examples. The
[public release checklist](./docs/public-release-checklist.md) records the
larger exact-SHA gate used before a release.

## Provenance

FormalSLT cites both the original mathematics and the checked implementation.
The [source map](./docs/references.md) records the mathematical routes; the
[literature ledger](./docs/LITERATURE.md) records agreement, differences, and
review requirements. The Lean theorem signatures and their checker files remain
the authority for what is proved.

An earlier verifier-gated formalization route built on FormalSLT was accepted
at the ICML 2026 AI for Math workshop:
[*From Agents to Axioms: Verifier-Gated Lean Formalization for Statistical
Learning Theory*](https://openreview.net/pdf?id=EsEqPLc0ef).

The companion library
[formal-martingales](https://github.com/Robby955/formal-martingales) develops
martingale and anytime-valid probability infrastructure.

## Contributing

Read [CONTRIBUTING.md](./CONTRIBUTING.md) and
[Good first issues](./docs/good-first-issues.md). New public theorems require a
focused checker, <code>#print axioms</code> receipt, explicit scope, and the
repository verification gates.

## Citation

Use [CITATION.cff](./CITATION.cff) for the current software citation. If the
tagged v0.2 file is to contain its DOI, that DOI will first be reserved in an
unpublished archival deposit and added to the final reviewed source commit.
The DOI is citable only after the deposit and GitHub Release are published and
the DOI resolves to the exact tagged artifact.

## License

MIT. See [LICENSE](./LICENSE).
