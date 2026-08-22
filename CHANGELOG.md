# Changelog

This file records user-visible changes to FormalSLT. Each version entry states
which publication artifacts actually exist; a source tag alone is not treated
as evidence of a GitHub Release or DOI.

## Unreleased

The changes below are candidates for FormalSLT v0.2.0. They are not a published
v0.2 release, and no DOI is attached to them yet.

### Added

- All-sample-size empirical-Bernstein PAC-Bayes endpoints, forward e-process
  infrastructure, and confidence-allocated vanishing selectors.
- Adaptive trajectory inference for finite and general measurable state and
  hypothesis spaces.
- Finite-state stationary Poisson, contraction, empirical-transition,
  unknown-kernel, controlled-dynamics, and target-policy certification layers.
- A checked 20-state random-refresh load application with matched baselines,
  adaptive selection, and explicit known- and unknown-kernel certificates.
- An opt-in 24-state controlled-queue application with exact model and trace
  data, a checked invariant-risk atom, structured OPE events, and an aligned
  known-kernel receipt.
- A frozen prospective controlled-queue protocol, independent trace and receipt
  tooling, and a generic Lean histogram-to-bound reduction. These contain no
  fresh prospective artifact or result.
- A countable transition-confidence extension with geometric allocation and
  conditional vanishing row and candidate-kernel budgets.

### Public API candidate

- Four supported topic imports: `FormalSLT.PACBayes`,
  `FormalSLT.Sequential`, `FormalSLT.StochasticDynamics`, and `FormalSLT.VC`.
- A 19-declaration candidate compatibility allowlist with isolated import,
  signature, and axiom checks.
- Exact replay of the examples published with v0.1.0 and retained compatibility
  wrappers for the two renamed Bousquet--Elisseeff declarations.
- A separate downstream Lake consumer, configured for Linux and macOS CI.

### Documentation and verification

- A theorem-oriented landing page, concept index, reader routes, theorem map,
  literature ledger, and explicit proof-status and literature-fidelity labels.
- Fail-closed statement-fidelity, witness-quality, transitive-axiom,
  module-reachability, API-snapshot, and tagged-install gates.
- A hosted controlled-queue code-freeze gate that checks the prospective
  protocol, generator/verifier lanes, and generated-Lean branches without
  producing prospective evidence.
- Resolver-bound exact-tag receipts recording the tag object, peeled commit,
  tree, Lean toolchain, pinned Mathlib revision, operating system, timestamp,
  and hosted run URL. Automatic runs bind the initial resolution to the tag
  push event commit; a final gate requires matching Linux/macOS receipts and
  rechecks the remote without asserting a Release or DOI.
- GitHub workflows fetch the Elan installer from exact upstream commit
  `464c9d28395000a2a0128e07081e4956d50eced2` rather than a moving branch.
- Candidate release notes and a publication checklist in
  [`docs/releases/v0.2.0.md`](docs/releases/v0.2.0.md).

### Known boundaries

- The all-sample-size IID empirical-Bernstein endpoint is offline and does not
  license optional stopping.
- The named deterministic application path is not proved to lie in the
  theorem-produced probability event; the corresponding application statement
  remains conditional.
- Vanishing normalized unknown-kernel budgets require positive limiting row
  frequencies, and candidate-kernel vanishing also requires empirical
  discrepancy convergence.
- Application declarations are opt-in and are outside the 19-name public API
  candidate.
- No fresh prospective controlled-queue trace, receipt, or numerical outcome is
  included. After immutable registration and the single authorized generation,
  the ordered post-beacon verification gate is required and the result must be
  reported regardless of outcome.

## v0.1.0 - 2026-05-08

- First public FormalSLT source tag. No GitHub Release or DOI was issued for
  this version.
- Finite-sample statistical-learning foundations spanning Rademacher
  complexity, VC theory, concentration, PAC-Bayes, stability, and initial
  sequential-inference interfaces.

[Unreleased]: https://github.com/Robby955/FormalSLT/compare/v0.1.0...HEAD
[v0.1.0]: https://github.com/Robby955/FormalSLT/tree/v0.1.0
