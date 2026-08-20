# Changelog

This file records user-visible changes to FormalSLT. A section is a release
only after its tag and GitHub Release exist.

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

## v0.1.0 - 2026-05-08

- First public FormalSLT release.
- Finite-sample statistical-learning foundations spanning Rademacher
  complexity, VC theory, concentration, PAC-Bayes, stability, and initial
  sequential-inference interfaces.

[Unreleased]: https://github.com/Robby955/FormalSLT/compare/v0.1.0...HEAD
[v0.1.0]: https://github.com/Robby955/FormalSLT/releases/tag/v0.1.0
