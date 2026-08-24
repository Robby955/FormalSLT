# Changelog

## Unreleased

No entries yet.

## v0.2.0 - 2026-08-24

### Learning theory

- Expanded finite-sample Rademacher, VC, stability, metric-entropy, and
  chaining results, with executable examples and explicit assumptions.
- Added a four-topic stable import surface and a checked 19-declaration
  compatibility allowlist.
- Retained the published v0.1 examples and deprecated compatibility wrappers
  for the two renamed Bousquet--Elisseeff declarations.

### PAC-Bayes and anytime-valid inference

- Added all-sample-size empirical-Bernstein PAC-Bayes bounds for IID data.
- Added forward predictable-mean and variance-proxy interfaces for sequential
  use.
- Added e-process, mixture, stitched-boundary, and adaptive-selection
  components, including a polynomial stitched iterated-logarithm bound.
- Added rational witness checks that exercise the numerical boundary formulas.

### Adaptive and dependent data

- Added PAC-Bayes guarantees for adaptive trajectories with finite hypothesis
  catalogs and with arbitrary measurable state and hypothesis spaces.
- Added finite-state stationary-risk bounds using Poisson corrections,
  Dobrushin contraction, and empirical transition confidence.
- Added predeclared candidate-kernel and depth selection, target-policy
  evaluation, and finite controlled-process adapters.
- Added checked random-refresh and controlled-queue applications. The
  controlled-queue receipt is retrospective and conditional on its specified
  refresh-family model.

### Documentation and verification

- Added theorem-oriented documentation, declaration search, a concept index,
  literature and assumption ledgers, focused checker files, and an overview
  film.
- Added Linux and macOS downstream consumers for the supported imports.
- Added fail-closed checks for public signatures, axiom sets, statement
  fidelity, witness quality, module reachability, and generated artifacts.
- Added exact-tag identity receipts and deterministic source/documentation
  release assets.

See the [v0.2.0 release notes](docs/releases/v0.2.0.md) for installation,
verification, and scope boundaries.

## v0.1.0 - 2026-05-08

- First public FormalSLT source tag. No GitHub Release or DOI was issued for
  this version.
- Finite-sample statistical-learning foundations spanning Rademacher
  complexity, VC theory, concentration, PAC-Bayes, stability, and initial
  sequential-inference interfaces.

[Unreleased]: https://github.com/Robby955/FormalSLT/compare/v0.2.0...HEAD
[v0.2.0]: https://github.com/Robby955/FormalSLT/compare/v0.1.0...v0.2.0
[v0.1.0]: https://github.com/Robby955/FormalSLT/tree/v0.1.0
