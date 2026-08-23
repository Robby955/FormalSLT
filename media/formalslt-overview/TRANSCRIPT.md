# FormalSLT overview transcript

The film uses an original instrumental score. Its explanation is also written
on screen; this transcript provides an accessible, searchable version.

## 00:00.000 — FormalSLT

FormalSLT checks learning guarantees that survive adaptation. The film covers
PAC-Bayes bounds, anytime inference, dependent paths, and stationary risk.

## 00:04.500 — When the data are not IID

The next observation can depend on everything seen so far. Data-selected
models, dependent data, and repeated looks must be handled by the theorem.

## 00:09.600 — One family, one checked reduction

Inside the predeclared controlled-queue refresh family, a generic transition
route tracks 48 current observations × 48 next observations × 2 orientations:
4,608 coordinates. Each physical row is a uniform refresh plus extra mass on
one known deterministic step.

The binary hit records whether the next state takes that step. Its conditional
mean is `p_gamma = E[hit | past] = (1 + 23 * gamma) / 24`. Lean proves the exact
transfer identity
`TV(row gamma, row gamma') = |p_gamma - p_gamma'|` for every physical row.
This result assumes the predeclared refresh family; it does not test whether
the data belong to that family.

## 00:20.300 — Four mechanisms checked in Lean

The film follows exponential processes, change of measure with PAC-Bayes,
time-uniform validity, and guarantees along dependent paths. This is a route
through the mechanisms, not a claim that every displayed declaration forms one
literal dependency chain. Each result is tied to the pinned Lean source.

## 00:27.550 — One guarantee, valid at every time

The same checked event covers every time and every allowed posterior.

## 00:34.040 — Choices along an observed path

The posterior and time-indexed tilt may use the observed prefix. The next-step
score is fixed before the next state arrives.

## 00:39.790 — From one path to long-run risk

For finite-state kernels, a Poisson correction connects pathwise evidence to a
stationary target. FormalSLT keeps known-kernel and predeclared-kernel-catalog
routes separate.

## 00:45.690 — One library, four mathematical layers

The map shows PAC-Bayes, sequential inference, stochastic dynamics, and VC
theory. The library exposes reusable statements with explicit assumptions and
exact source.

## 00:51.140 — First exact Lean declaration

The exponential-process receipt is
`exists_forwardEmpiricalBernsteinLowerTiltCatalog_event` from
`ForwardBesselProcess.lean`.

## 00:54.890 — Second exact Lean declaration

The structured-transfer receipt is
`refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy` from
`ControlledQueuePersistenceConfidence.lean`.

## 00:57.790 — Axiom and revision card

The displayed declarations use no project-specific axioms. The card records
the audited primitives `propext`, `Classical.choice`, and `Quot.sound`, together
with the exact fact-bound Git revision.

## 01:00.890 — FormalSLT

Checked learning theory for data that adapt.
