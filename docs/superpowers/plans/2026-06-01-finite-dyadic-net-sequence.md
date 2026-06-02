# Finite Dyadic-Net Sequence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize the rounded dyadic-net Dudley wrapper away from `[0,1]`.

**Architecture:** Add a reusable `FiniteDyadicNetSequence` bundle around the existing projected finite-net Dudley theorem. Instantiate that bundle for the unit-interval rounded grid and route the arbitrary-`m` projected and supplied-supremum corollaries through the generic API.

**Tech Stack:** Lean 4, mathlib, FormalSLT finite sub-Gaussian chaining.

---

### Task 1: Generic Bundle

**Files:**
- Modify: `FormalSLT/Covering/FiniteSubGaussianChaining.lean`

- [ ] Add a structure bundling the net sequence, cover counts, radius scale, distance geometry, geometric radius decay, projection-pair nontriviality, and cover-count domination.
- [ ] Add a projected finite-net Dudley theorem that accepts the bundle and calls the existing covering-number theorem.
- [ ] Add a supplied-supremum finite-budget theorem that accepts a terminal approximation hypothesis and adds `terminalError`.

### Task 2: UnitInterval Instantiation

**Files:**
- Modify: `FormalSLT/Covering/UnitIntervalDudley.lean`

- [ ] Define `unitIntervalRoundedDyadicGridNetSequence`.
- [ ] Refactor `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound` through the generic projected theorem.
- [ ] Refactor `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound` through the generic supplied-supremum theorem.

### Task 3: Checker and Verification

**Files:**
- Modify: `examples/CheckUnitIntervalDudley.lean`

- [ ] Add `#check` and `#print axioms` lines for the generic bundle, generic theorems, and unit-interval instantiation.
- [ ] Run `lake build FormalSLT.Covering.UnitIntervalDudley`.
- [ ] Run `lake env lean examples/CheckUnitIntervalDudley.lean`.
- [ ] Run `python3 scripts/generate_proof_frontier_manifest.py --check`, `git diff --check`, and the public-writing audit on touched markdown.
