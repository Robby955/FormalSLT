# Synthetic Brier monitor proof of life

This directory exercises the finite sleeping suffix-variance API on the
soft-Brier branch already formalized in
`CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.lean`.
It is a small replayable arithmetic artifact, not the planned real-data
monitor.

The input records forecasts and binary outcomes. It contains no loss column.
The generator recomputes each Brier loss, posterior empirical suffix risk,
forward-predictor quadratic variation, wake allocation, and every supported
geometric-tilt witness. Logarithms and the empirical-Bernstein `psi` term are
enclosed by exact rational atanh-series bounds. The independent verifier has a
separate implementation of the same calculation and checks every tracked
digest.

For the frozen 512-observation synthetic stream, replay selects wake `0` and
tilt atom `0` (`lambda = 1/2`). The posterior empirical Brier risk is exactly
`1/16`, the observable quadratic variation is `49/256`, and the conservative
witness endpoint is at most `0.090592128650167`. The rational interval also
separates this witness from every other declared wake/tilt candidate.

Run the focused checks with:

```bash
python3 scripts/generate_brier_monitor_synthetic_receipt.py --check
python3 scripts/verify_brier_monitor_synthetic_receipt.py --check
python3 -m pytest -q tests/test_brier_monitor_synthetic_receipt.py
```

Regenerate tracked outputs with:

```bash
python3 scripts/generate_brier_monitor_synthetic_receipt.py
```

Tracked outputs:

- `generated/synthetic-proof-of-life-v1-receipt.json`: recomputed statistics,
  rational enclosures, candidate table, and selected witness;
- `generated/synthetic-proof-of-life-v1-manifest.json`: byte and SHA-256
  bindings for the input, scripts, Lean source, receipt, and generated data;
- `FormalSLT/Applications/BrierMonitorSyntheticProofOfLifeData.lean`: generated
  rational data only.

The generated Lean data module contains only rational constants. The separate
receipt module and checker prove the exact arithmetic and the conditional
composition with the statistical theorem. They do not establish that the
realized path belongs to a theorem-produced good event; the theorem supplies a
coverage probability, not an observable event-membership test. This artifact
also does not turn monitored conditional suffix risk into future, stationary,
population, or deployment risk. The real-data monitor still requires a frozen
dataset, chronological prediction protocol, and a Lean theorem/checker that
consumes the generated data.
