# Brier monitor certificates

This directory separates three jobs that should not be conflated:

1. raw-data replay computes exact summaries and binds them to source hashes;
2. Lean checks the statistical theorem specialization and endpoint arithmetic
   from those summaries;
3. the monitor renders the result without becoming a source of truth.

The public GJP viewer is under `docs/site/monitor/`. Its compact
`formalslt.certificate.v1` receipt is constant-size in the data: it records
hashes, exact summaries, theorem sources, checker output, and claim scope. The
172-point display trace is a separate hash-bound file. A normal verification
runs in seconds and does not regenerate the 31,000-line path ledger.

The user-facing command is profile-gated. It refuses unknown analyses before
writing output; a new CSV or Parquet adapter cannot reuse the GJP verification
badge without registering a theorem-backed profile.

```bash
./bin/formalslt profiles
./bin/formalslt certify \
  applications/brier_monitor/gjp-compact-certificate-protocol-v1.json \
  /tmp/formalslt-gjp-replay-v1 \
  --out /tmp/formalslt-certificate
./bin/formalslt verify \
  /tmp/formalslt-certificate/gjp-certificate-v1.json \
  --data /tmp/formalslt-gjp-replay-v1
```

For a new prediction stream, `prepare` accepts CSV with no extra dependency or
Parquet after installing `requirements-cli.txt`. Predictions are scaled
integers, so the exact quantity being analyzed is unambiguous. The output
contains exact empirical Brier risk, observable quadratic variation, KL and
logarithm enclosures, data and protocol hashes, and a candidate bound. It is
marked `PREPARED_NOT_CERTIFIED`; `certify` will continue to refuse it until a
registered Lean profile and independent replay checker cover that protocol.

```bash
./bin/formalslt prepare protocol.yaml predictions.parquet \
  --out preparation.json
./bin/formalslt verify-preparation \
  preparation.json protocol.yaml predictions.parquet
```

`verify-preparation` uses a separate implementation. It does not import the
preparation engine; it reparses the protocol and table, streams the rows again,
recomputes the normalized-data digest, empirical loss, observable variation,
KL term, logarithm enclosures, and candidate expression, then compares the
entire canonical preparation. Passing this replay still does not turn the
preparation into a certificate. The next registered profile supplies that
Lean boundary.

The worked real-data result is deliberately disclosed as it happened. The
certificate verification passes; the preregistered GJP study verdict is
`FAIL`. The newer `< 0.131` countable-strategy endpoint is retrospective and
is not substituted for the preregistered endpoint.

Issue from a clean, independently replayed artifact directory:

```bash
python3 scripts/formalslt_certificate.py issue \
  --artifacts /tmp/formalslt-gjp-replay-v1 \
  --run-lean
```

Run the compact verifier directly:

```bash
python3 scripts/formalslt_certificate.py verify
```

## Synthetic proof of life

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
