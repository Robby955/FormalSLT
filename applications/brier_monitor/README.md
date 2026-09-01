# Brier monitor certificates

This directory separates three jobs that should not be conflated:

1. raw-data replay computes exact losses and a conservative observable-variation
   bound, then binds them to source hashes;
2. Lean checks the statistical theorem specialization and endpoint arithmetic
   from those summaries;
3. the monitor renders the result without becoming a source of truth.

The public GJP viewer is under `docs/site/monitor/`. Its compact
`formalslt.certificate.v1` receipt is constant-size in the data: it records
hashes, exact summaries, theorem sources, checker output, and claim scope. The
172-point display trace is a separate hash-bound file. A normal verification
runs in seconds and does not regenerate the 31,000-line path ledger.

The user-facing command is profile-gated. It refuses unknown analyses before
writing output. The fixed GJP replay and general chronological tabular profile
have separate theorem and receipt bindings.

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

For a new prediction stream, `certify` accepts CSV with no extra dependency or
Parquet after installing `requirements-cli.txt`. Predictions are scaled
integers, so the analyzed quantity is exact. The protocol must declare that
each prediction was available before its corresponding outcome and must label
its provenance `DECLARED`, `AUDITED`, or `SIGNED_LOG`.

Replay the same protocol incrementally to produce an uncertified live trace:

```bash
./bin/formalslt monitor protocol.yaml predictions.parquet \
  --every 100 \
  --out monitor-trace.json
```

The incremental engine maintains exact per-model Brier loss, predictable
quadratic-variation ceilings, a post-data selected point posterior, and the
conservative boundary preview. Its trace deliberately says
`PREVIEW_NOT_CERTIFIED`; use `certify` to rerun the data independently and
invoke Lean on the final endpoint.

```bash
./bin/formalslt certify protocol.yaml predictions.parquet \
  --out certificate
./bin/formalslt verify certificate/certificate.json \
  --protocol protocol.yaml \
  --data predictions.parquet
./bin/formalslt show certificate/certificate.json
```

Issuance streams the table twice through independent implementations. Each
replay rounds every nonnegative row contribution to the same `2^-40` grid, so
the accumulated quadratic-variation input is a compact conservative upper
bound rather than a fraction whose denominator grows with the row count. The
maximum rounding slack is recorded in the receipt. The generated Lean checker
therefore grows with the model catalog, not the row count. Independent data
replay and Lean verification remain separate receipt lines. The checked
endpoint uses one predeclared half tilt and permits the reporting posterior over
models to be chosen after observing the prefix.

The lower-level preparation commands remain available for debugging:

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
entire canonical preparation. Passing this replay alone does not turn the
preparation into a certificate; `certify` adds the theorem-backed Lean check.

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

## Frozen UCI-357 data protocol

`uci357-protocol-v1.json` defines the first real-data input contract. It pins
the UCI Occupancy Detection landing page, DOI, CC BY 4.0 metadata, archive and
member hashes, strict parser, chronological 40/20/40 split, feature leakage
guards, 16-bit probability quantization, exact Brier arithmetic, and the
deterministic soft-winner posterior rule.

The source archive and derived stream are deliberately untracked. Prepare and
check them with:

```bash
python3 scripts/prepare_brier_monitor_uci357.py --download
python3 scripts/prepare_brier_monitor_uci357.py --check
python3 -m pytest -q tests/test_brier_monitor_uci357_protocol.py
```

The tracked `generated/uci357-protocol-v1-manifest.json` binds the observed
source and canonical stream hashes. These default preparation and check paths
use only the Python standard library. To explicitly compute the optional local
baselines when NumPy and scikit-learn are already installed, run:

```bash
python3 scripts/prepare_brier_monitor_uci357.py --baselines
python3 scripts/prepare_brier_monitor_uci357.py --check --baselines
```

The ignored local result contains only a training-prevalence constant and one
deterministic all-sensor logistic baseline. A scikit-learn convergence warning
fails the run. The result is descriptive and non-public; it is not a FormalSLT
certificate.

## Audited UCI-357 certificate application

The certificate application trains the logistic model only on the frozen
training prefix and emits predictions for the 8,224-row monitor suffix. It then
selects the lower-Brier model after observing that suffix. The selected point
posterior is charged against a uniform two-model prior; the receipt does not
pretend that the logistic model was selected in advance.

Install the pinned model runtime, prepare the hash-bound prediction stream, and
issue or verify the compact certificate with:

```bash
python3 -m pip install -r requirements-uci357.txt
python3 scripts/build_brier_monitor_uci357_certificate.py --prepare
python3 scripts/build_brier_monitor_uci357_certificate.py --issue
python3 scripts/build_brier_monitor_uci357_certificate.py --check
```

The tracked evidence labels this as an audited retrospective demonstration.
The model never receives `Occupancy` as an input, but the source archive does
not establish real-time label delay. The statistical claim remains encountered
conditional prefix risk, not future occupancy or deployment risk.

The tracked 8,224-observation result selects the all-sensor logistic model after
the monitored prefix, records observed Brier loss `0.0611976886…`, and checks a
95% upper bound of `0.073268`; the constant training-prevalence baseline has
loss `0.165321928…`. Reissue the same application through the public command:

```bash
./bin/formalslt certify \
  applications/brier_monitor/uci357-certificate-protocol-v1.json \
  applications/brier_monitor/generated/uci357-monitor-predictions-v1.csv \
  --out /tmp/formalslt-uci357-certificate
```

The interactive, digest-bound presentation is staged from
`docs/site/monitor/occupancy/`. Intermediate chart points are display replays;
the final `0.073268` endpoint is the point checked by the tracked Lean file.
