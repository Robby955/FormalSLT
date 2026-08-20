# Controlled queue preprocessing

Status: **MODEL AND TRACE/PREPROCESSING ONLY**

This directory freezes and compiles the deterministic model inputs for the
24-state, two-action controlled-queue benchmark. The trace slice is a frozen,
deterministically replayable data artifact. It is not a statistical
certificate, a theorem-produced good path, Lean-verified trace data, or a proof
of unknown-kernel target-policy OPE.

## Files

- `model-v1.json`: exact input schema and benchmark parameters. Rational values
  are canonical strings such as `3/4`; JSON floats are forbidden.
- `generated/model-v1-tables.json`: full exact rational candidate-kernel,
  policy, fixed-predictor, control-cost, outcome, and Brier-loss tables.
- `generated/model-v1-manifest.json`: schema/model/generator identifiers,
  frozen future parameters, and SHA-256 bindings for the input and outputs.
- `../../FormalSLT/Applications/ControlledQueueData.lean`: generated Lean
  definitions and tables. It intentionally contains no theorem or certificate.
- `trace-v1.json`: exact initial state, horizon, source candidate, behavior
  policy, weight tables, binary layout, SHA-256 counter-stream contract, and
  unbiased rejection-sampling contract.
- `generated/trace-v1.bin`: 200,000 transitions as explicit state and action
  arrays plus the exact pre-outcome numerator/denominator stream for both
  causal Beta predictors.
- `generated/trace-v1-counts.json`: exact state, action, state-action, edge, and
  outcome counts together with final causal sufficient statistics and PRNG
  consumption counts.
- `generated/trace-v1-manifest.json`: SHA-256 bindings for both inputs, both
  generators, the independent verifier, and both generated outputs.

Both generators and the independent trace verifier under `../../scripts/` use
only the Python standard library.

## Regenerate and verify

```bash
make generate-controlled-queue-model
make generate-controlled-queue-trace
~/.elan/bin/lake exe cache get
make verify-controlled-queue-model
make verify-controlled-queue-trace
```

The model verification target fails if any generated model byte or manifest
hash is stale, runs the narrow arithmetic/schema tests, and compiles only the
generated Lean data module. The trace target separately regenerates the full
byte stream, then an implementation-independent verifier replays every random
draw, transition, count, and causal update. It also runs tamper, rejection,
no-look-ahead, and stale-artifact tests.

The binary stores `state_t` and `action_t` separately. FormalSLT's
`ControlledObservation Z A` is represented as `A × Z`, while the generated
model's 48 rows use state-major indices `2 * state + action`. A future theorem
bridge must prove the required swap and index equivalence; these preprocessing
files do not identify the tuples definitionally. Likewise, the causal Beta
predictors currently support dynamic behavior-encountered comparison only.
They are not fixed stationary target-policy scores unless learner memory is
added to the state and a corresponding theorem is proved.

The stored path is `S_0, A_0, S_1, ..., A_{H-1}, S_H`. The current
deterministic-initial `controlledTrajectoryMeasure` instead fixes an initial
controlled observation `(A_0, S_1)`. Because this generator samples that first
pair, a future theorem instantiation must either condition on and use the
suffix beginning at the realized `(A_0, S_1)`, with its explicit horizon
offset, or prove a random-initial controlled-law bridge. The full trace is
preserved here, but direct horizon/index alignment is not claimed.
