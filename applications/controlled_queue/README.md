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
- `../../FormalSLT/Applications/ControlledQueueReindex.lean`: checked row-order,
  tuple-swap, and controlled-edge selection bridge.
- `../../FormalSLT/Applications/ControlledQueueTypedModel.lean`: checked
  table-backed kernel and policy PMFs with exact mass identities and the static
  uniform-behavior probability and TV transfers.
- `../../FormalSLT/Applications/ControlledQueueTargetPolicyScores.lean`:
  checked fixed Brier and control-cost scores, unit-range bounds, target-policy
  overlap, and the exact `3/2` ratio cap. The two causal Beta predictors remain
  outside this stationary-score interface.
- `../../FormalSLT/Applications/ControlledQueueContraction.lean`: checked
  candidate cell minorization, uniform physical-state reference, Dobrushin
  upper bounds `5/8`, `3/4`, and `7/8`, and target-policy oscillation
  contraction. The coefficient is bounded above, not claimed exact.
- `../../FormalSLT/StochasticDynamics/StationaryTargetPolicyEmpiricalFiniteDepthOPE.lean`:
  generic same-path intersection of signed-residual target-policy OPE and
  augmented empirical-transition confidence for a fixed candidate, depth, and
  certificate package.
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
model's 48 rows use state-major indices `2 * state + action`.
`ControlledQueueReindex` proves the required swap, index equivalence, and
controlled-edge row selection. `ControlledQueueTypedModel` reads the generated
kernel and policy tables into typed PMFs with exact mass identities.
`ControlledQueueTargetPolicyScores` reconstructs the three fixed Brier scores
from the generated forecast and outcome tables and types the generated
control-cost score. `ControlledQueueContraction` lifts each generated
candidate's common cell floor through every state-Markov target policy. None of
these bridges imports the frozen trace, supplies a true invariant PMF, or
supplies an empirical confidence event.
The generic empirical finite-depth theorem separately intersects its risk and
transition events with failure cost `deltaRisk + deltaTransition`. Under exact
behavior mass `1/2` and positive visit mass for every augmented source row, it
uses the physical radius `2 * etaAug` and residual
`alpha ^ m * D + 4 * ((1 + B_m) * etaAug)`. It does not instantiate this
frozen trace, prove its all-row visits or good-event membership, or select the
candidate or depth from data.
Likewise, the causal Beta predictors currently support dynamic
behavior-encountered comparison only. They are not fixed stationary
target-policy scores unless learner memory is added to the state and a
corresponding theorem is proved.

The stored path is `S_0, A_0, S_1, ..., A_{H-1}, S_H`. The current
deterministic-initial `controlledTrajectoryMeasure` instead fixes an initial
controlled observation `(A_0, S_1)`. Because this generator samples that first
pair, a future theorem instantiation must either condition on and use the
suffix beginning at the realized `(A_0, S_1)`, with its explicit horizon
offset, or prove a random-initial controlled-law bridge. The full trace is
preserved here, but direct horizon/index alignment is not claimed.
