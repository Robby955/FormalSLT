# FormalSLT v0.2 external review packet

This packet requests two bounded technical reviews of the FormalSLT v0.2
theorem candidate: one probability/statistics review and one Lean/artifact
review. It does not ask either reviewer to audit the entire repository.

## Review target

| Field | Value |
|---|---|
| Git commit | `1aca197cbcf1c2f483c212db508d1d488b700b40` |
| Git tree | `6ab3c4dca662ae9bda5d714e4347a68f97266033` |
| Pull request | [#99](https://github.com/Robby955/FormalSLT/pull/99) |
| Lean toolchain | `leanprover/lean4:v4.32.2` |
| Mathlib revision | `905b95818eb32af7874a58b427f50c1711a5e96c` |
| Hosted CI | [CI run 32554352481](https://github.com/Robby955/FormalSLT/actions/runs/32554352481) |
| Hosted documentation check | [Docs run 32554352413](https://github.com/Robby955/FormalSLT/actions/runs/32554352413) |

The hosted run built the library and examples, checked the candidate public
API, ran the controlled-queue gates, audited public axioms, and built separate
downstream Lake packages on Ubuntu and macOS. Those checks are evidence about
this exact commit only; they are not a substitute for either requested review.

The controlled-queue application declarations are public, but they are not
part of the 19-declaration v0.2 compatibility promise in
[`docs/api-stability.md`](../../api-stability.md).

## Common claim boundary

The review should keep four kinds of evidence separate:

1. **Lean theorem statements.** These hold under the premises and quantifier
   order printed by Lean.
2. **Coverage semantics.** Outer-mass event bounds apply under the fixed laws,
   initial conditions, catalogs, and allocations in the theorem statements.
3. **Retrospective arithmetic.** The independent verifier reconstructs the
   stored trace's aligned suffix histogram and deterministic endpoint
   arithmetic. Lean proves the conditional risk conclusion for any path
   satisfying the histogram and event-inequality premises; it does not
   identify the raw trace bytes with a Lean path.
4. **Prospective design.** The sharp structured protocol freezes a future
   experiment and theorem interface. At the review target there is no public
   registration, fresh trace, histogram, receipt, generated Lean result, or
   numerical `< 1/10` conclusion.

The code-freeze reporting contract renders two prospective comparison
rows—the true-kernel oracle and the fixed-range row—as arithmetic-only
`PLANNED_NOT_CHECKED` baselines. Their displayed `1/20` values are planned
allocations, not checked outer-mass bounds.

## Probability and statistics review

The requested question is whether the mathematical model, estimands, event
semantics, selection timing, confidence accounting, and evidence labels agree.
A Lean tactic audit is not required for this lane.

### Flagship endpoints

| Result | Theorem statement | Literature and scope record |
|---|---|---|
| All-sample-size offline empirical-Bernstein PAC-Bayes | [`exists_continuousInfiniteEmpiricalBernstein_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.lean#L332) | [`docs/LITERATURE.md`](../../LITERATURE.md) |
| Adaptive trajectory inference | [`exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.lean#L356) | [`docs/assumptions-and-nonclaims.md`](../../assumptions-and-nonclaims.md) |
| Known-kernel stationary Poisson selection | [`exists_stationaryPoissonDepthSelection_allTime_vanishing_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.lean#L966) | [`docs/LITERATURE.md`](../../LITERATURE.md) |
| Unknown-kernel stationary catalog | [`exists_selectedCanonicalEmpiricalStationaryCatalog_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean#L682) | [`docs/related-work.md`](../../related-work.md) |

For the IID endpoint, check that the result is an offline all-sample-size event,
not an optional-stopping or selected-process theorem. For the trajectory
endpoint, a supplied path- and time-dependent posterior rule is evaluated
pointwise on a common event. The capstone quantifies that rule before the
existential event; the underlying event theorem is posterior-uniform. No
selector measurability or selected process is asserted. For stationary
Poisson selection, check the supplied invariant law, contraction and
finite-depth drift premises, and pointwise depth/tilt/posterior substitution.
For the empirical stationary catalog, check the all-row visit premise,
candidate catalog restriction, finite invariant target, and
strict-contraction branch. Its informative checker proves existential paths
outside the risk exceptional event while supplying selected row-TV errors
exactly. It never invokes the transition-confidence event, so it is not an
end-to-end same-path empirical-kernel receipt outside the combined
risk-plus-transition event; that combined receipt remains open.

### Controlled-queue load-bearing targets

| Role | Theorem | Review question |
|---|---|---|
| Contraction | [`candidateTargetPolicyKernel_dobrushin_le_gamma`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueContraction.lean#L120) | Does the common refresh component imply the stated Dobrushin upper bound for every target policy? No exact-coefficient claim is made. |
| Stationarity | [`queueThresholdStationaryLaw_isInvariant`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueInvariantRisk.lean#L929) and [`queueThresholdStationaryLaw_eq_catalogStationary`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueInvariantRisk.lean#L956) | Is the explicit 24-state rational law invariant, with uniqueness obtained from strict contraction? |
| Estimand | [`queueThreshold_nominalModelOverload_catalogStationaryRisk`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueInvariantRisk.lean#L1476) | Does the exact nominal stationary Brier risk equal `4338268437 / 67816493056`, and is it kept distinct from a confidence certificate? |
| Persistence event | [`exists_persistenceHitConfidence_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean#L352) | Is coverage pointwise in the fixed true persistence parameter, simultaneous only over the declared tilts and times, and based on a deterministic initial observation? |
| Structured transfer | [`refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean#L432) | Within the asserted refresh family, does every physical row-TV discrepancy equal the persistence-hit discrepancy? This is not a family-membership test. |
| Adaptive OPE | [`exists_controlledQueueStructuredAdaptiveOPE_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueStructuredOPE.lean#L476) | Does one `1/20` outer event support the predeclared candidate-depth, risk-tilt, persistence-tilt, posterior, and time choices? Verify the `1/40 + 1/40` union-bound accounting without an independence claim. |
| Frozen sharp event | [`exists_controlledQueueSharpStructuredReceipt_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueSharpStructuredOPE.lean#L465) | For `gamma = 149/200`, initial `(eco, state 0)`, and horizon `200000`, is this an event theorem rather than a numerical result? Its target law is the canonical finite invariant witness; this wrapper does not prove uniqueness for the off-grid true parameter. |
| Histogram reduction | [`sharpStructuredReceiptBoundary_evaluation_of_histogram`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueSharpStructuredReceiptCore.lean#L602) | Does an exact `24 x 2 x 24` physical histogram bound the frozen primary boundary without embedding future counts, a threshold result, or event membership? |
| Known-kernel event | [`exists_controlledQueueKnownKernelReceiptOPE_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean#L450) | Is the `39/40` statement confined to the nominal known environment and fixed initial observation? |
| Retrospective endpoint | [`knownKernelReceipt_selectedRisk_lt_seven_hundredths`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean#L799) | Are the aligned suffix-histogram premise and selected event inequality both explicit premises used by the `< 7/100` composition? |

The controlled-queue index convention deserves a separate check. The
retrospective receipt uses `199999` aligned suffix scores, while the prospective
protocol fixes the initial observation before sampling and uses `200000`
scores. The distinction is documented in
[`applications/controlled_queue/README.md`](../../../applications/controlled_queue/README.md).

### Probability review questions

- Do the controlled path law, target-policy stationary estimand, and importance
  score describe the same process?
- Do the event binders permit every claimed adaptive substitution, and only
  choices from catalogs fixed before the event?
- Are outer-mass bounds, deterministic arithmetic, and realized-path claims
  kept separate?
- Are the known-kernel, refresh-family unknown-dynamics, retrospective, and
  prospective cases labeled correctly?
- Are the horizon alignment, overlap ratio `3/2`, Brier range, contraction,
  and confidence allocation consistent?
- Does any prose overstate coverage, optional stopping, model-family
  robustness, policy optimization, or numerical evidence?

## Lean and artifact review

This lane reviews theorem types, dependency boundaries, generated-data trust,
axiom reports, and reproducibility. It does not ask the reviewer to validate
the informal mathematical interpretation without the probability lane.

### Lean review targets

- Inspect the load-bearing queue semantic bridge rather than treating the
  application capstones as black boxes:
  [`controlledObservedImportanceScore_condExp`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/StochasticDynamics/ControlledTrajectory.lean#L316),
  [`exists_stationaryTargetPolicyOPE_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/StochasticDynamics/StationaryTargetPolicyOPE.lean#L431),
  [`exists_stationaryApproximateTargetPolicyOPE_signedResidual_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/StochasticDynamics/StationaryTargetPolicyApproximateOPE.lean#L181),
  and
  [`exists_structuredControlledQueueFiniteCatalogOPE_event`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueStructuredOPE.lean#L133).
- The prefix dynamic target-policy comparator and finite-horizon target-path
  change-of-measure theorem are adjacent controlled-inference results, not
  dependencies of the queue capstone. Review them separately if the requested
  scope includes history-dependent targets or target-law occupancy.
- For the sharp queue transfer, inspect both the exact affine identity
  [`targetPolicyPoissonDrift_refresh_sub_candidate_eq`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueRefreshSensitivity.lean#L119)
  and its residual wrapper
  [`abs_approximateTargetPolicyPoissonResidual_le_refreshSensitivity`](https://github.com/Robby955/FormalSLT/blob/1aca197cbcf1c2f483c212db508d1d488b700b40/FormalSLT/Applications/ControlledQueueRefreshSensitivity.lean#L169).
- Compare the four supported imports and 19 declaration types against
  [`docs/api-stability.md`](../../api-stability.md), the isolated files under
  [`examples/stable_imports`](../../../examples/stable_imports), and the
  committed API signature snapshots.
- Run the concise checker for each theorem above. The controlled-queue checkers
  are `CheckControlledQueueContraction.lean`,
  `CheckControlledQueueInvariantRisk.lean`,
  `CheckControlledQueuePersistenceConfidence.lean`,
  `CheckControlledQueueStructuredOPE.lean`,
  `CheckControlledQueueSharpStructuredOPE.lean`,
  `CheckControlledQueueSharpStructuredReceiptCore.lean`, and
  `CheckControlledQueueKnownKernelReceipt.lean` under [`examples`](../../../examples).
- Confirm that every reviewed public theorem has a `#print axioms` report and
  that the reported closure is contained in `propext`, `Classical.choice`, and
  `Quot.sound`.
- Inspect deterministic regeneration and schema/arithmetic tests for the
  model, and the separate generator/verifier pairs for the historical trace,
  known-kernel receipt, and prospective trace/receipt paths. Manifests hash
  exact bytes and declared metadata; independent verifiers check byte/hash
  agreement outside Lean. Lean consumes generated rational declarations and
  proves endpoint arithmetic; it does not authenticate raw trace bytes or
  real-world provenance chronology.
- Confirm that `make verify-controlled-queue-structured-ope-code-freeze` is
  pre-beacon only. The post-beacon target is expected to fail until the public
  registration and one prospective execution exist.
- Review the statement-fidelity and witness gates as repository QA. They do
  not replace direct theorem-type review.

### Comparator boundary

This review target contains no Lean FRO Comparator receipt or trusted
`Challenge.lean`/untrusted `Solution.lean` split. The current build,
`#print axioms`, source scan, and fidelity gates are honest-development and
axiom-hygiene checks; they are not an adversarial boundary against malicious
metaprogramming or statement substitution.

A proper Comparator review would require separately approved challenge bytes,
a trusted import closure and project configuration, exact pins for Comparator,
`lean4export`, the sandbox, and the external kernel, and a fresh nonprivileged
checking environment that has never compiled the candidate. It would sandbox
the untrusted solution build, compare statement environments, enforce the
permitted axioms, and replay the exported proof with the Lean kernel and,
ideally, `nanoda`; sandbox security is itself part of the trust boundary. This
would add adversarial proof-artifact assurance. It would not assess model
fidelity, assumptions and constants, novelty, generated-data provenance,
nonvacuity, or named-path coverage. Comparator is therefore a possible
additional review artifact, not evidence already obtained.

## Reproduction

Run the following in a clean detached checkout of the review target. Keep this
packet open separately because it is documentation prepared after that target.

### Core replay

```bash
set -euo pipefail

test "$(git rev-parse HEAD)" = \
  1aca197cbcf1c2f483c212db508d1d488b700b40
test "$(git rev-parse HEAD^{tree})" = \
  6ab3c4dca662ae9bda5d714e4347a68f97266033

~/.elan/bin/lake exe cache get
~/.elan/bin/lake build FormalSLT
env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 MAKEFLAGS=-j1 make api
env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 MAKEFLAGS=-j1 make downstream

for f in \
  examples/CheckContinuousInfiniteEmpiricalBernsteinStitch.lean \
  examples/CheckForwardPredictableMeanBesselPACBayes.lean \
  examples/CheckTrajectoryEmpiricalBernsteinPACBayesCountable.lean \
  examples/CheckDynamicTargetPolicyComparator.lean \
  examples/CheckTargetPathChangeOfMeasure.lean \
  examples/CheckStationaryPoissonDepthSelection.lean \
  examples/CheckEmpiricalStationaryCatalog.lean \
  examples/CheckControlledQueueContraction.lean \
  examples/CheckControlledQueueInvariantRisk.lean \
  examples/CheckControlledQueuePersistenceConfidence.lean \
  examples/CheckControlledQueueStructuredOPE.lean \
  examples/CheckControlledQueueSharpStructuredOPE.lean \
  examples/CheckControlledQueueSharpStructuredReceiptCore.lean \
  examples/CheckControlledQueueKnownKernelReceipt.lean
do
  ~/.elan/bin/lake env lean "$f"
done

env PATH="$HOME/.elan/bin:$PATH" bash scripts/check_axioms.sh
test -z "$(git status --porcelain)"
```

### Full application replay

```bash
set -euo pipefail

review_venv="$(mktemp -d)"
python3 -m venv "$review_venv"
"$review_venv/bin/python" -m pip install -r requirements-dev.txt
export PATH="$review_venv/bin:$HOME/.elan/bin:$PATH"

env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 MAKEFLAGS=-j1 \
  make verify-controlled-queue-model
env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 MAKEFLAGS=-j1 \
  make verify-controlled-queue-trace
env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 MAKEFLAGS=-j1 \
  make verify-controlled-queue-known-kernel-receipt
env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 MAKEFLAGS=-j1 \
  make verify-controlled-queue-structured-ope-code-freeze
```

Do not run `make verify-controlled-queue-structured-ope-prospective-receipt`
before public registration and authorized generation. That target deliberately
requires artifacts that do not exist at the review target.

## Explicit nonclaims

- The offline IID result is not an optional-stopping theorem.
- Data-dependent selectors choose only among catalogs fixed before the common
  event; they do not construct a new path-fitted model or selected e-process.
- The generic unknown-kernel informative checker proves paths outside the risk
  exceptional event while supplying row-TV errors exactly; it is not an
  end-to-end same-path receipt outside the combined risk-plus-transition event.
- The retrospective `< 7/100` conclusion is conditional on both histogram and
  event-inequality premises; named-trace good-event membership is not proved.
- The prospective protocol is not a registration, trace, receipt, numerical
  result, or successful `< 1/10` certificate.
- The structured adaptive and frozen sharp queue theorems assume the true
  environment belongs to the stated refresh family; they do not test that
  family or cover arbitrary kernels.
- The frozen sharp wrapper targets a canonical invariant witness and does not
  prove uniqueness for the off-grid true persistence parameter.
- The application does not claim policy optimization, regret, cumulative
  value, or general continuous-state control.

## Review record

A useful response is short and exact. Record either a GitHub review permalink
or, with the reviewer's permission, a file under
`docs/reviews/v0.2/responses/<date>-<lane>-<reviewer>.md` using this schema:

```text
Reviewer:
Affiliation or relevant expertise:
Conflict and independence disclosure:
Review lane: probability/statistics | Lean/artifacts
Review date:
Target commit: 1aca197cbcf1c2f483c212db508d1d488b700b40
Materials read and commands run:
Verdict: accept | accept with caveats | changes required | unable to assess
Findings with theorem/file/line anchors:
Unresolved questions:
Permission to cite or publish this response:
```

An approval should state what was actually reviewed; it should not be reported
as an audit of the other lane or of the whole repository.

## Review status

| Lane | Status | Durable record |
|---|---|---|
| Probability/statistics | **OPEN** | No external response recorded |
| Lean/artifacts | **OPEN** | No external response recorded |
