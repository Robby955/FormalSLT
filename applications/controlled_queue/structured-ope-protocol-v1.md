# Prospective structured queue OPE protocol v1

Status: **PROSPECTIVE PROTOCOL ONLY — NO TRACE, RESULT, OR CONFIDENCE
RECEIPT**

This file is the human-readable companion to
[`structured-ope-protocol-v1.json`](structured-ope-protocol-v1.json). The JSON
is the fail-closed analytic contract. If prose and JSON differ, the JSON wins.

## Why this protocol exists

The existing `trace-v1` and known-kernel receipt were useful engineering and
power-analysis pilots, but the source family and off-grid gamma, horizon,
depth, confidence allocations, tilts, threshold, and reported atom were chosen
after that trace had been inspected. They are retrospective evidence. This
protocol freezes an independent confirmatory experiment before its randomness
is available.

The protocol commit itself is not enough. Before generation, one public,
immutable OSF registration must archive receipts for both this commit and the
still-to-be-written generator/verifier code freeze. Its API `date_registered`
field is converted to an integer Unix time exactly as specified in the JSON.
That time determines one scheduled League of Entropy drand `quicknet` round at
least one hour later. A fetch or signature-verification failure aborts the run;
it never advances to another round. The chain identity, public key, round
formula, seed derivation, and counter-stream test vector are frozen in the JSON.
OSF describes registrations as permanent time-stamped versions, and drand's
official API documents round retrieval and verification:
<https://developer.osf.io/>,
<https://docs.drand.love/developer/API-v2/drand-http-api/>.

## Frozen primary analysis

- Source family: the checked one-parameter refresh family with true
  `gamma = 149/200`, which is not one of the three candidate values.
- Path: `200,000` scored transitions from fixed controlled observation
  `(eco, state 0)`, with no suffix discard or random-initial conditioning.
- Estimand: stationary Brier risk of the queue-threshold target policy and the
  fixed nominal-model overload predictor.
- Analysis: nominal candidate, the predeclared shifted depth-12 potential,
  Dirac posterior on that policy/predictor atom, risk tilt `1/16`, persistence
  tilt `1/64`, and failure budgets `1/40 + 1/40`.
- Decision rule: the sharp structured endpoint is successful exactly when it
  is below `1/10`. A result above that threshold is published unchanged.

This is a fixed confirmatory primary. It is not adaptive candidate/depth
selection. The separately declared 21-atom finite-catalog result is secondary
and cannot rescue a failed primary.

Before the formula-selected beacon round is read, the code freeze must include
the generic checked histogram-to-endpoint theorem named in the JSON contract.
Fresh generated data may instantiate that theorem but may not introduce a new
post-data reduction or branch. The fixed-range comparison remains explicitly
`PLANNED_NOT_CHECKED` and is not a confidence certificate until its separate
target-policy event theorem exists.

## Formal work still required before generation

The generic checked `D = 1` structured theorem is too loose for the primary
claim. The sharper refresh-family drift-sensitivity event is now checked on the
later code-freeze branch. The protocol freezes its residual exactly as

```text
candidate drift oscillation
  + refresh drift-sensitivity oscillation × persistence TV budget.
```

The receipt proof must also establish the sharper fixed-tilt inequalities
`psi(1/16) <= 1/480` and `psi(1/64) <= 1/8064` frozen in the JSON; the older
coarser arithmetic is not silently substituted.

All receipt values are authoritative reduced rationals. The preregistered
arithmetic always uses the affine Bessel upper branch and the frozen rational
psi and log-cost bounds; it may not inspect the trace and switch to a smaller
harmonic branch. Decimal displays use fifteen places with half-even rounding
and never control a strict threshold comparison. The two causal Beta predictors
are scored with their pre-update probabilities, updated afterward, and reported
only as descriptive dynamic encountered-risk sums and means.

The generator, independent trace verifier, receipt generator, independent
receipt verifier, Lean data renderer, and adversarial tests must also be frozen
before the OSF registration that binds both commits. No fresh output listed in
the JSON may exist during protocol or code-freeze validation.

## Reporting contract

The single trace, counts, exact selected endpoint, adaptive secondary, and all
matched baselines will be published regardless of whether the primary target
is met. The report must show the empirical score, statistical correction,
persistence radius, model-misspecification residual, total endpoint, and
confidence allocation for every row. Candidate, seed, horizon, endpoint,
selector, deltas, and threshold cannot be changed after the beacon is known.

The fixed comparisons include an oracle known-true-kernel row whose depth-12
potential uses the uniform physical-state centering reference, is shifted to
zero at state `0`, and uses exact max-minus-min span and drift-oscillation
conventions; generic `D = 1` depth-12 and depth-5 rows; a non-variance
fixed-range row; and the full
4,608-coordinate empirical-transition construction. Separate confidence events
are reported as separate events unless a later theorem explicitly proves a
common-event allocation.

## Boundaries

This protocol is not a theorem, a generated trace, a numerical certificate, a
family-membership test, or a guarantee that the endpoint will be useful. Lean
will certify receipt arithmetic and theorem composition; independent manifests
and replay verifiers, not Lean, will bind SHA-256 hashes, beacon signatures, and
raw trace bytes. The two causal Beta predictors remain in the dynamic
encountered-risk comparison lane and are not relabeled as stationary target-
policy hypotheses.
