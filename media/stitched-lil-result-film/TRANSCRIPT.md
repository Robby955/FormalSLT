# Transcript: polynomial stitched confidence sequence

The film has no voiceover. Its original instrumental score contains no spoken
information. This is the accessible, searchable version of the burned-in copy
and the essential visual mathematics.

## 00:00.000 — One guarantee across every n >= 4.

A fixed-time interval answers one fixed-time question. The data path continues,
and repeated observation asks for a guarantee that remains valid across the
whole timeline.

## 00:08.000 — The process model

FormalSLT assumes measurable, integrable increments. Increment `X_k` is
revealed at time `k+1`, while its conditional mean and second-moment bound are
taken with respect to the past `F_k`. The increments are bounded by `b`; the
theorem takes `0 < delta <= 1`, `b > 0`, and `sigma^2 > 0`.

This is a bounded martingale-difference-style theorem. It does not assume IID
data, and it does not estimate the variance proxy from the observed path.

## 00:20.000 — Divide time geometrically

For `n >= 4`, time is split into factor-four epochs:

`[4,16)`, `[16,64)`, `[64,256)`, and onward.

Epoch `j` has floor `4^(j+1)`. The checked epoch selector places every eligible
sample size between that floor and four times the floor.

## 00:33.000 — Spend the error budget once

Epoch `j` receives polynomial weight

`w_j = 1 / ((j+1)(j+2))`.

The identity

`w_j = 1/(j+1) - 1/(j+2)`

makes the allocation telescope. The infinite sum of the weights is exactly
one, so the allocated failure masses sum to `delta`.

## 00:46.000 — Precommit one tilt per epoch

Every epoch receives one admissible sub-Gamma tilt optimized at its left
endpoint. The tilt is fixed before observing the path. Its exact two-sided
confidence budget is

`B_j = log(2/delta) + log(j+1) + log(j+2)`.

For the checker's concrete first epoch, `delta = 1/2`, `j = 0`, and the budget
is exactly `log 8`.

## 01:00.000 — Stitch the epochs

Each epoch tilt defines an all-time fixed-tilt crossing event. The proof controls
that event at mass `delta w_j`, selects the tilt matched to the current epoch,
and uses countable subadditivity over all epochs.

The result is one two-sided guarantee for every `n >= 4`. This confidence
allocation is not itself a countable e-process.

## 01:14.000 — A checked log-log confidence sequence

Let `j` be the selected epoch and define

`B_j = log(2/delta) + log(j+1) + log(j+2)`.

Define

`W_n = 2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n)`.

Outside one failure set of mass at most `delta`,

`|runningMean X n| < W_n`

for every `n >= 4`.

The source is
`FormalSLT.AnytimeValid.PolynomialStitchedLIL.exists_polynomialStitchedLIL_explicit_event`
at commit `285921b`. This is a checked confidence sequence with an exact
iterated-logarithm-order budget. It is not a proof of the law of the iterated
logarithm, a sharp-constant claim, or a countable e-process.
