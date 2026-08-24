# Storyboard: one guarantee across every n >= 4

Target: 86 seconds, 16:9, caption-led, no voiceover. The instrumental score
supports the cuts but never carries mathematical information. The animated
sample path is illustrative; no numerical performance claim is attached to it.

## 00:00-00:08 — Fixed time is one question

An ivory running-mean trace moves across a dark coordinate plane. One vertical
slice at `n = 16` receives a narrow cyan interval, then the trace continues
beyond it. The isolated slice recedes.

On screen:

> One guarantee across every `n >= 4`.

> A fixed-time interval answers only one fixed-time question.

The contrast is fixed-time versus time-uniform inference, not a claim that a
fixed-time interval is intrinsically invalid.

## 00:08-00:20 — The process model

Four restrained cards enter around a central `X_0, X_1, ...` spine:

- `X_k revealed at time k+1`
- `|X_k| <= b`
- `E[X_k | F_k] = 0`
- `E[X_k^2 | F_k] <= sigma^2`

A compact footer records `0 < delta <= 1`, `b > 0`, and `sigma^2 > 0`.

On screen:

> Revealed at time `k+1`; centered given `F_k`.

This is the actual theorem model, not an IID or empirical-variance claim.

## 00:20-00:33 — Geometric epochs

A log-scaled timeline divides into `[4,16)`, `[16,64)`, `[64,256)`, and
`[256,1024)`. The left endpoints pulse once in amber. The formula
`N_j = 4^(j+1)` sits above the axis; `j = selected epoch for n` sits below.

On screen:

> Each `n >= 4` belongs to one factor-four epoch.

The interval convention comes directly from the checked floor/horizon and
epoch-index specification.

## 00:33-00:46 — Polynomial allocation

The weights `1/2`, `1/6`, `1/12`, `1/20`, ... arrive as amber tiles. Each tile
turns into `1/(j+1) - 1/(j+2)`. Adjacent terms cancel, leaving a single cyan
`sum_j w_j = 1` lockup.

On screen:

> `w_j = 1 / ((j+1)(j+2))`

> The weights telescope exactly to one.

This scene earns the later countable union visually; it is not decorative
algebra.

## 00:46-01:00 — Predeclared tilts

One thin sub-Gamma line appears for every epoch and extends faintly across the
whole time axis. Its matched epoch segment brightens. A dot at the left endpoint
marks where the epoch's tilt is optimized.

The budget is introduced in two readable lines:

`B_j = log(2/delta)`

`      + log(j+1) + log(j+2)`

On screen:

> One fixed tilt per epoch, chosen before the path.

Do not imply that the tilt changes predictably within an epoch or is selected
from the observed data.

## 01:00-01:14 — Stitch

The faint all-time lines remain visible while their active epoch segments join
into an upper envelope. A reflected lower envelope appears. A small failure
ledger accumulates `delta w_0 + delta w_1 + ... = delta` and resolves to one red
sliver labeled `failure mass <= delta`.

On screen:

> One two-sided event. Every `n >= 4`.

> Countable subadditivity, not a countable e-process.

Each epoch atom is itself an all-time fixed-tilt crossing event. The proof then
selects the tilt matched to the current epoch; the film keeps the unused parts
of every line faintly visible to preserve that distinction.

## 01:14-01:26 — The theorem

The final card gives named pieces rather than one oversized formula:

`B_j = log(2/delta) + log(j+1) + log(j+2)`

`W_n = 2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n)`

`|mean_n| < W_n   for every n >= 4`

`failure mass <= delta`

The composition contracts to the FormalSLT wordmark, source commit `285921b`,
and a split identifier:

`AnytimeValid.PolynomialStitchedLIL`

`exists_polynomialStitchedLIL_explicit_event`

Final scope line:

> Checked log-log confidence sequence. Not the LIL law. Not itself an e-process.

## Visual system

- Background `#08111E`; ivory `#F4F1E8`; cyan `#64D8D2`; amber `#F0B35A`;
  muted blue-gray `#A7B3C2`; red `#EF6A68` only for failure mass.
- Avenir Next for prose and Menlo for mathematical identifiers.
- Minimum 42 px body-equivalent size at 1080p. No paragraph exceeds two lines.
- Essential content stays inside a centered 1536 by 864 safe area.
- Movement is limited to the trace, epoch segmentation, telescoping
  cancellation, active tilt segments, and final stitch. Text does not float or
  continually rescale.
- Scene cuts coincide with soundtrack cues at 0, 8, 20, 33, 46, 60, and 74
  seconds.

## Evidence anchors

The extractor binds these claims to the exact merged source commit:

- process and endpoint assumptions:
  `FormalSLT/AnytimeValid/PolynomialStitchedLIL.lean`, theorem
  `exists_polynomialStitchedLIL_explicit_event`;
- geometric floor, horizon, and selector specification: the same module;
- exact polynomial weights and total mass:
  `FormalSLT/AnytimeValid/AllocationLogLog.lean`;
- first-epoch receipt, endpoint checks, and axiom-query surface:
  `examples/CheckPolynomialStitchedLIL.lean`;
- scope and novelty boundaries: the module docstring,
  `docs/proof-frontier.md`, `docs/assumptions-and-nonclaims.md`, and
  `docs/related-work.md`.
