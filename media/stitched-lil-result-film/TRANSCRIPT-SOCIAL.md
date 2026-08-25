# Mobile-film transcript

The 4:5 film has no voiceover. This is its accessible burned-in copy.

## 00:00.000 — A fixed-time guarantee assumes one fixed look

Real systems keep monitoring. This theorem supplies one event controlling every
sample size `n >= 4`.

## 00:07.000 — What the theorem actually assumes

`X_k` is strongly measurable with respect to `F_(k+1)`. The boundedness,
conditional-centering, and conditional second-moment relations hold almost
everywhere. The model is adapted and need not be IID.

## 00:15.000 — Geometric sample sizes, one error budget

Factor-four epochs receive weights `1/2`, `1/6`, `1/12`, `1/20`, and onward.
They telescope to one. The selected epoch satisfies
`4^(j+1) <= n < 4^(j+2)` and has budget
`B_j = log(2/delta) + log(j+1) + log(j+2)`.

## 00:26.000 — Stitch the epochs

The segments evaluate the displayed width at every plotted integer sample size
for `sigma^2 = 0.08`, `b = 0.25`, and `delta = 0.05`, splitting at the epoch
jumps; the path is illustrative. The allocated complement masses
sum to at most `delta`.

## 00:35.000 — One checked event, every sample size from four onward

For selected `j`,
`W_n = 2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n)`. The theorem's measurable event `G` has
`mu.real(G) >= 1 - delta`, and on `G` the running-mean bound holds for every
`n >= 4`.

Source:
`FormalSLT.AnytimeValid.PolynomialStitchedLIL.polynomialStitchedLIL_explicit_measurable_event`,
FormalSLT main commit
`44ebbff74aea1dcd5b25592aefb561aeede51696`.

Allocated fixed-tilt stitch. No sharp-constant claim. Not itself an e-process.
The theorem proves that `G` is measurable, so the displayed
mass bound is an ordinary probability-at-least statement.
