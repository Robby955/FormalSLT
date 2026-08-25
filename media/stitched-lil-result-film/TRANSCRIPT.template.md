# Main-film transcript

The film has no voiceover. This is the accessible version of its burned-in
copy and essential visual mathematics.

## 00:00.000 — A fixed-time guarantee assumes one fixed look

One interval answers one fixed-sample question. The data path continues. The
checked theorem instead supplies one event controlling every sample size
`n >= 4`.

## 00:08.000 — The process Lean checks

Each measurable, integrable increment `X_k` is strongly measurable with respect
to `F_(k+1)`. Almost everywhere, `|X_k| <= b`,
`E[X_k | F_k] = 0`, and `E[X_k^2 | F_k] <= sigma^2`. The theorem assumes
`0 < delta <= 1`, `b > 0`, and `sigma^2 > 0`.

This is a bounded martingale-difference-style model. It does not require IID
increments and does not estimate the variance proxy from the observed path.

## 00:20.000 — Divide sample sizes geometrically

The checked selector assigns each `n >= 4` to a factor-four epoch:
`[4,16)`, `[16,64)`, `[64,256)`, and onward. For the selected epoch `j`,
`4^(j+1) <= n < 4^(j+2)`.

## 00:33.000 — Spend the error budget once

Epoch `j` receives `w_j = 1 / ((j+1)(j+2))`. The identity
`w_j = 1/(j+1) - 1/(j+2)` telescopes, and the infinite sum of the weights is
exactly one.

## 00:46.000 — Precommit one tilt per epoch

The exact two-sided budget is
`B_j = log(2/delta) + log(j+1) + log(j+2)`. One admissible sub-Gamma tilt is
optimized at each epoch floor before the path is observed.

The curves evaluate the actual fixed-tilt expression
`subGammaCgf(sigma^2,b,lambda_j)/lambda_j + B_j/(n lambda_j)` at declared
parameters `sigma^2 = 0.08`, `b = 0.25`, and `delta = 0.05`, on a log-scaled
sample-size axis. For the checker's first epoch, `delta = 1/2`, `j = 0`, and
`B_0 = log 8` exactly.

## 01:00.000 — Stitch the epochs

The upper and lower segments evaluate the displayed `W_n` at every integer
sample size in the plotted epochs, splitting at each epoch jump; the path is
illustrative. Each fixed tilt controls a crossing
event. Countable subadditivity and `sum_j delta w_j = delta` yield one event
whose complement has real mass at most `delta`.

This allocation is not itself a countable e-process.

## 01:14.000 — A checked log-log confidence sequence

For selected `j`, define
`B_j = log(2/delta) + log(j+1) + log(j+2)` and
`W_n = 2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n)`.

{{MAIN_CONFIDENCE_PARAGRAPH}}

The theorem is
`{{THEOREM_FQN}}`
at {{SOURCE_DESCRIPTION}}.

This is a formalized allocated fixed-tilt composition with an
iterated-logarithm-order price. It is not the law of the iterated logarithm,
does not make a sharp-constant claim, is not an empirical-variance-adaptive or
optional-stopping result, and is not itself an e-process. {{MEASURABILITY_SENTENCE}}
