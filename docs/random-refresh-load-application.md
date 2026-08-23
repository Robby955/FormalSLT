# Twenty-state random-refresh load application

This application exercises the stationary, unknown-kernel, trajectory, and
selection layers on one fully explicit finite Markov model. It is a checked
research application, not part of the small v0.2 stable-endpoint promise.

## Model

The state space is `Fin 20`, interpreted as five load levels crossed with four
regimes. Each candidate kernel has the form

```text
gamma * pointMass(successor state) + (1 - gamma) * uniform(Fin 20)
```

with `gamma` equal to `1/8`, `1/4`, or `3/8`. The uniform law is invariant for
all three kernels, their exact Dobrushin coefficients are their corresponding
`gamma` values, and the row total-variation distance from the nominal kernel is
`19/160`, `0`, and `19/160`.

Four predeclared predictors estimate next-step overload under binary Brier
loss. Their exact stationary risks are:

| Kernel | constant | loadOnly | oracle | early |
|---|---:|---:|---:|---:|
| low gamma | `4/25` | `4/25` | `4/25` | `69/400` |
| nominal gamma | `4/25` | `99/640` | `3/20` | `7/40` |
| high gamma | `4/25` | `239/1600` | `7/50` | `71/400` |

The model-specific centered row-risk oscillation envelopes are `7/80`, `7/40`,
and `21/80`; the `early` predictor attains each envelope.

## Periodic arithmetic path

The deterministic `balancedPath` repeats a `1,600`-transition block: three
complete order-two de Bruijn circuits followed by twenty complete successor
cycles. Every positive whole-block horizon realizes the nominal transition
table exactly and has empirical oracle Brier risk `3/20`; there is no
eventually homogeneous successor-cycle tail. At the reported `200,000 =
125 * 1,600` horizon, it visits every source state `10,000` times and has:

```text
successor edge frequency = 23/80
every other edge frequency = 3/80
```

These arithmetic identities remove the former long-run tail contradiction.
They do not show that the path is typical or that it belongs to any
theorem-produced good event.

## Primary receipt

For the oracle posterior at horizon `200,000`, Lean checks:

| Quantity | Checked value or bound |
|---|---:|
| Empirical Brier risk | `3/20` |
| Corrected-score Bessel statistic | `722853659625 / 112710098` |
| Known-kernel width | at most `20679874814747 / 1937166336000000` |
| Known-kernel empirical-risk plus width | below `1607/10000` |
| Empirical all-row TV budget | at most `174387/896000` |
| Unknown-kernel width | at most `3802036720268663 / 7748665344000000` |
| Unknown-kernel empirical-risk plus width | below `6407/10000` |

This numerical receipt evaluates the fixed nominal-kernel, depth-five,
risk-tilt-five, oracle-posterior atom inside the simultaneous catalog. The
path-dependent selector theorem below is a separate result and is not used to
produce these displayed numbers. The application also retains one fixed
transition-confidence atom; the separate countable transition extension is
not instantiated by this numerical receipt.

The transferred Dobrushin coefficient is strictly below one. One theorem gives
a common event whose complement has real outer mass at most `1/20`, supporting
the known- and empirical-kernel inequalities at every covered path and time.
The displayed numerical conclusion for `balancedPath` is conditional on that
path belonging to the event. The library does not prove event measurability or
membership of this named path.

## Data-dependent selectors

The application also supplies path-and-time selectors for the candidate,
predictor posterior, depth, and risk tilt. On the balanced path the candidate
and predictor selectors choose the nominal kernel and oracle predictor; on a
constant-zero path they choose the low-gamma kernel and `loadOnly` predictor.
The boundary choice is a finite `Fin 9 x Fin 7` classical argmin and is proved
no worse than the fixed `(5, 5)` choice. It is noncomputable and its exact
argmin is not identified. The selector theorem substitutes these functions
into a simultaneous event; it does not construct a selected e-process.

## Finite-catalog oracle certificate

A separate two-sided construction orients each of the eight predictor/flip
scores and places them in one predeclared catalog. On one all-time event whose
complement has real outer mass at most `1/20`, the finite empirical-risk
minimizer has an upper bound, every predictor has a matched lower bound, and
the selected stationary risk is at most the exact catalog minimum `3/20` plus
an explicit selected penalty. The probability quantifier is outside the time
and comparator quantifiers. This certificate is independent of
`balancedPath`; it neither proves that named path belongs to the event nor
claims a measurable selector construction.

## Confidence-matched, separate-event baselines

The three baselines use distinct exceptional events, but every risk event has
the same failure budget `1/40`. The numerical widths are therefore matched in
confidence level, although they are not same-event comparisons:

| Construction | Empirical-risk plus width |
|---|---:|
| Primary variance-adaptive, fixed depth/tilt atom | below `0.1607` |
| Fixed unit-range Poisson construction | below `0.1749` |
| Fixed depth five, without depth-allocation price | below `0.158` |
| Fixed-tilt non-variance-adaptive construction | below `0.157` |

On this instance, the proved numerical upper thresholds for the fixed-depth
and fixed-tilt baselines are smaller than the corresponding proved threshold
for the selected empirical-Bernstein construction. The checked results do not
prove the exact width ordering or any uniform dominance theorem.

## Verification

From the repository root:

```bash
~/.elan/bin/lake exe cache get
make verify-random-refresh-load
bash scripts/check_axioms.sh
bash scripts/check_witness_quality.sh
```

The component checkers pair every public declaration with `#check` and every
public theorem with `#print axioms`. The accepted axiom set is
`[propext, Classical.choice, Quot.sound]`.
