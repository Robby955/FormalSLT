# Erdős walk problem lane: visible points with a composite coordinate

This directory is a self-contained research lane, separate from the
FormalSLT statistical-learning-theory library, on the open Erdős problem:

> Is there an infinite unit-step path through lattice points $(x,y)$ with
> $x, y > 1$, $\gcd(x,y) = 1$, and at least one coordinate composite?

**Status: open.** Nothing here claims a solution.

## Contents

* [`notes/monotone-admissible-paths.md`](notes/monotone-admissible-paths.md)
  — the working note. New results proved there, extending the prior
  composite-anchor partial results:
  * **Theorem C (unconditional).** Every dyadic window $[X, 2X]$ with
    $X \ge \exp(C\,m\log m)$ contains an $m$-stage monotone admissible path
    (prior construction: one path somewhere, at height
    $\exp(m\,e^{m(1+o(1))})$). Finite paths are ubiquitous at every scale;
    only reachability between scales is missing.
  * **Theorem A (conditional).** If for a single fixed
    $\theta \in (0, 1/2)$ every window $(x - x^\theta, x]$ contains a
    composite $a$ with $P^-(a) > 10x^\theta$ (hypothesis B($\theta$)), then
    an infinite monotone admissible path exists. Robust to failures of
    B($\theta$) on runs shorter than $\sim x^\theta$. This replaces the
    apparent need for balanced semiprimes at square-root scale by a
    worst-case supply statement at *any* power scale, with no coprimality
    side conditions.
  * **Proposition B.** An explicit certificate mechanism
    $a = p\lfloor x/p\rfloor$ with $\lfloor x/p \rfloor$ prime, linking
    B($\theta$) to the floor-quotient-primes literature.
  * **Lemma 2′/Corollary 2″ (unconditional).** Transversal blocking lemma
    and escape rate: any visible-point path with coordinates $> 1$ spanning
    horizontal distance $D$ reaches height $\gg \log D/\log\log D$.
  * A scale analysis (§7) of why multi-row "ladder" schemes stall exactly at
    the quadratic-vs-linear Jacobsthal gap, and a Rankin-type proof (§5(c))
    that the chain strategy is impossible at polylogarithmic scale — power
    scale is forced.
  * A Lean 4 formalization plan (§10): the elementary results (Lemmas 1, 2′,
    3, Proposition 1, Theorem A as a conditional) are direct Mathlib
    targets; Theorem C admits a fully elementary variant via exact periodic
    counting, avoiding sieve machinery. Not formalized in this session: the
    sandbox network policy blocked the Lean toolchain and Mathlib cache
    downloads.

* `scripts/` — verification experiments (Python 3 + NumPy, exact integer
  sieves):
  * `build_explicit_path.py` — builds a greedy gap-condition chain on
    $[10^9, 10^9 + 5\cdot 10^6)$ and **pointwise-verifies** the resulting
    monotone admissible path: 144,486 stages, 288,972 turns, 9,999,882 unit
    edges, zero violations. All 144,488 available anchors chain up with no
    dead ends (max anchor gap 374 vs. roughness floor 1500).
  * `verify_bridge_hypothesis.py` — stress-tests B($\theta$) for
    $\theta \in \{1/3, 0.30, 1/4, 1/5\}$ over all $x \le 10^8$.
  * `failure_run_lengths.py` — exact failing-run statistics on
    $[9\cdot 10^7, 10^8]$: for $\theta = 1/3$, failure rate 1.46%, longest
    failing run $1.70\,x^\theta$ — the run-robust hypothesis of the note's
    §5(b) holds at these heights with a small constant.
  * `floor_mechanism_stats.py` — certificate counts for the floor-quotient
    semiprime mechanism (median 5 certifying primes per window at
    $x \sim 10^8$–$10^9$, $\theta = 1/3$; 0.45% of samples need the more
    general certificates).

* `data/` — JSON outputs of the four scripts, as cited in the note.

## Reproducing

```bash
cd erdos
python3 scripts/build_explicit_path.py       data/explicit_path.json      # ~5 s
python3 scripts/verify_bridge_hypothesis.py  data/bridge_results.json     # ~90 s
python3 scripts/failure_run_lengths.py       data/failure_runs.json       # ~75 s
python3 scripts/floor_mechanism_stats.py     data/floor_mechanism.json    # ~60 s
```

Requires `numpy` (and nothing else; `sympy` is not used by the final
scripts).

## Relation to the main library

None yet: no Lean code is added by this lane so far, and nothing in the
FormalSLT public surface depends on it. The formalization plan in the note
(§10) lists the intended `Erdos/*.lean` modules; per repository policy they
will only land together with a verified `lake build`.
