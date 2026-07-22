#!/usr/bin/env python3
"""Computational check of the bridge hypothesis B(theta, K).

B(theta, K): for every integer x >= x0, the window (x - x^theta, x] contains a
composite integer a with least prime factor P^-(a) > K * x^theta.

Method
------
Segmented least-prime-factor sieve on [2, N] with primes up to sqrt(N).
Any n <= N left unmarked by primes <= sqrt(N) is prime, hence never a
certificate; every composite a <= N has P^-(a) <= sqrt(N) and gets its exact
least prime factor.

A composite a with lpf v certifies every x in the conservative interval

    a <= x <= min(a + floor(a^theta), ceil((v/K)^(1/theta)) - 1, N - 1)

because x >= a gives x^theta >= a^theta (so a > x - x^theta), and
x <= (v/K)^(1/theta) - 1 gives K*x^theta < v.  Coverage is accumulated with a
difference array per segment (with cross-segment tail).  Uncovered x are
*conservative* failures (true failures are a subset).

Output: for each theta, the largest conservatively-failing x, failure counts
by decade, and sampled margin statistics
    max{ lpf(a) : a composite in window } / (K x^theta).
"""

import json
import math
import sys
import time

import numpy as np

N_END = 10 ** 8
SEG = 2 * 10 ** 7
K = 10.0
THETAS = [("1/3", 1.0 / 3.0), ("0.30", 0.30), ("1/4", 0.25), ("1/5", 0.20)]
REPORT_FROM = 1000  # ignore x below this in failure reporting
SAMPLE_STRIDE = 9973  # margin sampling stride

OUT = sys.argv[1] if len(sys.argv) > 1 else "bridge_results.json"

t0 = time.time()

lim = math.isqrt(N_END) + 1
bs = np.ones(lim + 1, dtype=bool)
bs[:2] = False
for p in range(2, math.isqrt(lim) + 1):
    if bs[p]:
        bs[p * p :: p] = False
PRIMES = [int(p) for p in np.nonzero(bs)[0]]
print(f"[{time.time()-t0:6.1f}s] {len(PRIMES)} sieving primes up to {lim}", flush=True)

MAXTAIL = 6000  # > max cover length: floor(a^theta) <= (1e8)^(1/3) ~ 4642

results = {
    name: {
        "theta": th,
        "K": K,
        "N": N_END,
        "uncovered_ge_report": 0,
        "max_uncovered": None,
        "uncovered_by_decade": {},
        "_margins": [],
    }
    for name, th in THETAS
}
carry = {name: np.zeros(MAXTAIL, dtype=np.int64) for name, _ in THETAS}
uncovered_lists = {name: [] for name, _ in THETAS}

seg_starts = list(range(0, N_END, SEG))
for base in seg_starts:
    hi = min(base + SEG, N_END)
    n0 = max(base, 2)
    size = hi - base
    lpf = np.zeros(size, dtype=np.uint16)
    for p in PRIMES:
        first = max(2 * p, ((base + p - 1) // p) * p)  # never mark p itself
        start = first - base
        if start >= size:
            continue
        view = lpf[start::p]
        view[view == 0] = p
    comp_idx = np.nonzero(lpf)[0]
    a = comp_idx.astype(np.int64) + base
    v = lpf[comp_idx].astype(np.float64)
    keep = a >= 4
    a = a[keep]
    v = v[keep]
    print(
        f"[{time.time()-t0:6.1f}s] segment [{base},{hi}): {len(a)} composites",
        flush=True,
    )

    for name, th in THETAS:
        af = a.astype(np.float64)
        cover_end = a + np.floor(af ** th).astype(np.int64)
        cap = np.ceil((v / K) ** (1.0 / th)).astype(np.int64) - 1
        end = np.minimum(np.minimum(cover_end, cap), N_END - 1)
        ok = end >= a
        s_ = (a[ok] - base).astype(np.int64)
        e_ = (end[ok] - base).astype(np.int64)
        L = size + MAXTAIL + 1
        diff = np.bincount(s_, minlength=L)[:L].astype(np.int64)
        diff -= np.bincount(e_ + 1, minlength=L)[:L]
        # inject carried coverage depth from the previous segment
        c = carry[name]
        diff[0] += c[0]
        diff[1 : len(c)] += np.diff(c)
        diff[len(c)] -= c[-1]
        depth = np.cumsum(diff[: size + MAXTAIL])
        segdepth = depth[:size]
        unc = np.nonzero(segdepth[(n0 - base) :] == 0)[0] + n0
        unc = unc[unc >= REPORT_FROM]
        if len(unc):
            uncovered_lists[name].append(unc)
        carry[name] = depth[size : size + MAXTAIL].copy()

        xs = np.arange(
            ((base // SAMPLE_STRIDE) + 1) * SAMPLE_STRIDE, hi, SAMPLE_STRIDE
        )
        xs = xs[xs >= max(REPORT_FROM, base + MAXTAIL)]
        for x in xs[:: max(1, len(xs) // 400)]:
            x = int(x)
            w = int(x ** th)
            lo = max(x - w + 1 - base, 0)
            hiw = x - base + 1
            seg_l = lpf[lo:hiw]
            m = seg_l[seg_l > 0]
            best = int(m.max()) if len(m) else 0
            results[name]["_margins"].append(best / (K * x ** th))

for name, th in THETAS:
    if uncovered_lists[name]:
        allunc = np.concatenate(uncovered_lists[name])
    else:
        allunc = np.array([], dtype=np.int64)
    r = results[name]
    r["uncovered_ge_report"] = int(len(allunc))
    r["max_uncovered"] = int(allunc.max()) if len(allunc) else None
    dec = {}
    for u in allunc:
        d = int(math.log10(u))
        dec[d] = dec.get(d, 0) + 1
    r["uncovered_by_decade"] = {f"1e{d}-1e{d+1}": c for d, c in sorted(dec.items())}
    mg = np.array(r.pop("_margins"))
    r["margin_stats"] = {
        "min": float(mg.min()) if len(mg) else None,
        "p1": float(np.percentile(mg, 1)) if len(mg) else None,
        "p50": float(np.percentile(mg, 50)) if len(mg) else None,
        "n_samples": int(len(mg)),
    }
    ms = r["margin_stats"]
    print(
        f"theta={name}: conservative failures (x>={REPORT_FROM}): "
        f"{r['uncovered_ge_report']}, largest: {r['max_uncovered']}, "
        f"margin(min/p1/p50 of best-lpf/(K x^theta)): "
        f"{ms['min']:.2f}/{ms['p1']:.2f}/{ms['p50']:.2f} over {ms['n_samples']}",
        flush=True,
    )

with open(OUT, "w") as f:
    json.dump(results, f, indent=2)
print(f"[{time.time()-t0:6.1f}s] wrote {OUT}")
