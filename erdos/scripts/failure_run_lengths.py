#!/usr/bin/env python3
"""Longest consecutive-failure runs for B(theta, K) in a top decade segment.

Theorem A survives B(theta) failures as long as failing x's never form runs
of length ~ x^theta (see note §5(b)).  This script measures, on a segment
[LO, HI), the exact set of failing x (no conservative rounding: per-x window
check against the certificate threshold) and reports the maximal run length
and its ratio to x^theta.
"""

import json
import math
import sys
import time

import numpy as np

LO = 9 * 10 ** 7
HI = 10 ** 8
K = 10.0
THETAS = [("1/3", 1.0 / 3.0), ("0.30", 0.30), ("1/4", 0.25), ("1/5", 0.20)]
OUT = sys.argv[1] if len(sys.argv) > 1 else "failure_runs.json"

t0 = time.time()
PAD = 5000  # window can reach below LO
lim = math.isqrt(HI) + 1
bs = np.ones(lim + 1, dtype=bool)
bs[:2] = False
for p in range(2, math.isqrt(lim) + 1):
    if bs[p]:
        bs[p * p :: p] = False
PRIMES = [int(p) for p in np.nonzero(bs)[0]]

base = LO - PAD
size = HI - base
lpf = np.zeros(size, dtype=np.uint16)
for p in PRIMES:
    first = max(2 * p, ((base + p - 1) // p) * p)
    start = first - base
    if start >= size:
        continue
    view = lpf[start::p]
    view[view == 0] = p
print(f"[{time.time()-t0:6.1f}s] sieve done on [{base},{HI})", flush=True)

lpf_i = lpf.astype(np.int32)


def sliding_max(arr, w):
    """max over each length-w window; out[j] = max(arr[j : j + w])."""
    n = len(arr)
    nb = -(-n // w)
    A = np.concatenate([arr, np.full(nb * w - n, -1, dtype=arr.dtype)])
    B = A.reshape(nb, w)
    pre = np.maximum.accumulate(B, axis=1).ravel()
    suf = np.maximum.accumulate(B[:, ::-1], axis=1)[:, ::-1].ravel()
    return np.maximum(suf[: n - w + 1], pre[w - 1 : n])


res = {}
for name, th in THETAS:
    # exact per-x check via sliding-window maximum of composite lpf
    fail = np.zeros(HI - LO, dtype=bool)
    # windows have slowly varying length; process in chunks with fixed w
    CH = 10 ** 6
    for clo in range(LO, HI, CH):
        chi = min(clo + CH, HI)
        w = int(clo ** th)  # window length floor(x^th) varies by <1 over chunk
        # sliding max over [x-w+1, x] of composite lpf, threshold K*x^th
        # build via stride trick per chunk
        arr = lpf_i[clo - w + 1 - base : chi - base]
        best = sliding_max(arr, w)  # best[j] = max lpf in window ending at clo+j
        xs = np.arange(clo, chi, dtype=np.float64)
        thr = K * xs ** th
        # exact per-x window length: recompute for x where int(x**th) != w
        wl = np.floor(xs ** th).astype(np.int64)
        fail_chunk = best <= thr
        # for x with wl != w, do exact recheck (rare, boundary of chunk)
        odd = np.nonzero(wl != w)[0]
        for j in odd:
            x = int(xs[j])
            wj = int(wl[j])
            m = lpf_i[x - wj + 1 - base : x + 1 - base]
            mb = m.max() if len(m) else 0
            fail_chunk[j] = mb <= K * x ** th
        fail[clo - LO : chi - LO] = fail_chunk
    # run lengths
    f = fail.astype(np.int8)
    total = int(f.sum())
    if total == 0:
        res[name] = {"total_failures": 0}
        print(f"theta={name}: no failures in [{LO},{HI})", flush=True)
        continue
    d = np.diff(np.concatenate(([0], f, [0])))
    starts = np.nonzero(d == 1)[0]
    ends = np.nonzero(d == -1)[0]
    runs = ends - starts
    imax = int(np.argmax(runs))
    xmax = int(LO + starts[imax])
    rmax = int(runs[imax])
    ratio = rmax / (xmax ** th)
    res[name] = {
        "theta": th,
        "segment": [LO, HI],
        "total_failures": total,
        "fail_fraction": total / (HI - LO),
        "num_runs": int(len(runs)),
        "mean_run": float(runs.mean()),
        "max_run": rmax,
        "max_run_at": xmax,
        "max_run_over_x_theta": ratio,
        "runs_exceeding_x_theta": int((runs > (LO ** th)).sum()),
    }
    print(
        f"theta={name}: failures {total} ({100*total/(HI-LO):.2f}%), runs "
        f"{len(runs)}, mean run {runs.mean():.1f}, max run {rmax} at x={xmax} "
        f"(= {ratio:.3f} * x^theta), runs>x^theta: {res[name]['runs_exceeding_x_theta']}",
        flush=True,
    )

with open(OUT, "w") as f:
    json.dump(res, f, indent=2)
print(f"[{time.time()-t0:6.1f}s] wrote {OUT}")
