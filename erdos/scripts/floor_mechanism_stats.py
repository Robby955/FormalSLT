#!/usr/bin/env python3
"""Statistics for the floor-quotient semiprime mechanism behind B(theta).

For x and theta, count primes p in (10 x^theta, 20 x^theta] such that

    m = floor(x/p) is prime  and  p*m > x - x^theta,

i.e. a = p*m is a semiprime in the window (x - x^theta, x] with
P^-(a) = min(p, m) = p > 10 x^theta.  Each such p certifies the bridge
hypothesis B(theta, 10) at x through the explicit semiprime a = p*floor(x/p).

We sample many x and report the distribution of the number of certifying p,
in particular the minimum (zero counts = x needs a non-semiprime or
out-of-range certificate).
"""

import json
import math
import random
import sys
import time

import numpy as np

THETA = 1.0 / 3.0
X_LO, X_HI = 10 ** 8, 10 ** 9
N_SAMPLES = 4000
SEED = 20260722
OUT = sys.argv[1] if len(sys.argv) > 1 else "floor_mechanism.json"

t0 = time.time()
# primes p up to 20 * (1e9)^(1/3) = 20000
PLIM = int(20 * X_HI ** THETA) + 10
bs = np.ones(PLIM + 1, dtype=bool)
bs[:2] = False
for q in range(2, math.isqrt(PLIM) + 1):
    if bs[q]:
        bs[q * q :: q] = False
SMALL_PRIMES = np.nonzero(bs)[0].astype(np.int64)

# primality mask for m = floor(x/p) <= x / (10 x^theta) = x^(2/3)/10 <= 1e6
MLIM = int(X_HI ** (1 - THETA) / 10) + 10
mb = np.ones(MLIM + 1, dtype=bool)
mb[:2] = False
for q in range(2, math.isqrt(MLIM) + 1):
    if mb[q]:
        mb[q * q :: q] = False
print(f"[{time.time()-t0:6.1f}s] sieves ready (p<= {PLIM}, m<= {MLIM})", flush=True)

rng = random.Random(SEED)
counts = []
zeros = []
for _ in range(N_SAMPLES):
    x = rng.randrange(X_LO, X_HI)
    w = x ** THETA
    lo, hi = 10 * w, 20 * w
    ps = SMALL_PRIMES[
        np.searchsorted(SMALL_PRIMES, lo, "right") : np.searchsorted(
            SMALL_PRIMES, hi, "right"
        )
    ]
    if len(ps) == 0:
        counts.append(0)
        zeros.append(x)
        continue
    ms = x // ps
    a = ps * ms
    ok = (a > x - w) & mb[ms] & (ms > ps)
    c = int(ok.sum())
    counts.append(c)
    if c == 0:
        zeros.append(x)

counts = np.array(counts)
res = {
    "theta": THETA,
    "range": [X_LO, X_HI],
    "n_samples": N_SAMPLES,
    "count_min": int(counts.min()),
    "count_p10": float(np.percentile(counts, 10)),
    "count_median": float(np.median(counts)),
    "count_mean": float(counts.mean()),
    "count_max": int(counts.max()),
    "num_zero": int((counts == 0).sum()),
    "zero_examples": zeros[:20],
}
print(json.dumps(res, indent=2))
with open(OUT, "w") as f:
    json.dump(res, f, indent=2)
