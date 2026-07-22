#!/usr/bin/env python3
"""Build and pointwise-verify an explicit long monotone admissible path.

Pipeline
--------
1. Least-prime-factor sieve on a window [X, X + SPAN] (primes to sqrt).
2. Anchor set: composites a with P^-(a) >= LMIN.
3. Greedy gap-condition chain a_0 < a_1 < ... with

       a_{n+2} - a_n < min(P^-(a_n), P^-(a_{n+2}))          (C1)

   built by always taking the smallest admissible next anchor.
4. Turn the chain into the monotone L-path

       (a_n, a_{n+1}) -> (a_n, a_{n+2}) -> (a_{n+1}, a_{n+2})

   and verify EVERY lattice point on the path:
     * both coordinates > 1,
     * gcd(x, y) = 1  (visibility),
     * at least one coordinate composite (the anchor coordinate).

The verification is a direct pointwise check with np.gcd, independent of the
theory that predicts it, so a PASS is a machine check of the construction.
"""

import json
import math
import sys
import time

import numpy as np

X0 = 10 ** 9
SPAN = 5 * 10 ** 6
LMIN = 1500  # anchor roughness threshold
OUT = sys.argv[1] if len(sys.argv) > 1 else "explicit_path.json"

t0 = time.time()
lim = math.isqrt(X0 + SPAN) + 1
bs = np.ones(lim + 1, dtype=bool)
bs[:2] = False
for p in range(2, math.isqrt(lim) + 1):
    if bs[p]:
        bs[p * p :: p] = False
PRIMES = [int(p) for p in np.nonzero(bs)[0]]
print(f"[{time.time()-t0:6.1f}s] {len(PRIMES)} primes to {lim}", flush=True)

lpf = np.zeros(SPAN, dtype=np.uint16)
for p in PRIMES:
    first = max(2 * p, ((X0 + p - 1) // p) * p)
    start = first - X0
    if start >= SPAN:
        continue
    view = lpf[start::p]
    view[view == 0] = p
print(f"[{time.time()-t0:6.1f}s] lpf sieve done", flush=True)

idx = np.nonzero(lpf >= LMIN)[0]
anchors = idx.astype(np.int64) + X0
avals = lpf[idx].astype(np.int64)
print(
    f"[{time.time()-t0:6.1f}s] {len(anchors)} anchors (composite, lpf>={LMIN}) "
    f"in [{X0}, {X0+SPAN})",
    flush=True,
)
gaps = np.diff(anchors)
print(
    f"anchor gaps: mean {gaps.mean():.1f}, max {gaps.max()} "
    f"(chain needs gaps comfortably below {LMIN})",
    flush=True,
)

# Greedy chain: smallest admissible next anchor.
chain = [0, 1]  # indices into anchors
while True:
    i, j = chain[-2], chain[-1]
    # find smallest k > j with anchors[k] - anchors[i] < min(avals[i], avals[k])
    k = j + 1
    found = None
    while k < len(anchors) and anchors[k] - anchors[i] < avals[i]:
        if anchors[k] - anchors[i] < avals[k]:
            found = k
            break
        k += 1
    if found is None:
        break
    chain.append(found)
a_seq = anchors[chain]
v_seq = avals[chain]
m = len(a_seq)
print(f"[{time.time()-t0:6.1f}s] greedy (C1)-chain length: {m} anchors", flush=True)

# verify (C1) explicitly
c1_ok = all(
    a_seq[n + 2] - a_seq[n] < min(v_seq[n], v_seq[n + 2]) for n in range(m - 2)
)
print(f"(C1) verified on all {m-2} triples: {c1_ok}", flush=True)

# Build + verify the L-path pointwise.
# Stage n: vertical leg x=a_n, y from a_{n+1} to a_{n+2};
#          horizontal leg y=a_{n+2}, x from a_n to a_{n+1}.
STAGES = m - 2
edges = 0
turns = 0
bad = []
composite_mask_cache = {}


def is_composite(n):
    n = int(n)
    if n in composite_mask_cache:
        return composite_mask_cache[n]
    r = lpf[n - X0] != 0 if X0 <= n < X0 + SPAN else None
    if r is None:
        r = any(n % p == 0 for p in PRIMES if p * p <= n)
    composite_mask_cache[n] = bool(r)
    return bool(r)


for n in range(STAGES):
    an, an1, an2 = int(a_seq[n]), int(a_seq[n + 1]), int(a_seq[n + 2])
    ys = np.arange(an1, an2 + 1, dtype=np.int64)
    g = np.gcd(np.full_like(ys, an), ys)
    if not np.all(g == 1):
        bad.append(("vertical", n, int(ys[np.argmax(g > 1)])))
    if not is_composite(an):
        bad.append(("vertical-composite", n, an))
    xs = np.arange(an, an1 + 1, dtype=np.int64)
    g = np.gcd(xs, np.full_like(xs, an2))
    if not np.all(g == 1):
        bad.append(("horizontal", n, int(xs[np.argmax(g > 1)])))
    if not is_composite(an2):
        bad.append(("horizontal-composite", n, an2))
    edges += (an2 - an1) + (an1 - an)
    turns += 2

print(
    f"[{time.time()-t0:6.1f}s] L-path: {STAGES} stages, {edges} unit edges, "
    f"~{turns} turns, from ({a_seq[0]},{a_seq[1]}) to "
    f"({a_seq[-2]},{a_seq[-1]}); violations: {len(bad)}",
    flush=True,
)

summary = {
    "X0": X0,
    "SPAN": SPAN,
    "LMIN": LMIN,
    "num_anchors": int(len(anchors)),
    "anchor_gap_mean": float(gaps.mean()),
    "anchor_gap_max": int(gaps.max()),
    "chain_length": int(m),
    "c1_verified": bool(c1_ok),
    "path_stages": int(STAGES),
    "path_unit_edges": int(edges),
    "path_start": [int(a_seq[0]), int(a_seq[1])],
    "path_end": [int(a_seq[-2]), int(a_seq[-1])],
    "pointwise_violations": len(bad),
    "first_anchors": [int(t) for t in a_seq[:12]],
    "first_lpfs": [int(t) for t in v_seq[:12]],
}
with open(OUT, "w") as f:
    json.dump(summary, f, indent=2)
print(f"wrote {OUT}")
