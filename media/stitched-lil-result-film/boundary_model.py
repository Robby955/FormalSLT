"""Deterministic numerical model for the film's declared boundary illustration.

The displayed theorem is symbolic.  These constants only select one admissible
parameter triple so the animation can draw the exact fixed-tilt and stitched
boundary shapes instead of arbitrary screen-space curves.
"""

from __future__ import annotations

import math


ILLUSTRATIVE_SIGMA2 = 0.08
ILLUSTRATIVE_B = 0.25
ILLUSTRATIVE_DELTA = 0.05


def epoch_budget_value(j: int) -> float:
    if j < 0:
        raise ValueError("epoch index must be nonnegative")
    return (
        math.log(2.0 / ILLUSTRATIVE_DELTA)
        + math.log(j + 1.0)
        + math.log(j + 2.0)
    )


def selected_epoch_value(n: float) -> int:
    if not math.isfinite(n) or n < 4.0:
        raise ValueError("the stitched selector is displayed only for n >= 4")
    return max(0, math.floor(math.log(n, 4.0)) - 1)


def optimized_tilt_value(j: int) -> float:
    """The checked fixed tilt at the floor N_j = 4^(j+1)."""
    floor = float(4 ** (j + 1))
    budget = epoch_budget_value(j)
    root = math.sqrt(2.0 * budget / (ILLUSTRATIVE_SIGMA2 * floor))
    tilt = root / (1.0 + (ILLUSTRATIVE_B / 3.0) * root)
    if not 0.0 < ILLUSTRATIVE_B * tilt < 3.0:
        raise ValueError("illustrative tilt left the sub-Gamma domain")
    return tilt


def fixed_tilt_boundary_value(j: int, n: float) -> float:
    """Exact fixed-tilt mean boundary a_j + c_j/n used in the film."""
    if not math.isfinite(n) or n <= 0.0:
        raise ValueError("sample size must be positive")
    lam = optimized_tilt_value(j)
    cgf = (
        ILLUSTRATIVE_SIGMA2
        * lam
        * lam
        / (2.0 * (1.0 - ILLUSTRATIVE_B * lam / 3.0))
    )
    return cgf / lam + epoch_budget_value(j) / (n * lam)


def stitched_width_value(n: float) -> float:
    """Exact displayed W_n for the declared numerical illustration."""
    j = selected_epoch_value(n)
    budget = epoch_budget_value(j)
    return (
        2.0 * math.sqrt(2.0 * ILLUSTRATIVE_SIGMA2 * budget / n)
        + 4.0 * ILLUSTRATIVE_B * budget / (3.0 * n)
    )


def log_time_x(n: float, left: float, right: float) -> float:
    if not math.isfinite(n) or n < 4.0:
        raise ValueError("log-time plot starts at n = 4")
    coordinate = (math.log(n, 4.0) - 1.0) / 4.0
    return left + coordinate * (right - left)
