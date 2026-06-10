"""Tests for the Gaussian-posterior feasibility mirrors.

These tests pin the Python mirrors in ``gaussian_feasibility.py`` to the
checked Lean closed forms in ``FormalSLT/PACBayes/GaussianKL.lean`` and the
McAllester penalty in ``FormalSLT/PACBayes/Compiler.lean``. They prove nothing
about Lean; they guard the numeric planning layer for the Route B lane.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from gaussian_feasibility import (  # noqa: E402
    diagonal_gaussian_kl,
    mcallester_penalty,
    recommended_instance,
    self_check,
    spherical_gaussian_kl,
)


def test_self_check_passes():
    self_check()


def test_equal_variance_collapse():
    """Mirrors sphericalGaussianKL_equalVariance_eq: KL = dist2 / (2 var)."""
    assert spherical_gaussian_kl(100, 1.0, 1.0, 4.0) == pytest.approx(2.0)
    assert spherical_gaussian_kl(7, 0.5, 0.5, 3.0) == pytest.approx(3.0)


def test_identical_distributions_zero_kl():
    assert spherical_gaussian_kl(10, 2.0, 2.0, 0.0) == 0.0
    assert diagonal_gaussian_kl([1.0], [0.3], [1.0], [0.3]) == pytest.approx(0.0)


def test_kl_nonnegative_on_grid():
    """Gibbs inequality sanity for the mirror."""
    for s in (0.1, 1.0, 5.0):
        for t in (0.1, 1.0, 5.0):
            for dist2 in (0.0, 2.0):
                assert spherical_gaussian_kl(4, s, t, dist2) >= -1e-12


def test_mcallester_penalty_matches_lean_shape():
    """mcAllesterPenalty n C = sqrt(C / (2n))."""
    assert mcallester_penalty(10000, 5.0) == pytest.approx(math.sqrt(5.0 / 20000))


def test_penalty_rejects_bad_inputs():
    with pytest.raises(ValueError):
        mcallester_penalty(0, 1.0)
    with pytest.raises(ValueError):
        mcallester_penalty(100, -0.1)
    with pytest.raises(ValueError):
        spherical_gaussian_kl(3, 0.0, 1.0, 0.0)
    with pytest.raises(ValueError):
        spherical_gaussian_kl(3, 1.0, 1.0, -1.0)


def test_recommended_instance_is_nonvacuous():
    """The Route B PR4 target instance must stay nonvacuous and exact."""
    rec = recommended_instance()
    assert rec.kl == pytest.approx(2.0)  # 4 / (2 * 1), exact rational
    assert rec.complexity == pytest.approx(2.0 + math.log(20.0))
    assert rec.risk_bound < 0.2
    assert rec.nonvacuous


def test_complexity_budget_five_is_a_valid_ceiling():
    """The fallback rational budget C = 5 dominates 2 + log 20 (e^3 > 20)."""
    rec = recommended_instance()
    assert rec.complexity < 5.0
    assert math.exp(3.0) > 20.0
