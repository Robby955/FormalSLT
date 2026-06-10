"""Soundness regression tests for the KL upper-bound check in compile.normalize_spec.

A spec may supply a `KL` (or `kl`) field as a *declared upper bound* on the
true KL divergence between the posterior and prior. If the supplied value is
strictly below the actual `kl_divergence(posterior, prior)`, the compiler
must reject the spec rather than emit a Lean certificate that would
silently inherit a tighter-than-true complexity bound.

These tests exercise the regression for PR #10 review finding P1.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from compile import kl_divergence, normalize_spec  # noqa: E402


def _delta_vs_uniform_spec(kl_value):
    return {
        "spec_id": "test_delta_vs_uniform",
        "H": 2,
        "n": 100,
        "B": "1",
        "delta": "0.05",
        "KL": kl_value,
        "prior": {"kind": "uniform"},
        "posterior": {"kind": "delta", "index": 0},
    }


def test_supplied_kl_below_actual_raises():
    """Delta posterior on a uniform prior has KL = log 2.

    Declaring `KL: 0` claims a strictly tighter bound and must be rejected.
    """
    spec = _delta_vs_uniform_spec(0)
    with pytest.raises(ValueError, match="KL.*upper-bound"):
        normalize_spec(spec)


def test_supplied_kl_equal_to_actual_accepted():
    """An exact KL match (within tolerance) is a valid upper bound."""
    spec = _delta_vs_uniform_spec(math.log(2))
    result = normalize_spec(spec)
    assert result.kl == pytest.approx(math.log(2), rel=1e-9)


def test_supplied_kl_above_actual_accepted():
    """A loose upper bound is allowed; the bound used is the supplied value."""
    spec = _delta_vs_uniform_spec(1.0)
    result = normalize_spec(spec)
    assert result.kl == pytest.approx(1.0, rel=1e-12)


def test_lowercase_kl_field_also_checked():
    """Lowercase `kl` triggers the same upper-bound check."""
    spec = _delta_vs_uniform_spec(0)
    spec["kl"] = spec.pop("KL")
    with pytest.raises(ValueError, match="KL.*upper-bound"):
        normalize_spec(spec)


def test_kl_divergence_matches_lean_convention():
    """Python `kl_divergence` mirrors Lean `klDiv` from FormalSLT/PACBayesKL.lean:61.

    Both compute ``sum_i rho_i * log(rho_i / pi_i)`` with `0 * log(0) = 0`.
    """
    from fractions import Fraction

    posterior = [Fraction(1, 1), Fraction(0, 1)]
    prior = [Fraction(1, 2), Fraction(1, 2)]
    assert kl_divergence(posterior, prior) == pytest.approx(math.log(2))
