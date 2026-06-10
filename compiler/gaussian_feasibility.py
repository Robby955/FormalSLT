#!/usr/bin/env python3
"""Numeric feasibility study for a Gaussian-posterior PAC-Bayes certificate.

This script contains no Lean and proves nothing. It mirrors the checked
closed-form KL definitions from ``FormalSLT/PACBayes/GaussianKL.lean`` and the
McAllester penalty from ``FormalSLT/PACBayes/Compiler.lean`` so that the
continuous-posterior lane (Route B) can pick a concrete nonvacuous numeric
instance *before* any Lean theorem is written. The Lean-side soundness story
is unchanged: a future certificate is checked by the Lean kernel, not by this
script.

Python mirror of the Lean definitions:

* ``spherical_gaussian_kl`` mirrors ``sphericalGaussianKLClosedForm``
  (GaussianKL.lean): ``(d*(s/t - 1 + log(t/s)) + dist2/t) / 2`` with
  ``s = posterior variance``, ``t = prior variance``,
  ``dist2 = squared mean distance``.
* ``diagonal_gaussian_kl`` mirrors ``diagonalGaussianKLClosedForm``.
* ``mcallester_penalty`` mirrors ``mcAllesterPenalty n C = sqrt(C / (2n))``
  with ``C >= KL + log(1/delta)``.

Run directly to print the feasibility sweep and a recommended instance:

    python3 compiler/gaussian_feasibility.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass


def diagonal_gaussian_kl(
    posterior_mean: list[float],
    posterior_variance: list[float],
    prior_mean: list[float],
    prior_variance: list[float],
) -> float:
    """Coordinatewise diagonal Gaussian KL, posterior first, prior second."""
    if not (
        len(posterior_mean)
        == len(posterior_variance)
        == len(prior_mean)
        == len(prior_variance)
    ):
        raise ValueError("dimension mismatch")
    total = 0.0
    for pm, pv, qm, qv in zip(
        posterior_mean, posterior_variance, prior_mean, prior_variance, strict=True
    ):
        if pv <= 0 or qv <= 0:
            raise ValueError("variances must be positive")
        total += (pv / qv + (pm - qm) ** 2 / qv - 1 + math.log(qv / pv)) / 2
    return total


def spherical_gaussian_kl(
    d: int,
    posterior_variance: float,
    prior_variance: float,
    squared_mean_distance: float,
) -> float:
    """Spherical Gaussian KL via the Lean closed form."""
    if posterior_variance <= 0 or prior_variance <= 0:
        raise ValueError("variances must be positive")
    if squared_mean_distance < 0:
        raise ValueError("squared mean distance must be nonnegative")
    return (
        d
        * (
            posterior_variance / prior_variance
            - 1
            + math.log(prior_variance / posterior_variance)
        )
        + squared_mean_distance / prior_variance
    ) / 2


def mcallester_penalty(n: int, complexity_bound: float) -> float:
    """McAllester square-root penalty ``sqrt(C / (2n))`` for unit-width loss."""
    if n <= 0:
        raise ValueError("sample size must be positive")
    if complexity_bound < 0:
        raise ValueError("complexity bound must be nonnegative")
    return math.sqrt(complexity_bound / (2 * n))


@dataclass(frozen=True)
class GaussianInstance:
    """One candidate Gaussian-posterior certificate instance."""

    label: str
    d: int
    n: int
    delta: float
    posterior_variance: float
    prior_variance: float
    squared_mean_distance: float
    empirical_risk: float

    @property
    def kl(self) -> float:
        return spherical_gaussian_kl(
            self.d,
            self.posterior_variance,
            self.prior_variance,
            self.squared_mean_distance,
        )

    @property
    def complexity(self) -> float:
        return self.kl + math.log(1.0 / self.delta)

    @property
    def penalty(self) -> float:
        return mcallester_penalty(self.n, self.complexity)

    @property
    def risk_bound(self) -> float:
        return self.empirical_risk + self.penalty

    @property
    def nonvacuous(self) -> bool:
        return self.risk_bound < 1.0


def self_check() -> None:
    """Cross-check the mirrors against the Lean closed-form special cases."""
    # sphericalGaussianKL_equalVariance_eq: equal variance collapses to
    # squaredMeanDistance / (2 * variance).
    for d in (1, 5, 100):
        for var in (0.5, 1.0, 4.0):
            for dist2 in (0.0, 1.0, 7.25):
                got = spherical_gaussian_kl(d, var, var, dist2)
                want = dist2 / (2 * var)
                assert math.isclose(got, want, rel_tol=1e-12, abs_tol=1e-12), (
                    d,
                    var,
                    dist2,
                    got,
                    want,
                )
    # Identical posterior and prior gives KL = 0.
    assert spherical_gaussian_kl(10, 1.0, 1.0, 0.0) == 0.0
    # Spherical agrees with the diagonal mirror on a concrete instance.
    d = 4
    pm = [0.3, -0.2, 0.5, 0.0]
    dist2 = sum(x * x for x in pm)
    got_diag = diagonal_gaussian_kl(pm, [0.25] * d, [0.0] * d, [1.0] * d)
    got_sph = spherical_gaussian_kl(d, 0.25, 1.0, dist2)
    assert math.isclose(got_diag, got_sph, rel_tol=1e-12), (got_diag, got_sph)
    # KL nonnegativity on a small grid (Gibbs inequality sanity check).
    for s in (0.1, 0.5, 1.0, 2.0, 10.0):
        for t in (0.1, 0.5, 1.0, 2.0, 10.0):
            assert spherical_gaussian_kl(3, s, t, 0.0) >= -1e-12, (s, t)


def sweep() -> list[GaussianInstance]:
    """Candidate regimes for the first verified Gaussian certificate."""
    instances = [
        # Equal-variance posterior centered near the prior: the KL is just
        # dist2/(2 tau^2). Small d-independence makes this the cleanest
        # first Lean instance (matches sphericalGaussianKL_equalVariance_eq).
        GaussianInstance(
            label="equal-variance, small shift",
            d=100,
            n=10000,
            delta=0.05,
            posterior_variance=1.0,
            prior_variance=1.0,
            squared_mean_distance=4.0,
            empirical_risk=0.10,
        ),
        # Shrunk posterior variance: pays d * (s/t - 1 + log(t/s)) / 2.
        GaussianInstance(
            label="shrunk variance, d=10",
            d=10,
            n=10000,
            delta=0.05,
            posterior_variance=0.5,
            prior_variance=1.0,
            squared_mean_distance=2.0,
            empirical_risk=0.10,
        ),
        # Higher-dimensional shrunk posterior; KL grows linearly in d.
        GaussianInstance(
            label="shrunk variance, d=100",
            d=100,
            n=10000,
            delta=0.05,
            posterior_variance=0.5,
            prior_variance=1.0,
            squared_mean_distance=2.0,
            empirical_risk=0.10,
        ),
        # Stress case: large dimension at moderate n; expected vacuous.
        GaussianInstance(
            label="large d, moderate n (stress)",
            d=10000,
            n=10000,
            delta=0.05,
            posterior_variance=0.5,
            prior_variance=1.0,
            squared_mean_distance=10.0,
            empirical_risk=0.10,
        ),
        # Dziugaite-Roy-like ballpark: big KL absorbed by big n.
        GaussianInstance(
            label="large KL, large n",
            d=1000,
            n=60000,
            delta=0.025,
            posterior_variance=0.9,
            prior_variance=1.0,
            squared_mean_distance=100.0,
            empirical_risk=0.05,
        ),
    ]
    return instances


def recommended_instance() -> GaussianInstance:
    """The instance Route B PR4 should target first.

    Equal-variance spherical Gaussians make the Lean-side KL collapse to
    ``squaredMeanDistance / (2 * variance)`` via the already-checked
    ``sphericalGaussianKL_equalVariance_eq``, so the first verified numeric
    certificate needs no log-term rational approximation at all when the
    squared mean distance and variance are rational.
    """
    return GaussianInstance(
        label="PR4 target: equal-variance rational instance",
        d=100,
        n=10000,
        delta=0.05,
        posterior_variance=1.0,
        prior_variance=1.0,
        squared_mean_distance=4.0,  # KL = 2 exactly
        empirical_risk=0.10,
    )


def main() -> int:
    self_check()
    print("self-check: OK (mirrors match Lean closed-form special cases)\n")
    header = (
        f"{'label':38} {'d':>6} {'n':>7} {'KL':>10} {'C':>10} "
        f"{'penalty':>9} {'bound':>8} {'nonvac':>6}"
    )
    print(header)
    print("-" * len(header))
    for inst in sweep():
        print(
            f"{inst.label:38} {inst.d:>6} {inst.n:>7} {inst.kl:>10.4f} "
            f"{inst.complexity:>10.4f} {inst.penalty:>9.4f} "
            f"{inst.risk_bound:>8.4f} {str(inst.nonvacuous):>6}"
        )
    rec = recommended_instance()
    print("\nRecommended first verified instance (Route B PR4):")
    print(f"  {rec.label}")
    print(f"  d={rec.d}, n={rec.n}, delta={rec.delta}")
    print(
        f"  posterior=N(mu, {rec.posterior_variance} I), "
        f"prior=N(0, {rec.prior_variance} I), ||mu||^2={rec.squared_mean_distance}"
    )
    print(f"  KL = {rec.kl} (exact rational: dist2/(2 var) = 2)")
    print(f"  complexity C = KL + log(1/delta) = {rec.complexity:.6f}")
    print(f"  McAllester penalty = {rec.penalty:.6f}")
    print(f"  risk bound = {rec.empirical_risk} + penalty = {rec.risk_bound:.6f}")
    print(f"  nonvacuous: {rec.nonvacuous}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
