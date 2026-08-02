#!/usr/bin/env python3
"""CPU smoke test for the continuous time-uniform PAC-Bayes bridge.

This is not a proof checker and does not validate Lean's kernel. It exercises
an exact synthetic specialization of the process-level theorem:

* hypotheses theta in R^d;
* prior P = N(0, sigma_p^2 I_d);
* fixed posterior Q = N(kappa a, sigma_q^2 I_d), ||a|| = 1;
* data Z_i ~ N(0, 1);
* loss ell(theta, z) = 1{z <= a dot theta}.

Equivalently, after U_i = Phi(Z_i), this is
ell(theta, U_i) = 1{U_i <= Phi(a dot theta)}. Therefore

  E_Q R(theta) = Phi(kappa / sqrt(1 + sigma_q^2)),
  E_Q ell(theta, z) = 1 - Phi((z - kappa) / sigma_q),

and the spherical Gaussian KL is available in closed form. For each fixed
lambda > 0, Hoeffding's lemma gives the per-hypothesis e-process

  exp(lambda * sum_i (R(theta) - ell_i(theta)) - n * lambda^2 / 8).

A finite preregistered lambda grid is combined by Bonferroni, so taking the
minimum displayed boundary over the grid remains valid. Posterior
configurations are reported separately; the script never selects a posterior
from the evaluation stream.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from statistics import NormalDist
from typing import Iterable

STD_NORMAL = NormalDist()


@dataclass(frozen=True)
class PosteriorConfig:
    name: str
    dimension: int
    sigma_prior: float
    kappa: float
    sigma_posterior: float


@dataclass
class ConfigAccumulator:
    violations: int = 0
    sum_horizon_bound: float = 0.0
    sum_horizon_gap: float = 0.0
    sum_min_margin: float = 0.0
    sum_best_bound: float = 0.0
    sum_best_n: int = 0
    nonvacuous_at_horizon: int = 0


def spherical_gaussian_kl(config: PosteriorConfig) -> float:
    """KL(N(kappa a, sigma_q^2 I) || N(0, sigma_p^2 I))."""
    d = config.dimension
    sp = config.sigma_prior
    sq = config.sigma_posterior
    ratio = (sq * sq) / (sp * sp)
    return 0.5 * (
        d * (ratio - 1.0 - math.log(ratio))
        + (config.kappa**2) / (sp * sp)
    )


def posterior_population_risk(config: PosteriorConfig) -> float:
    return STD_NORMAL.cdf(
        config.kappa / math.sqrt(1.0 + config.sigma_posterior**2)
    )


def posterior_expected_loss(config: PosteriorConfig, z: float) -> float:
    standardized = (z - config.kappa) / config.sigma_posterior
    return 1.0 - STD_NORMAL.cdf(standardized)


def wilson_interval(
    successes: int,
    trials: int,
    z_score: float = 1.959963984540054,
) -> tuple[float, float]:
    if trials <= 0:
        raise ValueError("trials must be positive")
    p = successes / trials
    z2 = z_score * z_score
    denominator = 1.0 + z2 / trials
    center = (p + z2 / (2.0 * trials)) / denominator
    radius = (
        z_score
        * math.sqrt((p * (1.0 - p) + z2 / (4.0 * trials)) / trials)
        / denominator
    )
    return max(0.0, center - radius), min(1.0, center + radius)


def penalty_schedule(
    *,
    kl: float,
    horizon: int,
    delta: float,
    lambdas: tuple[float, ...],
) -> list[float]:
    # Bonferroni across the fixed lambda grid: delta_lambda = delta / |grid|.
    log_term = kl + math.log(len(lambdas) / delta)
    return [
        0.0,
        *[
            min(log_term / (lam * n) + lam / 8.0 for lam in lambdas)
            for n in range(1, horizon + 1)
        ],
    ]


def default_configs() -> tuple[PosteriorConfig, ...]:
    return (
        PosteriorConfig("matched", 32, 1.0, 0.0, 1.0),
        PosteriorConfig("mean_shift", 32, 1.0, 0.5, 1.0),
        PosteriorConfig("mild_contraction", 32, 1.0, 0.25, 0.9),
        PosteriorConfig("low_dim_contraction", 4, 1.0, 0.5, 0.75),
    )


def self_test() -> None:
    matched = PosteriorConfig("matched", 32, 1.0, 0.0, 1.0)
    assert abs(spherical_gaussian_kl(matched)) < 1e-12
    assert abs(posterior_population_risk(matched) - 0.5) < 1e-12
    for z in (-2.0, 0.0, 1.5):
        expected = 1.0 - STD_NORMAL.cdf(z)
        assert abs(posterior_expected_loss(matched, z) - expected) < 1e-12
    shifted = PosteriorConfig("shifted", 7, 2.0, 0.3, 2.0)
    expected_kl = 0.5 * (0.3**2) / (2.0**2)
    assert abs(spherical_gaussian_kl(shifted) - expected_kl) < 1e-12
    penalties = penalty_schedule(
        kl=0.0,
        horizon=10,
        delta=0.05,
        lambdas=(0.1, 0.2),
    )
    assert len(penalties) == 11
    assert all(math.isfinite(x) and x > 0.0 for x in penalties[1:])


def run_experiment(
    *,
    configs: tuple[PosteriorConfig, ...],
    replicates: int,
    horizon: int,
    delta: float,
    seed: int,
    lambdas: tuple[float, ...],
) -> dict:
    if replicates <= 0 or horizon <= 0:
        raise ValueError("replicates and horizon must be positive")
    if not (0.0 < delta < 1.0):
        raise ValueError("delta must lie in (0, 1)")
    if not lambdas or any(
        lam <= 0.0 or not math.isfinite(lam) for lam in lambdas
    ):
        raise ValueError("all lambda values must be finite and positive")
    if any(
        config.dimension <= 0
        or config.sigma_prior <= 0.0
        or config.sigma_posterior <= 0.0
        for config in configs
    ):
        raise ValueError("dimensions and Gaussian scales must be positive")

    rng = random.Random(seed)
    accumulators = {
        config.name: ConfigAccumulator() for config in configs
    }
    precomputed = {}
    for config in configs:
        kl = spherical_gaussian_kl(config)
        precomputed[config.name] = {
            "kl": kl,
            "risk": posterior_population_risk(config),
            "penalty": penalty_schedule(
                kl=kl,
                horizon=horizon,
                delta=delta,
                lambdas=lambdas,
            ),
        }

    for _replicate in range(replicates):
        stream = [rng.gauss(0.0, 1.0) for _ in range(horizon)]
        for config in configs:
            values = precomputed[config.name]
            true_risk = values["risk"]
            penalties = values["penalty"]
            cumulative_loss = 0.0
            violated = False
            min_margin = math.inf
            best_bound = math.inf
            best_n = 0
            horizon_bound = math.nan

            for n, z in enumerate(stream, start=1):
                cumulative_loss += posterior_expected_loss(config, z)
                empirical_risk = cumulative_loss / n
                bound = empirical_risk + penalties[n]
                margin = bound - true_risk
                if margin < 0.0:
                    violated = True
                if margin < min_margin:
                    min_margin = margin
                if bound < best_bound:
                    best_bound = bound
                    best_n = n
                if n == horizon:
                    horizon_bound = bound

            acc = accumulators[config.name]
            acc.violations += int(violated)
            acc.sum_horizon_bound += horizon_bound
            acc.sum_horizon_gap += horizon_bound - true_risk
            acc.sum_min_margin += min_margin
            acc.sum_best_bound += best_bound
            acc.sum_best_n += best_n
            acc.nonvacuous_at_horizon += int(horizon_bound < 1.0)

    results = []
    for config in configs:
        acc = accumulators[config.name]
        values = precomputed[config.name]
        lower, upper = wilson_interval(acc.violations, replicates)
        results.append(
            {
                **asdict(config),
                "kl": values["kl"],
                "posterior_population_risk": values["risk"],
                "violations": acc.violations,
                "violation_rate": acc.violations / replicates,
                "violation_rate_wilson_95": [lower, upper],
                "mean_horizon_bound": acc.sum_horizon_bound / replicates,
                "mean_horizon_gap": acc.sum_horizon_gap / replicates,
                "mean_min_margin": acc.sum_min_margin / replicates,
                "mean_best_bound": acc.sum_best_bound / replicates,
                "mean_best_n": acc.sum_best_n / replicates,
                "nonvacuous_at_horizon_rate": (
                    acc.nonvacuous_at_horizon / replicates
                ),
            }
        )

    return {
        "schema": (
            "FormalSLT.time_uniform_continuous_pac_bayes_smoke.v1"
        ),
        "scope": {
            "claim": (
                "finite-horizon numerical smoke test of one exact Gaussian "
                "specialization"
            ),
            "nonclaims": [
                "not a Lean proof check",
                "not a proof of empirical coverage",
                "not a data-dependent-posterior theorem",
                "not a neural-network generalization theorem",
            ],
        },
        "parameters": {
            "replicates": replicates,
            "horizon": horizon,
            "delta_familywise_over_lambda_grid": delta,
            "seed": seed,
            "lambda_grid": list(lambdas),
            "posterior_configurations_are_tested_separately": True,
        },
        "results": results,
    }


def write_outputs(
    report: dict,
    output_prefix: Path,
) -> tuple[Path, Path]:
    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    json_path = output_prefix.with_suffix(".json")
    csv_path = output_prefix.with_suffix(".csv")
    json_path.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    rows = report["results"]
    fieldnames = [
        "name",
        "dimension",
        "sigma_prior",
        "kappa",
        "sigma_posterior",
        "kl",
        "posterior_population_risk",
        "violations",
        "violation_rate",
        "wilson_95_lower",
        "wilson_95_upper",
        "mean_horizon_bound",
        "mean_horizon_gap",
        "mean_min_margin",
        "mean_best_bound",
        "mean_best_n",
        "nonvacuous_at_horizon_rate",
    ]
    with csv_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            flattened = dict(row)
            interval = flattened.pop("violation_rate_wilson_95")
            flattened["wilson_95_lower"] = interval[0]
            flattened["wilson_95_upper"] = interval[1]
            writer.writerow({key: flattened[key] for key in fieldnames})
    return json_path, csv_path


def parse_lambdas(raw: str) -> tuple[float, ...]:
    values = tuple(
        float(part.strip())
        for part in raw.split(",")
        if part.strip()
    )
    if not values:
        raise argparse.ArgumentTypeError("lambda grid must be nonempty")
    return values


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replicates", type=int, default=500)
    parser.add_argument("--horizon", type=int, default=2000)
    parser.add_argument("--delta", type=float, default=0.05)
    parser.add_argument("--seed", type=int, default=20260802)
    parser.add_argument(
        "--lambdas",
        type=parse_lambdas,
        default=(0.05, 0.1, 0.2, 0.4, 0.8),
    )
    parser.add_argument(
        "--output-prefix",
        type=Path,
        default=Path(
            "benchmark/output/time_uniform_continuous_pac_bayes_smoke"
        ),
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help=(
            "run 40 replicates to horizon 250 for a fast deterministic "
            "smoke test"
        ),
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)

    self_test()
    if args.self_test:
        print("self-test: ok")
        return 0
    if args.quick:
        args.replicates = 40
        args.horizon = 250

    report = run_experiment(
        configs=default_configs(),
        replicates=args.replicates,
        horizon=args.horizon,
        delta=args.delta,
        seed=args.seed,
        lambdas=args.lambdas,
    )
    json_path, csv_path = write_outputs(report, args.output_prefix)
    print(json.dumps(report, indent=2, sort_keys=True))
    print(f"wrote {json_path}")
    print(f"wrote {csv_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
