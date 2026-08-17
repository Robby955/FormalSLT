#!/usr/bin/env python3
"""Deterministic comparison for FormalSLT's empirical-Bernstein flagship.

The benchmark evaluates five raw (unclipped) population-risk ceilings on the
same balanced Bernoulli inputs.  It is numerical evidence about displayed
constants, not a proof checker or an extension of any Lean theorem.

The two all-time formulas are exact transcriptions of
``InfiniteEmpiricalBernsteinStitch.lean``.  The fixed empirical-Bernstein and
McAllester formulas are transcriptions of their fixed-sample FormalSLT
theorems.  The PAC-Bayes-kl ceiling numerically inverts the formalized Maurer
kl-form inequality; the floating-point inversion itself is not formalized.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Iterable


DEFAULT_SAMPLE_SIZES = (64, 128, 256, 512, 1024, 2048, 4096, 16384)
DEFAULT_DELTA = 0.05
DEFAULT_KL = math.log(2.0)
DEFAULT_EMPIRICAL_RISK = 0.5
DEFAULT_SCAN_MAX = 1_000_000


@dataclass(frozen=True)
class ComparisonRow:
    n: int
    empirical_risk: float
    empirical_variance_bessel: float
    kl: float
    delta: float
    floor_log2_r: int
    dyadic_epoch_floor_m: int
    fixed_grid_depth_J: int
    all_time_complexity: float
    fixed_empirical_bernstein_complexity: float
    mcallester_complexity: float
    maurer_kl_complexity: float
    all_time_epoch_ceiling: float
    all_time_clean_ceiling: float
    fixed_empirical_bernstein_ceiling: float
    mcallester_hoeffding_ceiling: float
    pac_bayes_kl_ceiling: float


@dataclass(frozen=True)
class NonvacuityResult:
    name: str
    first_even_n_below_one: int | None
    remains_below_one_through_scan: bool
    basis: str


def floor_log2(n: int) -> int:
    """Return ``floor(log2(n))`` for positive integer ``n``."""
    if n <= 0:
        raise ValueError("n must be positive")
    return n.bit_length() - 1


def ceil_log2(n: int) -> int:
    """Return ``ceil(log2(n))`` for positive integer ``n``."""
    if n <= 0:
        raise ValueError("n must be positive")
    return (n - 1).bit_length()


def balanced_bessel_variance(n: int) -> float:
    """Bessel variance of an even sample with half zeros and half ones."""
    if n < 2 or n % 2 != 0:
        raise ValueError("the balanced witness requires an even n >= 2")
    return n / (4.0 * (n - 1))


def all_time_complexity(n: int, kl: float, delta: float) -> float:
    r = floor_log2(n)
    return kl + math.log(r * (r + 1) ** 2 / delta)


def fixed_empirical_bernstein_complexity(
    n: int,
    kl: float,
    delta: float,
) -> float:
    grid_depth = ceil_log2(n)
    return kl + math.log((grid_depth + 1) / delta)


def all_time_epoch_ceiling(
    n: int,
    empirical_risk: float,
    empirical_variance: float,
    kl: float,
    delta: float,
) -> float:
    """Sharper stitched theorem with the lower dyadic epoch denominator."""
    complexity = all_time_complexity(n, kl, delta)
    epoch_floor = 1 << floor_log2(n)
    return (
        empirical_risk
        + 1.25 * math.sqrt(2.0 * empirical_variance * complexity / epoch_floor)
        + 2.5 * complexity / epoch_floor
    )


def all_time_clean_ceiling(
    n: int,
    empirical_risk: float,
    empirical_variance: float,
    kl: float,
    delta: float,
) -> float:
    """Researcher-facing stitched theorem with denominator ``n``."""
    complexity = all_time_complexity(n, kl, delta)
    return (
        empirical_risk
        + 2.5 * math.sqrt(empirical_variance * complexity / n)
        + 5.0 * complexity / n
    )


def fixed_empirical_bernstein_ceiling(
    n: int,
    empirical_risk: float,
    empirical_variance: float,
    kl: float,
    delta: float,
) -> float:
    complexity = fixed_empirical_bernstein_complexity(n, kl, delta)
    return (
        empirical_risk
        + 1.25 * math.sqrt(2.0 * empirical_variance * complexity / n)
        + 2.5 * complexity / n
    )


def mcallester_hoeffding_ceiling(
    n: int,
    empirical_risk: float,
    kl: float,
    delta: float,
) -> float:
    complexity = kl + math.log(1.0 / delta)
    return empirical_risk + math.sqrt(complexity / (2.0 * n))


def binary_kl(q: float, p: float) -> float:
    """Bernoulli KL ``kl(q || p)`` with endpoint conventions."""
    if not (0.0 <= q <= 1.0 and 0.0 <= p <= 1.0):
        raise ValueError("q and p must lie in [0, 1]")
    if q == 0.0:
        return math.inf if p == 1.0 else -math.log1p(-p)
    if q == 1.0:
        return math.inf if p == 0.0 else -math.log(p)
    if p == 0.0 or p == 1.0:
        return math.inf
    return q * math.log(q / p) + (1.0 - q) * math.log(
        (1.0 - q) / (1.0 - p)
    )


def pac_bayes_kl_upper_inverse(q: float, complexity: float) -> float:
    """Numerically invert ``kl(q || p) <= complexity`` for ``p >= q``.

    Bisection maintains a lower feasible endpoint and an upper infeasible
    endpoint.  Returning the upper endpoint makes the floating-point display
    conservative up to rounding.
    """
    if not (0.0 <= q <= 1.0):
        raise ValueError("q must lie in [0, 1]")
    if not math.isfinite(complexity) or complexity < 0.0:
        raise ValueError("complexity must be finite and nonnegative")
    if q == 1.0:
        return 1.0
    if q == 0.0:
        return -math.expm1(-complexity)

    low = q
    high = 1.0
    for _ in range(80):
        midpoint = (low + high) / 2.0
        if binary_kl(q, midpoint) <= complexity:
            low = midpoint
        else:
            high = midpoint
    return high


def pac_bayes_kl_ceiling(
    n: int,
    empirical_risk: float,
    kl: float,
    delta: float,
) -> float:
    complexity = (
        kl + math.log(2.0 * math.sqrt(n) / delta)
    ) / n
    return pac_bayes_kl_upper_inverse(empirical_risk, complexity)


def validate_inputs(
    sample_sizes: Iterable[int],
    empirical_risk: float,
    kl: float,
    delta: float,
) -> tuple[int, ...]:
    sizes = tuple(sample_sizes)
    if not sizes:
        raise ValueError("at least one sample size is required")
    if any(n < 2 or n % 2 != 0 for n in sizes):
        raise ValueError("all sample sizes must be even integers >= 2")
    if not (0.0 <= empirical_risk <= 1.0):
        raise ValueError("empirical risk must lie in [0, 1]")
    if not math.isfinite(kl) or kl < 0.0:
        raise ValueError("KL must be finite and nonnegative")
    if not (0.0 < delta < 1.0):
        raise ValueError("delta must lie in (0, 1)")
    return sizes


def comparison_row(
    n: int,
    empirical_risk: float,
    kl: float,
    delta: float,
) -> ComparisonRow:
    variance = balanced_bessel_variance(n)
    all_complexity = all_time_complexity(n, kl, delta)
    fixed_complexity = fixed_empirical_bernstein_complexity(n, kl, delta)
    mcallester_complexity = kl + math.log(1.0 / delta)
    maurer_complexity = (
        kl + math.log(2.0 * math.sqrt(n) / delta)
    ) / n
    return ComparisonRow(
        n=n,
        empirical_risk=empirical_risk,
        empirical_variance_bessel=variance,
        kl=kl,
        delta=delta,
        floor_log2_r=floor_log2(n),
        dyadic_epoch_floor_m=1 << floor_log2(n),
        fixed_grid_depth_J=ceil_log2(n),
        all_time_complexity=all_complexity,
        fixed_empirical_bernstein_complexity=fixed_complexity,
        mcallester_complexity=mcallester_complexity,
        maurer_kl_complexity=maurer_complexity,
        all_time_epoch_ceiling=all_time_epoch_ceiling(
            n, empirical_risk, variance, kl, delta
        ),
        all_time_clean_ceiling=all_time_clean_ceiling(
            n, empirical_risk, variance, kl, delta
        ),
        fixed_empirical_bernstein_ceiling=(
            fixed_empirical_bernstein_ceiling(
                n, empirical_risk, variance, kl, delta
            )
        ),
        mcallester_hoeffding_ceiling=mcallester_hoeffding_ceiling(
            n, empirical_risk, kl, delta
        ),
        pac_bayes_kl_ceiling=pac_bayes_kl_ceiling(
            n, empirical_risk, kl, delta
        ),
    )


def scan_nonvacuity(
    *,
    empirical_risk: float,
    kl: float,
    delta: float,
    scan_max: int,
) -> list[NonvacuityResult]:
    if scan_max < 2:
        raise ValueError("scan-max must be at least 2")

    def with_variance(
        formula: Callable[[int, float, float, float, float], float]
    ) -> Callable[[int], float]:
        return lambda n: formula(
            n,
            empirical_risk,
            balanced_bessel_variance(n),
            kl,
            delta,
        )

    scanned_formulas: tuple[tuple[str, Callable[[int], float]], ...] = (
        ("all-time exact epoch", with_variance(all_time_epoch_ceiling)),
        ("all-time clean n-form", with_variance(all_time_clean_ceiling)),
        (
            "fixed empirical-Bernstein",
            with_variance(fixed_empirical_bernstein_ceiling),
        ),
        (
            "McAllester/Hoeffding",
            lambda n: mcallester_hoeffding_ceiling(
                n, empirical_risk, kl, delta
            ),
        ),
    )

    results = []
    for name, formula in scanned_formulas:
        first = None
        returned_to_vacuous = False
        for n in range(2, scan_max + 1, 2):
            below_one = formula(n) < 1.0
            if below_one and first is None:
                first = n
            elif first is not None and not below_one:
                returned_to_vacuous = True
        results.append(
            NonvacuityResult(
                name=name,
                first_even_n_below_one=first,
                remains_below_one_through_scan=(
                    first is not None and not returned_to_vacuous
                ),
                basis=f"every even n <= {scan_max}",
            )
        )

    # For finite complexity, the upper binary-kl inverse is strictly below one
    # whenever q < 1.  Avoid half a million redundant bisections in the default
    # run; one inversion at n = 2 is still exercised here and in self_test().
    pac_kl_at_two = pac_bayes_kl_ceiling(2, empirical_risk, kl, delta)
    pac_kl_nonvacuous = empirical_risk < 1.0 and pac_kl_at_two < 1.0
    results.append(
        NonvacuityResult(
            name="PAC-Bayes-kl",
            first_even_n_below_one=2 if pac_kl_nonvacuous else None,
            remains_below_one_through_scan=pac_kl_nonvacuous,
            basis="inverse endpoint (checked at n = 2)",
        )
    )
    return results


def self_test() -> None:
    assert floor_log2(2) == 1
    assert floor_log2(3) == 1
    assert floor_log2(4) == 2
    assert ceil_log2(2) == 1
    assert ceil_log2(3) == 2
    assert ceil_log2(4) == 2
    assert abs(balanced_bessel_variance(64) - 16.0 / 63.0) < 1e-15

    row64 = comparison_row(
        64,
        DEFAULT_EMPIRICAL_RISK,
        DEFAULT_KL,
        DEFAULT_DELTA,
    )
    # Matches the formula used by the checked balanced-64 Lean receipt.
    assert abs(row64.fixed_empirical_bernstein_ceiling - 0.9844493993) < 1e-9
    assert row64.fixed_empirical_bernstein_ceiling < 0.99
    assert row64.all_time_epoch_ceiling <= row64.all_time_clean_ceiling

    for q, complexity in ((0.0, 0.2), (0.2, 0.01), (0.5, 0.1), (0.9, 1.0)):
        upper = pac_bayes_kl_upper_inverse(q, complexity)
        assert q <= upper <= 1.0
        assert abs(binary_kl(q, upper) - complexity) < 1e-10


def format_number(value: float) -> str:
    return f"{value:.6f}"


def render_markdown(
    rows: list[ComparisonRow],
    nonvacuity: list[NonvacuityResult],
    scan_max: int,
) -> str:
    first = rows[0]
    lines = [
        "# Empirical-Bernstein flagship numerical comparison",
        "",
        "Generated by `python3 benchmark/empirical_bernstein_flagship.py`.",
        "The values are raw, unclipped risk ceilings. This is deterministic",
        "floating-point evidence about constants, not a Lean proof check.",
        "",
        "## Common input",
        "",
        "Every row uses a balanced even Bernoulli sample, a point posterior",
        "against a fair two-point full-support prior, the Boolean match loss,",
        "and the same confidence level. Observations are finite iid and losses",
        "lie in `[0,1]`:",
        "",
        f"- empirical risk `Rhat = {first.empirical_risk:.1f}`;",
        "- Bessel empirical variance `Vhat = n / (4(n-1))`;",
        f"- `KL(rho || prior) = log 2 = {first.kl:.6f}`;",
        f"- `delta = {first.delta:.2f}`;",
        "- the scenario's population risk is `R = 0.5` (not used to compute",
        "  the ceilings).",
        "",
        "At `n = 64`, these are exactly the statistics in",
        "`CheckFiniteEmpiricalBernsteinSqrt.lean`. Only that fixed-sample row",
        "is tied to the checked balanced-path good-event membership receipt.",
        "The all-time rows evaluate the stitched boundary on the same summary",
        "statistics; they do not certify that a particular balanced infinite",
        "path lies outside the stitched exceptional event.",
        "",
        "## Formulas",
        "",
        "Let `r = floor(log2 n)`, `m = 2^r`, `J = ceil(log2 n)`,",
        "`L_inf = KL + log(r(r+1)^2/delta)`, and",
        "`L_fix = KL + log((J+1)/delta)`.",
        "",
        "- All-time exact epoch:",
        "  `Rhat + (5/4)sqrt(2 Vhat L_inf/m) + (5/2)L_inf/m`.",
        "- All-time clean n-form:",
        "  `Rhat + (5/2)sqrt(Vhat L_inf/n) + 5 L_inf/n`.",
        "- Fixed FormalSLT empirical-Bernstein:",
        "  `Rhat + (5/4)sqrt(2 Vhat L_fix/n) + (5/2)L_fix/n`.",
        "- McAllester/Hoeffding fixed-budget display:",
        "  `Rhat + sqrt((KL + log(1/delta))/(2n))`.",
        "- PAC-Bayes-kl (Maurer/Seeger): the largest `u in [Rhat,1]`",
        "  satisfying `kl(Rhat || u) <= (KL + log(2 sqrt(n)/delta))/n`,",
        "  obtained by deterministic bisection.",
        "",
        "## Raw ceilings",
        "",
        "| n | Vhat | all-time epoch | all-time clean | fixed EB | McAllester | PAC-Bayes-kl |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    str(row.n),
                    format_number(row.empirical_variance_bessel),
                    format_number(row.all_time_epoch_ceiling),
                    format_number(row.all_time_clean_ceiling),
                    format_number(row.fixed_empirical_bernstein_ceiling),
                    format_number(row.mcallester_hoeffding_ceiling),
                    format_number(row.pac_bayes_kl_ceiling),
                )
            )
            + " |"
        )

    lines.extend(
        [
            "",
            "A ceiling below `1` is nonvacuous relative to the `[0,1]` loss",
            "range. Lower numbers are tighter on this input, but the coverage",
            "regimes differ.",
            "",
            "## Deterministic nonvacuity scan",
            "",
            "For the first four formulas, the script scanned every even `n`",
            f"from `2` through `{scan_max:,}`. The PAC-Bayes-kl row uses the",
            "fact that its finite-complexity upper inverse is below one when",
            "`Rhat < 1`, with the numerical inversion checked at `n = 2`.",
            "The first raw ceiling below one was:",
            "",
            "| formula | first even n < 1 | stayed < 1 | basis |",
            "|---|---:|:---:|---|",
        ]
    )
    for result in nonvacuity:
        first_n = (
            str(result.first_even_n_below_one)
            if result.first_even_n_below_one is not None
            else "none"
        )
        stayed = "yes" if result.remains_below_one_through_scan else "no"
        lines.append(
            f"| {result.name} | {first_n} | {stayed} | {result.basis} |"
        )

    lines.extend(
        [
            "",
            "This finite scan is not a monotonicity proof. In particular, the",
            "all-time complexity changes at dyadic boundaries.",
            "",
            "## Coverage and interpretation",
            "",
            "- The two stitched bounds share one exceptional event of mass at",
            "  most `delta` across every `n >= 2` and every finite posterior",
            "  (`exists_infiniteEmpiricalBernsteinReverseSqrt_event` and",
            "  `exists_infiniteEmpiricalBernstein_event`). Their checked scope",
            "  here is a finite observation space, finite hypothesis class,",
            "  fixed full-support prior, iid stream, and `[0,1]` losses.",
            "- The fixed empirical-Bernstein bound has a separate event for one",
            "  fixed `n`; it is simultaneous over finite posteriors at that `n`",
            "  (`finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem`).",
            "- The McAllester number uses one predeclared fixed-sample complexity",
            "  budget (`finiteMcAllesterBoundedComplexity_badEventMass_le_delta`).",
            "  It does not pay for all-time validity or empirical variance.",
            "- The PAC-Bayes-kl number is a fixed-sample Bernoulli-kl comparator.",
            "  The inequality is `maurer_pacbayes_kl_bound`; its bisection",
            "  implementation is tested numerically but not checked by Lean.",
            "- The benchmark makes no novelty, optimality, or empirical-coverage",
            "  claim. A smaller fixed-sample baseline does not dominate a theorem",
            "  with simultaneous all-time coverage.",
            "",
        ]
    )
    return "\n".join(lines)


def write_csv(path: Path, rows: list[ComparisonRow]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(asdict(rows[0]).keys()),
            lineterminator="\n",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def parse_sample_sizes(raw: str) -> tuple[int, ...]:
    try:
        return tuple(int(item.strip()) for item in raw.split(",") if item.strip())
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            "sample sizes must be comma-separated integers"
        ) from error


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sample-sizes",
        type=parse_sample_sizes,
        default=DEFAULT_SAMPLE_SIZES,
        help="comma-separated even sample sizes (default: %(default)s)",
    )
    parser.add_argument("--scan-max", type=int, default=DEFAULT_SCAN_MAX)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "output",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run deterministic formula and solver checks, then exit",
    )
    parser.add_argument(
        "--no-write",
        action="store_true",
        help="print the Markdown report without writing output files",
    )
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    self_test()
    if args.self_test:
        print("self-test: PASS")
        return

    try:
        sample_sizes = validate_inputs(
            args.sample_sizes,
            DEFAULT_EMPIRICAL_RISK,
            DEFAULT_KL,
            DEFAULT_DELTA,
        )
        if args.scan_max < 2:
            raise ValueError("scan-max must be at least 2")
    except ValueError as error:
        parser.error(str(error))
    rows = [
        comparison_row(
            n,
            DEFAULT_EMPIRICAL_RISK,
            DEFAULT_KL,
            DEFAULT_DELTA,
        )
        for n in sample_sizes
    ]
    nonvacuity = scan_nonvacuity(
        empirical_risk=DEFAULT_EMPIRICAL_RISK,
        kl=DEFAULT_KL,
        delta=DEFAULT_DELTA,
        scan_max=args.scan_max,
    )
    report = render_markdown(rows, nonvacuity, args.scan_max)

    if args.no_write:
        print(report)
        return

    output_dir = args.output_dir
    csv_path = output_dir / "empirical_bernstein_flagship.csv"
    markdown_path = output_dir / "empirical_bernstein_flagship.md"
    write_csv(csv_path, rows)
    output_dir.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(report, encoding="utf-8")
    print(f"wrote {csv_path}")
    print(f"wrote {markdown_path}")


if __name__ == "__main__":
    main()
