#!/usr/bin/env python3
"""Sweep harness for generated PAC-Bayes certificates."""

from __future__ import annotations

import csv
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from compile import REPO_ROOT, axiom_output_clean, load_spec

RESULTS_DIR = REPO_ROOT / "compiler" / "results"
COMPILER = REPO_ROOT / "compiler" / "compile.py"


@dataclass(frozen=True)
class SweepRow:
    spec_id: str
    H: int
    n: int
    B: str
    delta: str
    KL: str
    computed_bound: str
    lake_build_ok: int
    axiom_clean: int
    wallclock_seconds: str


def run_command(args: list[str], *, timeout: int = 900) -> tuple[bool, str, float]:
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    start = time.perf_counter()
    proc = subprocess.run(
        args,
        cwd=REPO_ROOT,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    elapsed = time.perf_counter() - start
    return proc.returncode == 0, proc.stdout + proc.stderr, elapsed


def run_spec(spec_path: Path) -> SweepRow:
    spec = load_spec(spec_path)
    compile_ok, compile_out, _compile_seconds = run_command(
        [sys.executable, str(COMPILER), "--spec", str(spec_path)],
        timeout=300,
    )
    if not compile_ok:
        print(compile_out)
        return SweepRow(
            spec_id=spec.spec_id,
            H=spec.H,
            n=spec.n,
            B=str(spec.B),
            delta=str(spec.delta),
            KL=f"{spec.kl:.12g}",
            computed_bound=f"{spec.computed_bound:.12g}",
            lake_build_ok=0,
            axiom_clean=0,
            wallclock_seconds="0.000",
        )

    lake_ok, lake_out, lake_seconds = run_command(
        ["lake", "build", spec.module],
        timeout=900,
    )
    print(lake_out)
    axiom_ok = False
    if lake_ok:
        axiom_run_ok, axiom_out, _axiom_seconds = run_command(
            ["lake", "env", "lean", str(spec.check_path)],
            timeout=300,
        )
        print(axiom_out)
        axiom_ok = axiom_run_ok and axiom_output_clean(axiom_out)

    return SweepRow(
        spec_id=spec.spec_id,
        H=spec.H,
        n=spec.n,
        B=str(spec.B),
        delta=str(spec.delta),
        KL=f"{spec.kl:.12g}",
        computed_bound=f"{spec.computed_bound:.12g}",
        lake_build_ok=1 if lake_ok else 0,
        axiom_clean=1 if axiom_ok else 0,
        wallclock_seconds=f"{lake_seconds:.3f}",
    )


def run_sweep(spec_dir: Path) -> Path:
    spec_paths = sorted(Path(spec_dir).glob("*.json"))
    if not spec_paths:
        raise FileNotFoundError(f"no JSON specs found in {spec_dir}")

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = time.strftime("%Y%m%d-%H%M%S")
    csv_path = RESULTS_DIR / f"sweep-{timestamp}.csv"

    rows = [run_spec(path) for path in spec_paths]
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            lineterminator="\n",
            fieldnames=[
                "spec_id",
                "H",
                "n",
                "B",
                "delta",
                "KL",
                "computed_bound",
                "lake_build_ok",
                "axiom_clean",
                "wallclock_seconds",
            ],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)

    failures = [row.spec_id for row in rows if not (row.lake_build_ok and row.axiom_clean)]
    print(f"[sweep] wrote {csv_path.relative_to(REPO_ROOT)}")
    if failures:
        raise SystemExit(f"[sweep] failed specs: {', '.join(failures)}")
    return csv_path


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: python3 compiler/sweep_runner.py compiler/specs/", file=sys.stderr)
        return 2
    run_sweep(Path(sys.argv[1]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
