#!/usr/bin/env python3
"""Extract overview-film facts from one exact FormalSLT commit."""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


BOUND_SHA = "e18e3f52326c98c878e73557305fc9ee482f499e"
ROOT = Path(__file__).resolve().parents[2]
OUTPUT = Path(__file__).with_name("facts.json")

DECLARATIONS = [
    {
        "stage": "Exponential processes",
        "file": "FormalSLT/AnytimeValid/ForwardBesselProcess.lean",
        "name": "exists_forwardEmpiricalBernsteinLowerTiltCatalog_event",
    },
    {
        "stage": "PAC-Bayes and anytime validity",
        "file": "FormalSLT/PACBayes/TimeUniformTiltMixture.lean",
        "name": "timeUniformPACBayes_tiltMixture_allPosteriors_bound",
    },
    {
        "stage": "Adaptive trajectories",
        "file": (
            "FormalSLT/StochasticDynamics/"
            "TrajectoryEmpiricalBernsteinPACBayesCountable.lean"
        ),
        "name": (
            "exists_trajectoryCountableEmpiricalBernsteinPACBayes_"
            "allTime_vanishing_event"
        ),
    },
    {
        "stage": "Stationary empirical-catalog certification",
        "file": "FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.lean",
        "name": "exists_empiricalStationaryCatalog_event",
    },
]


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(ROOT), *args],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout


def source_at(path: str) -> str:
    return git("show", f"{BOUND_SHA}:{path}")


def require(pattern: str, text: str, label: str) -> re.Match[str]:
    match = re.search(pattern, text, flags=re.MULTILINE)
    if match is None:
        raise SystemExit(f"missing fact at {BOUND_SHA}: {label}")
    return match


def main() -> None:
    resolved = git("rev-parse", BOUND_SHA).strip()
    if resolved != BOUND_SHA:
        raise SystemExit(f"commit did not resolve exactly: {resolved}")

    for declaration in DECLARATIONS:
        source = source_at(declaration["file"])
        name = declaration["name"]
        require(
            rf"^theorem\s+{re.escape(name)}\b",
            source,
            f"theorem {name}",
        )

    readme = source_at("README.md")
    stable_topic_imports = [
        "FormalSLT.PACBayes",
        "FormalSLT.Sequential",
        "FormalSLT.StochasticDynamics",
        "FormalSLT.VC",
    ]
    for topic in stable_topic_imports:
        require(rf"^import\s+{re.escape(topic)}$", readme, f"stable import {topic}")
    require(
        r"public theorem surface reports only\s*"
        r"`\[propext, Classical\.choice, Quot\.sound\]`",
        readme,
        "public axiom surface",
    )
    theorem_count = int(
        require(
            r"theorems%2Flemmas-([0-9]+(?:%2C[0-9]+)*)-brightgreen",
            readme,
            "README theorem and lemma badge",
        )
        .group(1)
        .replace("%2C", "")
    )
    module_count = int(
        require(
            r"FormalSLT%20modules-([0-9]+)-blue",
            readme,
            "README module badge",
        ).group(1)
    )
    lean_lines = int(
        require(
            r"Lean%20lines-([0-9]+(?:%2C[0-9]+)*)-brightgreen",
            readme,
            "README Lean line badge",
        )
        .group(1)
        .replace("%2C", "")
    )

    facts = {
        "schema": "formalslt-overview-v1",
        "commit": BOUND_SHA,
        "short_commit": BOUND_SHA[:7],
        "library": {
            "modules": module_count,
            "theorems_and_lemmas": theorem_count,
            "lean_lines": lean_lines,
            "stable_topic_imports": stable_topic_imports,
        },
        "proof_spine": DECLARATIONS,
    }
    OUTPUT.write_text(json.dumps(facts, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)} from {BOUND_SHA}")


if __name__ == "__main__":
    main()
