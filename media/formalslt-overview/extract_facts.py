#!/usr/bin/env python3
"""Extract overview-film facts from one exact FormalSLT commit."""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


BOUND_SHA = "7b1947544905aabf1b5ee8a6c3a7485e8762560e"
ROOT = Path(__file__).resolve().parents[2]
OUTPUT = Path(__file__).with_name("facts.json")

THEOREM_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:theorem|lemma)\s+[A-Za-z_]"
)

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
    {
        "stage": "Controlled-queue scalar confidence",
        "file": (
            "FormalSLT/Applications/"
            "ControlledQueuePersistenceConfidence.lean"
        ),
        "name": "exists_persistenceHitConfidence_event",
    },
    {
        "stage": "Controlled-queue exact structured transfer",
        "file": (
            "FormalSLT/Applications/"
            "ControlledQueuePersistenceConfidence.lean"
        ),
        "name": "refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy",
    },
]

DECLARATION_STATEMENT_SHAPES = {
    "exists_forwardEmpiricalBernsteinLowerTiltCatalog_event": (
        r"∃\s+goodEvent\s*:\s*Set\s+Ω",
        r"μ\.real\s+goodEventᶜ\s*≤\s*delta",
        r"∀\s+ω\s+∈\s+goodEvent,\s*∀\s+j\s*:\s*κ,\s*∀\s+n\s*:\s*ℕ,"
        r"\s*2\s*≤\s*n",
        r"mean\s*<\s*forwardPrefixMean[\s\S]*?"
        r"forwardEmpiricalBernsteinTiltCatalogBoundary",
    ),
    "timeUniformPACBayes_tiltMixture_allPosteriors_bound": (
        r"μ\.real\s*\(timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure",
        r"prior\s+weight\s+X\s+sigma2\s+b\s+lam\s+delta\)\s*≤\s*delta",
    ),
    "exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event": (
        r"∃\s+goodEvent\s*:\s*Set\s*\(ℕ\s*→\s*Z\)",
        r"\(trajectoryMeasure\s+K\s+x0\)\.real\s+goodEventᶜ\s*≤\s*delta",
        r"trajectoryPosteriorAverageConditionalRisk[\s\S]*?<"
        r"[\s\S]*?trajectoryPosteriorEmpiricalPrequentialRisk"
        r"[\s\S]*?trajectoryCountableEmpiricalBernsteinPACBayesBoundary",
        r"Filter\.Tendsto[\s\S]*?Filter\.atTop\s*\(nhds\s+0\)",
    ),
    "exists_empiricalStationaryCatalog_event": (
        r"∃\s+goodEvent\s*:\s*Set\s*\(ℕ\s*→\s*Z\)",
        r"\(markovPathMeasure\s+P\s+x0\)\.real\s+goodEventᶜ\s*≤"
        r"[\s\S]*?deltaRisk\s*\+\s*deltaTransition",
        r"let\s+eta\s*:=\s*empiricalCandidateKernelTVBudget",
        r"stationaryPosteriorMarkovRisk[\s\S]*?<"
        r"[\s\S]*?empiricalTransitionPosteriorRisk"
        r"[\s\S]*?empiricalStationaryCatalogBoundary",
    ),
    "exists_persistenceHitConfidence_event": (
        r"∃\s+goodEvent\s*:\s*Set\s*\(ℕ\s*→\s*Observation\)",
        r"∀\s+path\s+∈\s+goodEvent[\s\S]*?"
        r"\|persistenceHitProbability\s+gamma\s*-\s*"
        r"empiricalPersistenceHitRate\s+n\s+path\|\s*<\s*"
        r"persistenceHitRadius",
    ),
    "refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy": (
        r"finitePMFTotalVariation\s*"
        r"\(refreshEnvironment\s+gamma\s+state\s+action\)\s*"
        r"\(candidateEnvironment\s+candidate\s+state\s+action\)\s*=\s*"
        r"\|persistenceHitProbability\s+gamma\s*-\s*"
        r"candidatePersistenceHitProbability\s+candidate\|",
    ),
}


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


def bound_revision_library_counts() -> tuple[int, int, int]:
    """Count the pinned Lean surface using the repository badge contract."""
    lean_paths = [
        path
        for path in git(
            "ls-tree",
            "-r",
            "--name-only",
            BOUND_SHA,
            "--",
            "FormalSLT",
            "examples",
        ).splitlines()
        if path.endswith(".lean")
    ]
    library_paths = [path for path in lean_paths if path.startswith("FormalSLT/")]
    if not library_paths:
        raise SystemExit(f"no FormalSLT modules found at {BOUND_SHA}")

    theorem_count = 0
    lean_lines = 0
    for path in lean_paths:
        lines = source_at(path).splitlines()
        theorem_count += sum(1 for line in lines if THEOREM_RE.match(line))
        lean_lines += len(lines)

    return len(library_paths), theorem_count, lean_lines


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
        statement = require(
            rf"^theorem\s+{re.escape(name)}\b(?P<statement>[\s\S]*?)\s*:=\s*by",
            source,
            f"complete theorem statement {name}",
        ).group("statement")
        for index, shape in enumerate(DECLARATION_STATEMENT_SHAPES[name], 1):
            require(shape, statement, f"statement shape {name} [{index}]")

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
    module_count, theorem_count, lean_lines = bound_revision_library_counts()

    controlled_queue_data = source_at(
        "FormalSLT/Applications/ControlledQueueData.lean"
    )
    physical_states = int(
        require(
            r"^abbrev\s+PhysicalState\s*:=\s*Fin\s+([0-9]+)\s*$",
            controlled_queue_data,
            "controlled-queue physical-state cardinality",
        ).group(1)
    )
    actions = int(
        require(
            r"^abbrev\s+Action\s*:=\s*Fin\s+([0-9]+)\s*$",
            controlled_queue_data,
            "controlled-queue action cardinality",
        ).group(1)
    )
    controlled_queue_catalog = source_at(
        "FormalSLT/Applications/ControlledQueueOPECatalog.lean"
    )
    transition_coordinates = int(
        require(
            r"theorem\s+queueTransitionCoordinate_card\s*:\s*"
            r"Fintype\.card\s+\(TransitionCoordinate\s+Observation\)\s*=\s*"
            r"([0-9]+)",
            controlled_queue_catalog,
            "controlled-queue transition-coordinate cardinality",
        ).group(1)
    )
    persistence_source = source_at(
        "FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean"
    )
    require(
        r"^theorem\s+persistenceDestinationHit_rowRisk\b[\s\S]*?"
        r"markovRowRisk[\s\S]*?persistenceDestinationHitScore\s+current\s*=\s*"
        r"persistenceHitProbability\s+gamma\s*:=\s*by",
        persistence_source,
        "row-independent persistence-hit mean statement",
    )
    require(
        r"^def\s+persistenceHitProbability\b[\s\S]*?"
        r"\(1\s*\+\s*23\s*\*\s*\(gamma\s*:\s*ℝ\)\)\s*/\s*24",
        persistence_source,
        "persistence-hit probability formula",
    )
    require(
        r"^theorem\s+exists_persistenceHitConfidence_event\b[\s\S]*?"
        r"∃\s+goodEvent\s*:\s*Set\s*\(ℕ\s*→\s*Observation\)[\s\S]*?"
        r"∀\s+path\s+∈\s+goodEvent[\s\S]*?"
        r"\|persistenceHitProbability\s+gamma\s*-\s*"
        r"empiricalPersistenceHitRate\s+n\s+path\|\s*<\s*"
        r"persistenceHitRadius[\s\S]*?:=\s*by",
        persistence_source,
        "time-uniform scalar hit-confidence statement",
    )
    require(
        r"^theorem\s+refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy\b"
        r"[\s\S]*?finitePMFTotalVariation\s*"
        r"\(refreshEnvironment\s+gamma\s+state\s+action\)\s*"
        r"\(candidateEnvironment\s+candidate\s+state\s+action\)\s*=\s*"
        r"\|persistenceHitProbability\s+gamma\s*-\s*"
        r"candidatePersistenceHitProbability\s+candidate\|\s*:=\s*by",
        persistence_source,
        "exact physical-row TV transfer statement",
    )

    facts = {
        "schema": "formalslt-overview-v2",
        "commit": BOUND_SHA,
        "short_commit": BOUND_SHA[:7],
        "library": {
            "modules": module_count,
            "theorems_and_lemmas": theorem_count,
            "lean_lines": lean_lines,
            "stable_topic_imports": stable_topic_imports,
        },
        "controlled_queue": {
            "physical_states": physical_states,
            "actions": actions,
            "observations": physical_states * actions,
            "transition_coordinate_sides": 2,
            "transition_coordinates": transition_coordinates,
            "hit_probability": "(1 + 23 * gamma) / 24",
            "scope": "predeclared refresh family",
            "row_tv_identity": (
                "TV(true physical row, candidate physical row) = "
                "|p_hit(true) - p_hit(candidate)|"
            ),
            "row_tv_label": "EXACT TV IDENTITY   ·   EVERY PHYSICAL ROW",
            "row_tv_boundary": (
                "conditional on the predeclared refresh family",
                "not a family-membership test",
            ),
        },
        "proof_spine": DECLARATIONS,
    }
    OUTPUT.write_text(json.dumps(facts, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)} from {BOUND_SHA}")


if __name__ == "__main__":
    main()
