#!/usr/bin/env python3
"""Extract overview-film facts from one exact FormalSLT commit."""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


BOUND_SHA = "501fee458a539db654097dbec8933427dae9fee9"
ROOT = Path(__file__).resolve().parents[2]
OUTPUT = Path(__file__).with_name("facts.json")


ANCHORS = [
    {
        "label": "Sauer-Shelah and VC ERM",
        "file": "FormalSLT/VC/BinaryCapstone.lean",
        "name": "vc_erm_excessRisk_tail_binary_zeroOneLoss",
    },
    {
        "label": "Metric-entropy generalization",
        "file": "FormalSLT/Rademacher/MetricEntropyGeneralization.lean",
        "name": "metricEntropy_generalization_mean",
    },
    {
        "label": "Finite sub-Gaussian chaining",
        "file": "FormalSLT/Covering/FiniteSubGaussianChaining.lean",
        "name": "finite_chaining_expectation_bound",
    },
    {
        "label": "Anytime PAC-Bayes",
        "file": "FormalSLT/PACBayes/TimeUniformTiltMixture.lean",
        "name": "timeUniformPACBayes_tiltMixture_allPosteriors_bound",
    },
    {
        "label": "E-process Type-I control",
        "file": "FormalSLT/AnytimeValid/EProcess.lean",
        "name": "eProcess_typeI_control",
    },
    {
        "label": "Adaptive trajectory guarantee",
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
        "label": "Controlled-queue scalar confidence",
        "file": (
            "FormalSLT/Applications/"
            "ControlledQueuePersistenceConfidence.lean"
        ),
        "name": "exists_persistenceHitConfidence_event",
    },
    {
        "label": "Controlled-queue exact structured transfer",
        "file": (
            "FormalSLT/Applications/"
            "ControlledQueuePersistenceConfidence.lean"
        ),
        "name": "refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy",
    },
]


STATEMENT_SHAPES = {
    "vc_erm_excessRisk_tail_binary_zeroOneLoss": (
        r"binaryClassTrace\s+h\s+z\)\.vcDim\s*≤\s*d",
        r"\(piMeasure\s+μ\s+n\)\.real",
        r"≤\s*2\s*\*\s*Real\.exp",
    ),
    "metricEntropy_generalization_mean": (
        r"∫\s+S,\s*genGap\s+μ\s+ℓ\s+S",
        r"≤\s*8\s*\*\s*Real\.sqrt",
        r"coveringNumberAtRadius",
    ),
    "finite_chaining_expectation_bound": (
        r"finiteExpectation\s+p\s*\(fun\s+ω\s*=>\s*finiteSup",
        r"∑\s+j\s+∈\s+Finset\.range\s+m,\s*budget\s+j",
    ),
    "timeUniformPACBayes_tiltMixture_allPosteriors_bound": (
        r"timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure",
        r"prior\s+weight\s+X\s+sigma2\s+b\s+lam\s+delta",
        r"≤\s*delta",
    ),
    "eProcess_typeI_control": (
        r"finiteRunningMax\s+E\s+n\s+ω",
        r"≤\s*α",
    ),
    "exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event": (
        r"∃\s+goodEvent\s*:\s*Set\s*\(ℕ\s*→\s*Z\)",
        r"trajectoryPosteriorAverageConditionalRisk",
        r"trajectoryPosteriorEmpiricalPrequentialRisk",
        r"Filter\.Tendsto",
    ),
    "exists_persistenceHitConfidence_event": (
        r"∃\s+goodEvent\s*:\s*Set\s*\(ℕ\s*→\s*Observation\)",
        r"empiricalPersistenceHitRate",
        r"persistenceHitRadius",
    ),
    "refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy": (
        r"finitePMFTotalVariation",
        r"persistenceHitProbability\s+gamma",
        r"candidatePersistenceHitProbability\s+candidate",
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


def source_at(file_name: str) -> str:
    return git("show", f"{BOUND_SHA}:{file_name}")


def require(pattern: str, source: str, description: str) -> re.Match[str]:
    match = re.search(pattern, source, flags=re.MULTILINE)
    if match is None:
        raise SystemExit(f"missing fact at {BOUND_SHA}: {description}")
    return match


def statement_for(file_name: str, declaration_name: str) -> str:
    source = source_at(file_name)
    return require(
        rf"^theorem\s+{re.escape(declaration_name)}\b"
        rf"(?P<statement>[\s\S]*?)\s*:=\s*by",
        source,
        f"complete theorem statement {declaration_name}",
    ).group("statement")


def main() -> None:
    resolved = git("rev-parse", BOUND_SHA).strip()
    if resolved != BOUND_SHA:
        raise SystemExit(f"commit did not resolve exactly: {resolved}")

    for anchor in ANCHORS:
        statement = statement_for(anchor["file"], anchor["name"])
        for index, shape in enumerate(STATEMENT_SHAPES[anchor["name"]], 1):
            require(shape, statement, f"statement shape {anchor['name']} [{index}]")

    queue_data = source_at("FormalSLT/Applications/ControlledQueueData.lean")
    physical_states = int(
        require(
            r"^abbrev\s+PhysicalState\s*:=\s*Fin\s+([0-9]+)\s*$",
            queue_data,
            "controlled-queue physical-state cardinality",
        ).group(1)
    )
    actions = int(
        require(
            r"^abbrev\s+Action\s*:=\s*Fin\s+([0-9]+)\s*$",
            queue_data,
            "controlled-queue action cardinality",
        ).group(1)
    )
    queue_catalog = source_at(
        "FormalSLT/Applications/ControlledQueueOPECatalog.lean"
    )
    transition_coordinates = int(
        require(
            r"theorem\s+queueTransitionCoordinate_card\s*:\s*"
            r"Fintype\.card\s+\(TransitionCoordinate\s+Observation\)\s*=\s*"
            r"([0-9]+)",
            queue_catalog,
            "controlled-queue transition-coordinate cardinality",
        ).group(1)
    )
    persistence_source = source_at(
        "FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean"
    )
    require(
        r"^def\s+persistenceHitProbability\b[\s\S]*?"
        r"\(1\s*\+\s*23\s*\*\s*\(gamma\s*:\s*ℝ\)\)\s*/\s*24",
        persistence_source,
        "persistence-hit probability formula",
    )

    anchors_by_label = {anchor["label"]: anchor for anchor in ANCHORS}
    film_anchor_labels = [
        "Sauer-Shelah and VC ERM",
        "Metric-entropy generalization",
        "Anytime PAC-Bayes",
        "Adaptive trajectory guarantee",
    ]
    facts = {
        "schema": "formalslt-overview-v3",
        "commit": BOUND_SHA,
        "short_commit": BOUND_SHA[:7],
        "research_map": [
            "VC theory",
            "Rademacher complexity",
            "Metric entropy and chaining",
            "PAC-Bayes",
            "Sequential inference",
            "Dependent data",
        ],
        "film_anchors": [anchors_by_label[label] for label in film_anchor_labels],
        "all_anchors": ANCHORS,
        "controlled_queue": {
            "physical_states": physical_states,
            "actions": actions,
            "observations": physical_states * actions,
            "transition_coordinate_sides": 2,
            "transition_coordinates": transition_coordinates,
            "hit_probability": "(1 + 23 * gamma) / 24",
            "scope": "declared refresh family",
            "row_tv_identity": (
                "TV(true physical row, candidate physical row) = "
                "|p_hit(true) - p_hit(candidate)|"
            ),
        },
    }
    OUTPUT.write_text(json.dumps(facts, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)} from {BOUND_SHA}")


if __name__ == "__main__":
    main()
