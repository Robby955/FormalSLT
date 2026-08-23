#!/usr/bin/env python3
"""Independently verify the controlled-queue known-kernel receipt.

This verifier deliberately does not import the receipt generator.  It parses
the frozen model tables and raw trace directly, reconstructs the selected
kernel, invariant law, depth-twelve potential, residual, aligned edge
histogram, score summaries, and conservative confidence endpoint using exact
``Fraction`` arithmetic, then checks the tracked receipt and manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import sys
import unicodedata
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "applications" / "controlled_queue" / "known-kernel-receipt-v1.json"
DEFAULT_RECEIPT = ROOT / "applications" / "controlled_queue" / "generated" / "known-kernel-receipt-v1.json"
DEFAULT_MANIFEST = ROOT / "applications" / "controlled_queue" / "generated" / "known-kernel-receipt-v1-manifest.json"
DEFAULT_LEAN = ROOT / "FormalSLT" / "Applications" / "ControlledQueueKnownKernelReceiptData.lean"
GENERATOR = ROOT / "scripts" / "generate_controlled_queue_known_kernel_receipt.py"
TRACE_HEADER = struct.Struct(">8sQ")
TRACE_MAGIC = bytes.fromhex("4351545256310000")
STATE_COUNT = 24
ACTION_COUNT = 2
SOURCE_HORIZON = 200000
N = 199999
SCHEMA_VERSION = "controlled-queue-known-kernel-receipt-input-v1"
GENERATOR_REVISION = "controlled-queue-known-kernel-receipt-generator-v1"
ARTIFACT_STATUS = "DETERMINISTIC KNOWN-KERNEL RECEIPT"

EXPECTED_BINDING_PATHS = {
    "model_input": "applications/controlled_queue/model-v1.json",
    "model_manifest": "applications/controlled_queue/generated/model-v1-manifest.json",
    "model_tables": "applications/controlled_queue/generated/model-v1-tables.json",
    "trace_binary": "applications/controlled_queue/generated/trace-v1.bin",
    "trace_counts": "applications/controlled_queue/generated/trace-v1-counts.json",
    "trace_input": "applications/controlled_queue/trace-v1.json",
    "trace_manifest": "applications/controlled_queue/generated/trace-v1-manifest.json",
}
MODEL_LEAN_PATH = "FormalSLT/Applications/ControlledQueueData.lean"
MODEL_GENERATOR_PATH = "scripts/generate_controlled_queue_model.py"
TRACE_GENERATOR_PATH = "scripts/generate_controlled_queue_trace.py"
TRACE_VERIFIER_PATH = "scripts/verify_controlled_queue_trace.py"


class VerificationError(ValueError):
    """Raised when any receipt identity or provenance binding fails."""


def _reject_float(value: str) -> None:
    raise VerificationError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise VerificationError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise VerificationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_booleans(
    value: Any, where: str, allowed_paths: frozenset[str] = frozenset()
) -> None:
    if isinstance(value, bool):
        if where not in allowed_paths:
            raise VerificationError(f"JSON booleans are forbidden at {where}")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            _reject_booleans(item, f"{where}.{key}", allowed_paths)
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _reject_booleans(item, f"{where}[{index}]", allowed_paths)


def _parse(raw: bytes, where: str) -> Any:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
        return value
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"invalid JSON in {where}: {error}") from error


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise VerificationError(f"{where} must be an object")
    return value


def _list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise VerificationError(f"{where} must be an array")
    return value


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise VerificationError(f"{where} mismatch: expected {expected!r}, got {actual!r}")


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    _exact(set(value), expected, f"{where} keys")


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def _rat_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def _rat(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise VerificationError(f"{where} must be a rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError(f"invalid rational at {where}: {value!r}") from error
    _exact(value, _rat_text(result), f"canonical rational at {where}")
    return result


def _lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def _render_list(values: list[str], indent: int = 2) -> str:
    if not values:
        return "[]"
    pad = " " * indent
    return "[\n" + ",\n".join(f"{pad}{value}" for value in values) + "\n]"


def _render_nested_nat(value: Any, indent: int = 2) -> str:
    if isinstance(value, int):
        return str(value)
    rows = [_render_nested_nat(item, indent + 2) for item in value]
    if not rows:
        return "[]"
    pad = " " * indent
    return (
        "[\n"
        + ",\n".join(f"{pad}{row}" for row in rows)
        + "\n"
        + " " * (indent - 2)
        + "]"
    )


def _render_nested_text(value: Any, indent: int = 2) -> str:
    if isinstance(value, str):
        return value
    rows = [_render_nested_text(item, indent + 2) for item in value]
    if not rows:
        return "[]"
    pad = " " * indent
    return (
        "[\n"
        + ",\n".join(f"{pad}{row}" for row in rows)
        + "\n"
        + " " * (indent - 2)
        + "]"
    )


def _render_expected_lean(
    *,
    receipt: dict[str, Any],
    invariant: list[Fraction],
    risk: list[Fraction],
    potential: list[Fraction],
    residual: list[Fraction],
    histogram: list[list[list[int]]],
    score_row_sums: list[list[Fraction]],
    score_square_row_sums: list[list[Fraction]],
    span: Fraction,
    reference_risk: Fraction,
    scale: Fraction,
    residual_envelope: Fraction,
    stationary_risk: Fraction,
    score_sum: Fraction,
    score_square_sum: Fraction,
    bessel_q: Fraction,
    hybrid: Fraction,
    endpoint: Fraction,
) -> bytes:
    """Render the expected Lean data independently of the generator."""

    potential_text = [_lean_rat(value) for value in potential]
    residual_text = [_lean_rat(value) for value in residual]
    invariant_text = [_lean_rat(value) for value in invariant]
    risk_text = [_lean_rat(value) for value in risk]
    score_row_sum_text = [
        [_lean_rat(value) for value in row] for row in score_row_sums
    ]
    score_square_row_sum_text = [
        [_lean_rat(value) for value in row] for row in score_square_row_sums
    ]
    histogram_row_definitions = "\n\n".join(
        f"private abbrev suffixEdgeRow_{state}_{action} : List Nat := "
        f"{_render_list([str(value) for value in histogram[state][action]])}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    histogram_row_branches = "\n".join(
        f"  | {state}, {action} => suffixEdgeRow_{state}_{action}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    histogram_row_references = [
        [f"suffixEdgeRow_{state}_{action}" for action in range(ACTION_COUNT)]
        for state in range(STATE_COUNT)
    ]
    score_row_branches = "\n".join(
        f"  | {state}, {action} => {score_row_sum_text[state][action]}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    score_square_row_branches = "\n".join(
        f"  | {state}, {action} => {score_square_row_sum_text[state][action]}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    content = f'''/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Mathlib.Data.Rat.Defs

/-!
# Generated controlled-queue known-kernel receipt data

This definitions-only module is generated by
`scripts/generate_controlled_queue_known_kernel_receipt.py`.  It contains exact
rational summaries and the suffix edge histogram.  It does not prove raw-byte
hashes, good-event membership, or a confidence theorem.
-/

namespace FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

/-- Receipt schema version. -/
def schemaVersion : String := "{SCHEMA_VERSION}"

/-- Receipt generator revision. -/
def generatorRevision : String := "{GENERATOR_REVISION}"

/-- Deterministic artifact status. -/
def artifactStatus : String := "{ARTIFACT_STATUS}"

/-- SHA-256 of the frozen model input.  This is a provenance label, not a
kernel-verified hash statement. -/
def sourceModelSHA256 : String :=
  "{receipt['dependency_hashes']['model_input']}"

/-- SHA-256 of the frozen raw trace.  This is a provenance label, not a
kernel-verified hash statement. -/
def sourceTraceSHA256 : String :=
  "{receipt['dependency_hashes']['trace_binary']}"

/-- SHA-256 of the upstream trace manifest. -/
def sourceTraceManifestSHA256 : String :=
  "{receipt['dependency_hashes']['trace_manifest']}"

/-- SHA-256 of the encoded 24-by-2-by-24 suffix histogram. -/
def suffixEdgeHistogramSHA256 : String :=
  "{receipt['trace_alignment']['suffix_edge_histogram_sha256']}"

/-- Original physical-transition horizon. -/
def sourceHorizon : Nat := {SOURCE_HORIZON}

/-- Number of controlled-path scores in the aligned suffix. -/
def receiptHorizon : Nat := {N}

/-- Selected target-policy index. -/
def selectedTargetIndex : Nat := {receipt['selection']['target_policy_index']}

/-- Selected fixed-predictor index. -/
def selectedPredictorIndex : Nat := {receipt['selection']['predictor_index']}

/-- Action component of the fixed controlled initial observation. -/
def receiptInitialActionIndex : Nat := {receipt['trace_alignment']['initial_controlled_observation']['action_index']}

/-- Physical-state component of the fixed controlled initial observation. -/
def receiptInitialStateIndex : Nat := {receipt['trace_alignment']['initial_controlled_observation']['physical_state_index']}

/-- Fixed potential depth. -/
def receiptDepth : Nat := {receipt['potential_receipt']['depth']}

/-- Shifted depth-twelve selected potential in physical-state order. -/
def selectedPotentialTable : List ℚ := {_render_list(potential_text)}

/-- Exact selected residual in physical-state order. -/
def selectedResidualTable : List ℚ := {_render_list(residual_text)}

/-- Exact selected invariant law in physical-state order. -/
def selectedStationaryLawTable : List ℚ := {_render_list(invariant_text)}

/-- Exact selected row risk in physical-state order. -/
def selectedRowRiskTable : List ℚ := {_render_list(risk_text)}

{histogram_row_definitions}

/-- One physical edge-count row for the aligned suffix.  The wildcard branch
is unreachable for `Fin 24 × Fin 2`; the handwritten checker proves the row
length after exhaustive finite elimination. -/
def suffixEdgeRow (state : Fin 24) (action : Fin 2) : List Nat :=
  match state.val, action.val with
{histogram_row_branches}
  | _, _ => []

/-- Physical edge counts for transitions `t = 1, ..., 199999`, indexed by
source state, action, and destination state. -/
def suffixEdgeHistogram : List (List (List Nat)) :=
  {_render_nested_text(histogram_row_references)}

/-- Exact score subtotal for one source-state/action row. -/
def selectedScoreRowSum (state : Fin 24) (action : Fin 2) : ℚ :=
  match state.val, action.val with
{score_row_branches}
  | _, _ => 0

/-- Exact squared-score subtotal for one source-state/action row. -/
def selectedScoreSquareRowSum (state : Fin 24) (action : Fin 2) : ℚ :=
  match state.val, action.val with
{score_square_row_branches}
  | _, _ => 0

/-- Exact score subtotal for each source-state/action row. -/
def selectedScoreRowSums : List (List ℚ) := {_render_nested_text(score_row_sum_text)}

/-- Exact squared-score subtotal for each source-state/action row. -/
def selectedScoreSquareRowSums : List (List ℚ) := {_render_nested_text(score_square_row_sum_text)}

/-- Exact potential span. -/
def selectedPotentialSpan : ℚ := {_lean_rat(span)}

/-- Exact uniform-reference average of the selected row risk. -/
def selectedUniformReferenceRisk : ℚ := {_lean_rat(reference_risk)}

/-- Exact affine normalization `C * (1 + 2B)`. -/
def selectedNormalizedScale : ℚ := {_lean_rat(scale)}

/-- Exact selected pointwise residual envelope. -/
def selectedResidualEnvelope : ℚ := {_lean_rat(residual_envelope)}

/-- Exact selected stationary Brier risk. -/
def selectedStationaryRisk : ℚ := {_lean_rat(stationary_risk)}

/-- Sum of the 199999 normalized observed scores. -/
def observedScoreSum : ℚ := {_lean_rat(score_sum)}

/-- Sum of squares of the normalized observed scores. -/
def observedScoreSquareSum : ℚ := {_lean_rat(score_square_sum)}

/-- Exact Bessel statistic derived from the two score summaries. -/
def observedScoreBesselQ : ℚ := {_lean_rat(bessel_q)}

/-- First-branch hybrid-Bessel upper bound. -/
def observedHybridPenaltyUpper : ℚ := {_lean_rat(hybrid)}

/-- Exact rational upper bound obtained from `log(480) ≤ 9` and
`psi(1/16) ≤ 1/240`. -/
def certifiedKnownKernelUpperBound : ℚ := {_lean_rat(endpoint)}

end FormalSLT.Applications.ControlledQueueKnownKernelReceiptData
'''
    return content.encode()


def _repo_file(path_text: str) -> tuple[Path, bytes]:
    path = (ROOT / path_text).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as error:
        raise VerificationError(f"path escapes repository: {path_text}") from error
    return path, path.read_bytes()


def _display(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def _path_identity(path: Path) -> str:
    return unicodedata.normalize("NFC", path.resolve().as_posix()).casefold()


def _same_file_target(left: Path, right: Path) -> bool:
    if _path_identity(left) == _path_identity(right):
        return True
    try:
        return left.exists() and right.exists() and left.samefile(right)
    except OSError:
        return False


def _manifest_rows_by_role(
    raw_rows: Any, expected_roles: set[str], where: str
) -> dict[str, dict[str, Any]]:
    rows = _list(raw_rows, where)
    result: dict[str, dict[str, Any]] = {}
    for index, raw_row in enumerate(rows):
        row = _object(raw_row, f"{where}[{index}]")
        _exact(set(row), {"bytes", "path", "role", "sha256"}, f"{where}[{index}] keys")
        role = row["role"]
        if not isinstance(role, str) or role in result:
            raise VerificationError(f"{where} has invalid or duplicate role: {role!r}")
        result[role] = row
    _exact(set(result), expected_roles, f"{where} roles")
    return result


def _verify_manifest_row(
    row: dict[str, Any], path: Path, raw: bytes, where: str
) -> None:
    _exact(row["path"], _display(path), f"{where} path")
    _exact(row["bytes"], len(raw), f"{where} bytes")
    _exact(row["sha256"], _sha(raw), f"{where} sha256")


def _verify_bound_files(spec: dict[str, Any]) -> dict[str, tuple[Path, bytes]]:
    bindings = _object(spec["bindings"], "bindings")
    expected_roles = {
        "model_input",
        "model_manifest",
        "model_tables",
        "trace_binary",
        "trace_counts",
        "trace_input",
        "trace_manifest",
    }
    _keys(bindings, expected_roles, "bindings")
    result: dict[str, tuple[Path, bytes]] = {}
    for role, raw_binding in sorted(bindings.items()):
        binding = _object(raw_binding, f"bindings.{role}")
        _exact(set(binding), {"path", "sha256"}, f"bindings.{role} keys")
        _exact(
            binding["path"],
            EXPECTED_BINDING_PATHS[role],
            f"bindings.{role} path",
        )
        path, raw = _repo_file(binding["path"])
        _exact(_sha(raw), binding["sha256"], f"bindings.{role} sha256")
        result[role] = (path, raw)
    return result


def _verify_artifact_paths(
    input_path: Path,
    receipt_path: Path,
    manifest_path: Path,
    lean_path: Path,
    files: dict[str, tuple[Path, bytes]],
) -> None:
    artifacts = {
        "receipt_input": input_path.resolve(),
        "receipt": receipt_path.resolve(),
        "manifest": manifest_path.resolve(),
        "lean": lean_path.resolve(),
    }
    artifact_items = list(artifacts.items())
    artifact_aliases = [
        (left_role, right_role)
        for index, (left_role, left_path) in enumerate(artifact_items)
        for right_role, right_path in artifact_items[index + 1 :]
        if _same_file_target(left_path, right_path)
    ]
    if artifact_aliases:
        raise VerificationError(
            "receipt artifact paths must be distinct: "
            f"aliases={artifact_aliases}, paths={artifacts}"
        )
    protected = {
        "generator": GENERATOR.resolve(),
        "independent_verifier": Path(__file__).resolve(),
        **{role: path.resolve() for role, (path, _raw) in files.items()},
    }
    collisions = [
        f"{artifact_role}={artifact_path} aliases {protected_role}"
        for artifact_role, artifact_path in artifacts.items()
        if artifact_role != "receipt_input"
        for protected_role, protected_path in protected.items()
        if _same_file_target(artifact_path, protected_path)
    ]
    if collisions:
        raise VerificationError(
            "receipt artifact path aliases protected input: " + "; ".join(collisions)
        )


def _verify_input_contract(spec: dict[str, Any]) -> None:
    _keys(
        spec,
        {
            "artifact_status",
            "bindings",
            "confidence_contract",
            "edge_histogram_contract",
            "expected_receipt",
            "nonclaims",
            "potential_contract",
            "schema_version",
            "selection",
            "trace_alignment",
        },
        "receipt input",
    )
    _exact(spec["schema_version"], SCHEMA_VERSION, "receipt input schema")
    _exact(
        spec["artifact_status"],
        "DETERMINISTIC KNOWN-KERNEL RECEIPT INPUT",
        "receipt input status",
    )
    _exact(
        _object(spec["selection"], "selection"),
        {
            "candidate_id": "nominal",
            "candidate_index": 1,
            "predictor_id": "nominal_model_overload",
            "predictor_index": 2,
            "target_policy_id": "queue_threshold",
            "target_policy_index": 1,
        },
        "selection",
    )
    _exact(
        _object(spec["potential_contract"], "potential contract"),
        {
            "centering_reference": "uniform_physical_state_reference",
            "depth": 12,
            "selected_potential_shift": {
                "anchor_state": 0,
                "definition": "h_shift(z) = h_raw(z) - h_raw(0)",
            },
            "unselected_potential": "zero",
            "unselected_residual_envelope": "1",
        },
        "potential contract",
    )
    _exact(
        _object(spec["confidence_contract"], "confidence contract"),
        {
            "failure_budget": "1/40",
            "importance_ratio_cap": "3/2",
            "posterior": "dirac_queue_threshold_nominal_model_overload",
            "risk_tilt": "1/16",
            "risk_tilt_weight": "1",
            "twelve_hypothesis_prior_mass": "1/12",
        },
        "confidence contract",
    )
    _exact(
        _object(spec["edge_histogram_contract"], "histogram contract"),
        {
            "axes": ["current_state", "action", "next_state"],
            "encoded_bytes": 9216,
            "flat_index": "((current_state * 2 + action) * 24 + next_state)",
            "positive_cells": 1152,
            "sha256": "2a484e76850d41fa40e16bdb988bb24131a355800e503e283a26ad22b9d8a874",
            "shape": [24, 2, 24],
            "total": N,
            "word_encoding": "unsigned 64-bit big-endian",
        },
        "histogram contract",
    )
    expected_receipt = _object(spec["expected_receipt"], "expected receipt")
    _keys(
        expected_receipt,
        {
            "bessel_q",
            "certified_upper_bound",
            "hybrid_first_branch_upper",
            "potential_span",
            "residual_envelope",
            "score_sum",
            "score_sum_squares",
            "stationary_risk",
        },
        "expected receipt",
    )
    for key, value in expected_receipt.items():
        _rat(value, f"expected receipt {key}")
    _exact(
        _object(spec["trace_alignment"], "trace alignment"),
        {
            "controlled_observation": "x_k = (A_k, S_{k+1})",
            "controlled_observation_range": {
                "start_inclusive": 0,
                "stop_exclusive": SOURCE_HORIZON,
            },
            "excluded_transition": {
                "action": 1,
                "current_state": 0,
                "next_state": 1,
                "physical_index": 0,
            },
            "initial_controlled_observation": {
                "action_index": 1,
                "physical_state_index": 1,
            },
            "physical_transition_range": {
                "start_inclusive": 1,
                "stop_exclusive": SOURCE_HORIZON,
            },
            "score_count": N,
            "score_index_range": {"start_inclusive": 0, "stop_exclusive": N},
            "source_horizon": SOURCE_HORIZON,
        },
        "trace alignment",
    )
    _exact(
        spec["nonclaims"],
        [
            "not a proof that the frozen trace belongs to the theorem-produced good event",
            "not a confidence guarantee conditional on this particular frozen trace",
            "not an unknown-kernel certificate",
            "not a data-selected candidate, potential depth, or potential catalog",
            "not a Lean decoder or SHA-256 verification of the raw trace bytes",
        ],
        "receipt input nonclaims",
    )


def _verify_receipt_schema(receipt: dict[str, Any]) -> None:
    _keys(
        receipt,
        {
            "artifact_status",
            "confidence_receipt",
            "dependency_hashes",
            "model_receipt",
            "nonclaims",
            "potential_receipt",
            "receipt_version",
            "schema_version",
            "score_receipt",
            "selection",
            "trace_alignment",
        },
        "receipt",
    )
    _keys(
        _object(receipt["selection"], "receipt selection"),
        {
            "candidate_id",
            "candidate_index",
            "predictor_id",
            "predictor_index",
            "target_policy_id",
            "target_policy_index",
        },
        "receipt selection",
    )
    _keys(
        _object(receipt["trace_alignment"], "receipt trace alignment"),
        {
            "controlled_observation",
            "controlled_observation_range",
            "excluded_edge",
            "excluded_transition",
            "full_edge_histogram_sha256",
            "included_terminal_edge",
            "initial_controlled_observation",
            "off_by_one_edge_histogram_sha256",
            "off_by_one_histogram_is_distinct",
            "physical_transition_range",
            "score_count",
            "score_index_range",
            "source_horizon",
            "suffix_edge_histogram",
            "suffix_edge_histogram_sha256",
        },
        "receipt trace alignment",
    )
    _keys(
        _object(receipt["model_receipt"], "receipt model"),
        {
            "selected_row_risk",
            "stationary_law",
            "stationary_risk",
            "target_kernel",
            "uniform_reference_row_risk_mean",
        },
        "receipt model",
    )
    _keys(
        _object(receipt["potential_receipt"], "receipt potential"),
        {
            "depth",
            "normalized_scale",
            "residual",
            "residual_envelope",
            "shift",
            "span",
            "values",
        },
        "receipt potential",
    )
    _keys(
        _object(receipt["score_receipt"], "receipt score"),
        {
            "bessel_q",
            "hybrid_first_branch_upper",
            "row_sum_squares",
            "row_sums",
            "sum",
            "sum_squares",
        },
        "receipt score",
    )
    _keys(
        _object(receipt["confidence_receipt"], "receipt confidence"),
        {
            "certified_log_cost_upper",
            "certified_psi_upper",
            "certified_threshold",
            "certified_upper_bound",
            "coverage_statement",
            "failure_budget",
            "importance_ratio_cap",
            "log_cost_identity",
            "posterior",
            "risk_tilt",
            "risk_tilt_weight",
            "twelve_hypothesis_prior_mass",
        },
        "receipt confidence",
    )
    _keys(
        _object(receipt["dependency_hashes"], "receipt dependencies"),
        {
            "model_input",
            "model_manifest",
            "model_tables",
            "trace_binary",
            "trace_counts",
            "trace_input",
            "trace_manifest",
        },
        "receipt dependencies",
    )


def _verify_manifest_references(manifest: dict[str, Any], where: str) -> None:
    for key in ("files", "inputs", "outputs"):
        for index, raw_row in enumerate(manifest.get(key, [])):
            row = _object(raw_row, f"{where}.{key}[{index}]")
            _path, data = _repo_file(row["path"])
            _exact(_sha(data), row["sha256"], f"{where}.{key}[{index}] hash")
            if "bytes" in row:
                _exact(len(data), row["bytes"], f"{where}.{key}[{index}] bytes")
    for key in ("generator", "independent_verifier"):
        if key in manifest:
            row = _object(manifest[key], f"{where}.{key}")
            _path, data = _repo_file(row["path"])
            _exact(_sha(data), row["sha256"], f"{where}.{key} hash")
    for index, raw_row in enumerate(manifest.get("generator_dependencies", [])):
        row = _object(raw_row, f"{where}.generator_dependencies[{index}]")
        _path, data = _repo_file(row["path"])
        _exact(_sha(data), row["sha256"], f"{where}.generator dependency hash")


def _manifest_file_row(
    raw_row: Any,
    *,
    expected_path: str,
    expected_role: str,
    include_bytes: bool,
    where: str,
) -> dict[str, Any]:
    row = _object(raw_row, where)
    expected_keys = {"path", "role", "sha256"}
    if include_bytes:
        expected_keys.add("bytes")
    _keys(row, expected_keys, where)
    _exact(row["path"], expected_path, f"{where} path")
    _exact(row["role"], expected_role, f"{where} role")
    digest = row["sha256"]
    if (
        not isinstance(digest, str)
        or len(digest) != 64
        or any(character not in "0123456789abcdef" for character in digest)
    ):
        raise VerificationError(f"{where} sha256 must be a lowercase SHA-256 digest")
    if include_bytes and (
        isinstance(row["bytes"], bool)
        or not isinstance(row["bytes"], int)
        or row["bytes"] < 0
    ):
        raise VerificationError(f"{where} bytes must be a nonnegative integer")
    return row


def _binding_identity(spec: dict[str, Any], role: str) -> dict[str, Any]:
    binding = _object(spec["bindings"][role], f"bindings.{role}")
    return {"path": binding["path"], "sha256": binding["sha256"]}


def _row_identity(row: dict[str, Any]) -> dict[str, Any]:
    return {"path": row["path"], "sha256": row["sha256"]}


def _verify_upstream_manifests(
    spec: dict[str, Any],
    model_manifest: dict[str, Any],
    trace_manifest: dict[str, Any],
) -> None:
    """Cross-bind the two frozen upstream manifests to every consumed role."""

    _keys(
        model_manifest,
        {
            "artifact_status",
            "files",
            "generator",
            "model_version",
            "nonclaims",
            "parameters",
            "schema_version",
        },
        "model manifest",
    )
    _exact(
        model_manifest["artifact_status"],
        "MODEL/PREPROCESSING ONLY",
        "model manifest status",
    )
    _exact(
        model_manifest["schema_version"],
        "controlled-queue-input-v1",
        "model manifest schema",
    )
    _exact(
        model_manifest["model_version"],
        "controlled-queue-v1",
        "model manifest version",
    )
    _keys(
        _object(model_manifest["parameters"], "model manifest parameters"),
        {
            "action_count",
            "augmented_behavior_state_count",
            "candidate_gammas",
            "confidence_allocation",
            "depth_grid",
            "horizon",
            "next_trace_slice_contract",
            "nominal_candidate",
            "physical_state_count",
            "posterior_catalog",
            "random_seed",
            "tilt_grid",
        },
        "model manifest parameters",
    )
    _exact(
        model_manifest["nonclaims"],
        [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not a proof bridge",
        ],
        "model manifest nonclaims",
    )
    model_generator = _object(model_manifest["generator"], "model manifest generator")
    _keys(
        model_generator,
        {"path", "revision", "sha256"},
        "model manifest generator",
    )
    _exact(
        model_generator["path"],
        MODEL_GENERATOR_PATH,
        "model manifest generator path",
    )
    _exact(
        model_generator["revision"],
        "controlled-queue-preprocess-v1",
        "model manifest generator revision",
    )
    model_files = _list(model_manifest["files"], "model manifest files")
    _exact(len(model_files), 3, "model manifest files length")
    model_input_row = _manifest_file_row(
        model_files[0],
        expected_path=EXPECTED_BINDING_PATHS["model_input"],
        expected_role="input",
        include_bytes=False,
        where="model manifest files[0]",
    )
    model_tables_row = _manifest_file_row(
        model_files[1],
        expected_path=EXPECTED_BINDING_PATHS["model_tables"],
        expected_role="output",
        include_bytes=False,
        where="model manifest files[1]",
    )
    _manifest_file_row(
        model_files[2],
        expected_path=MODEL_LEAN_PATH,
        expected_role="output",
        include_bytes=False,
        where="model manifest files[2]",
    )
    _exact(
        _row_identity(model_input_row),
        _binding_identity(spec, "model_input"),
        "model manifest model_input binding",
    )
    _exact(
        _row_identity(model_tables_row),
        _binding_identity(spec, "model_tables"),
        "model manifest model_tables binding",
    )

    _keys(
        trace_manifest,
        {
            "artifact_status",
            "files",
            "generator",
            "generator_dependencies",
            "independent_verifier",
            "manifest_note",
            "nonclaims",
            "parameters",
            "schema_version",
            "trace_version",
        },
        "trace manifest",
    )
    _exact(
        trace_manifest["artifact_status"],
        "TRACE/PREPROCESSING ONLY",
        "trace manifest status",
    )
    _exact(
        trace_manifest["schema_version"],
        "controlled-queue-trace-input-v1",
        "trace manifest schema",
    )
    _exact(
        trace_manifest["trace_version"],
        "controlled-queue-trace-v1",
        "trace manifest version",
    )
    _exact(
        trace_manifest["manifest_note"],
        "the manifest is canonical JSON and is not recursively self-hashed",
        "trace manifest note",
    )
    _keys(
        _object(trace_manifest["parameters"], "trace manifest parameters"),
        {
            "behavior_policy",
            "binary_layout",
            "binary_version",
            "horizon",
            "initial_state",
            "prng_version",
            "sampling_version",
            "source_candidate",
        },
        "trace manifest parameters",
    )
    _exact(
        trace_manifest["nonclaims"],
        [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not Lean-verified trace data",
            "not a direct deterministic-initial ControlledTrajectory horizon alignment",
            "not an unknown-kernel target-policy OPE result",
        ],
        "trace manifest nonclaims",
    )
    trace_generator = _object(trace_manifest["generator"], "trace manifest generator")
    _keys(
        trace_generator,
        {"path", "revision", "sha256"},
        "trace manifest generator",
    )
    _exact(
        trace_generator["path"],
        TRACE_GENERATOR_PATH,
        "trace manifest generator path",
    )
    _exact(
        trace_generator["revision"],
        "controlled-queue-trace-generator-v1",
        "trace manifest generator revision",
    )
    trace_verifier = _object(
        trace_manifest["independent_verifier"],
        "trace manifest independent verifier",
    )
    _keys(
        trace_verifier,
        {"path", "sha256"},
        "trace manifest independent verifier",
    )
    _exact(
        trace_verifier["path"],
        TRACE_VERIFIER_PATH,
        "trace manifest independent verifier path",
    )
    trace_files = _list(trace_manifest["files"], "trace manifest files")
    _exact(len(trace_files), 4, "trace manifest files length")
    trace_input_row = _manifest_file_row(
        trace_files[0],
        expected_path=EXPECTED_BINDING_PATHS["trace_input"],
        expected_role="trace_input",
        include_bytes=False,
        where="trace manifest files[0]",
    )
    trace_model_row = _manifest_file_row(
        trace_files[1],
        expected_path=EXPECTED_BINDING_PATHS["model_input"],
        expected_role="model_input",
        include_bytes=False,
        where="trace manifest files[1]",
    )
    trace_binary_row = _manifest_file_row(
        trace_files[2],
        expected_path=EXPECTED_BINDING_PATHS["trace_binary"],
        expected_role="raw_trace_output",
        include_bytes=True,
        where="trace manifest files[2]",
    )
    trace_counts_row = _manifest_file_row(
        trace_files[3],
        expected_path=EXPECTED_BINDING_PATHS["trace_counts"],
        expected_role="counts_output",
        include_bytes=True,
        where="trace manifest files[3]",
    )
    for role, row in (
        ("trace_input", trace_input_row),
        ("trace_binary", trace_binary_row),
        ("trace_counts", trace_counts_row),
    ):
        _exact(
            _row_identity(row),
            _binding_identity(spec, role),
            f"trace manifest {role} binding",
        )
    _exact(
        _row_identity(trace_model_row),
        _binding_identity(spec, "model_input"),
        "trace manifest model_input binding",
    )
    _exact(
        _row_identity(trace_model_row),
        _row_identity(model_input_row),
        "trace manifest model_input dependency",
    )
    dependencies = _list(
        trace_manifest["generator_dependencies"],
        "trace manifest generator dependencies",
    )
    _exact(len(dependencies), 1, "trace manifest generator dependencies length")
    model_dependency = _object(
        dependencies[0],
        "trace manifest generator dependencies[0]",
    )
    _keys(
        model_dependency,
        {"path", "sha256"},
        "trace manifest generator dependencies[0]",
    )
    _exact(
        model_dependency,
        {"path": model_generator["path"], "sha256": model_generator["sha256"]},
        "trace manifest model-generator dependency",
    )

    _verify_manifest_references(model_manifest, "model manifest")
    _verify_manifest_references(trace_manifest, "trace manifest")


def _rows(table: Any, value_key: str, expected_rows: int, width: int, where: str) -> list[list[Fraction]]:
    rows = _list(table, where)
    _exact(len(rows), expected_rows, f"{where} row count")
    result: list[list[Fraction]] = []
    for row_index, raw_row in enumerate(rows):
        row = _object(raw_row, f"{where}[{row_index}]")
        values = _list(row[value_key], f"{where}[{row_index}].{value_key}")
        _exact(len(values), width, f"{where}[{row_index}] width")
        result.append([_rat(value, f"{where}[{row_index}][{column}]") for column, value in enumerate(values)])
    return result


def _solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    size = len(rhs)
    rows = [matrix[index][:] + [rhs[index]] for index in range(size)]
    for column in range(size):
        pivot = next((index for index in range(column, size) if rows[index][column]), None)
        if pivot is None:
            raise VerificationError(f"singular invariant system at column {column}")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        divisor = rows[column][column]
        rows[column] = [value / divisor for value in rows[column]]
        for index in range(size):
            if index == column:
                continue
            multiplier = rows[index][column]
            if multiplier:
                rows[index] = [
                    left - multiplier * right
                    for left, right in zip(rows[index], rows[column], strict=True)
                ]
    return [rows[index][-1] for index in range(size)]


def _invariant(kernel: list[list[Fraction]]) -> list[Fraction]:
    matrix = []
    rhs = []
    for destination in range(STATE_COUNT - 1):
        matrix.append([
            kernel[source][destination] - int(source == destination)
            for source in range(STATE_COUNT)
        ])
        rhs.append(Fraction(0))
    matrix.append([Fraction(1)] * STATE_COUNT)
    rhs.append(Fraction(1))
    law = _solve(matrix, rhs)
    _exact(sum(law), Fraction(1), "invariant mass")
    if any(value <= 0 for value in law):
        raise VerificationError("invariant law is not strictly positive")
    for destination in range(STATE_COUNT):
        _exact(
            sum((law[source] * kernel[source][destination] for source in range(STATE_COUNT)), Fraction(0)),
            law[destination],
            f"invariant balance at {destination}",
        )
    return law


def _apply(kernel: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [
        sum((kernel[source][destination] * vector[destination] for destination in range(STATE_COUNT)), Fraction(0))
        for source in range(STATE_COUNT)
    ]


def _decode_trace(raw: bytes) -> tuple[bytes, bytes]:
    expected = TRACE_HEADER.size + SOURCE_HORIZON + 1 + SOURCE_HORIZON + 16 * SOURCE_HORIZON
    _exact(len(raw), expected, "trace byte length")
    magic, horizon = TRACE_HEADER.unpack_from(raw)
    _exact(magic, TRACE_MAGIC, "trace magic")
    _exact(horizon, SOURCE_HORIZON, "trace horizon")
    offset = TRACE_HEADER.size
    states = raw[offset : offset + SOURCE_HORIZON + 1]
    offset += SOURCE_HORIZON + 1
    actions = raw[offset : offset + SOURCE_HORIZON]
    if max(states) >= STATE_COUNT or max(actions) >= ACTION_COUNT:
        raise VerificationError("trace state/action out of range")
    return states, actions


def _histogram(states: bytes, actions: bytes, start: int, stop: int) -> list[list[list[int]]]:
    result = [[[0] * STATE_COUNT for _action in range(ACTION_COUNT)] for _state in range(STATE_COUNT)]
    for time in range(start, stop):
        result[states[time]][actions[time]][states[time + 1]] += 1
    return result


def _histogram_bytes(histogram: list[list[list[int]]]) -> bytes:
    return b"".join(
        struct.pack(">Q", histogram[state][action][destination])
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
        for destination in range(STATE_COUNT)
    )


def verify(
    input_path: Path,
    receipt_path: Path,
    manifest_path: Path,
    lean_path: Path,
) -> None:
    input_raw = input_path.read_bytes()
    receipt_raw = receipt_path.read_bytes()
    manifest_raw = manifest_path.read_bytes()
    lean_raw = lean_path.read_bytes()
    spec = _object(_parse(input_raw, "receipt input"), "receipt input")
    receipt = _object(_parse(receipt_raw, "receipt"), "receipt")
    manifest = _object(_parse(manifest_raw, "receipt manifest"), "receipt manifest")
    _exact(input_raw, _canonical(spec), "canonical receipt input")
    _exact(receipt_raw, _canonical(receipt), "canonical receipt")
    _exact(manifest_raw, _canonical(manifest), "canonical receipt manifest")
    _reject_booleans(spec, "receipt input")
    _reject_booleans(
        receipt,
        "receipt",
        frozenset({"receipt.trace_alignment.off_by_one_histogram_is_distinct"}),
    )
    _reject_booleans(manifest, "receipt manifest")
    _verify_input_contract(spec)
    _verify_receipt_schema(receipt)
    files = _verify_bound_files(spec)
    _verify_artifact_paths(
        input_path, receipt_path, manifest_path, lean_path, files
    )
    _exact(receipt["artifact_status"], ARTIFACT_STATUS, "receipt status")
    _exact(
        receipt["receipt_version"],
        "controlled-queue-known-kernel-receipt-v1",
        "receipt version",
    )
    _exact(receipt["schema_version"], SCHEMA_VERSION, "receipt schema")
    _exact(receipt["selection"], spec["selection"], "receipt selection")
    _exact(
        receipt["model_receipt"]["target_kernel"],
        "queue_threshold policy mixed with nominal candidate",
        "receipt target-kernel description",
    )
    model_manifest = _object(
        _parse(files["model_manifest"][1], "model manifest"),
        "model manifest",
    )
    trace_manifest = _object(
        _parse(files["trace_manifest"][1], "trace manifest"),
        "trace manifest",
    )
    _exact(
        files["model_manifest"][1],
        _canonical(model_manifest),
        "canonical model manifest",
    )
    _exact(
        files["trace_manifest"][1],
        _canonical(trace_manifest),
        "canonical trace manifest",
    )
    _verify_upstream_manifests(spec, model_manifest, trace_manifest)

    tables = _object(_parse(files["model_tables"][1], "model tables"), "model tables")
    _exact(files["model_tables"][1], _canonical(tables), "canonical model tables")
    candidate = _object(_list(tables["candidate_kernels"], "candidate kernels")[1], "nominal candidate")
    policy = _object(_list(tables["policies"], "policies")[2], "queue-threshold policy")
    brier = _object(_list(tables["fixed_brier_loss"], "fixed Brier tables")[2], "nominal-model Brier")
    _exact(candidate["id"], "nominal", "candidate id")
    _exact(policy["id"], "queue_threshold", "policy id")
    _exact(brier["id"], "nominal_model_overload", "predictor id")
    q_rows = _rows(candidate["rows"], "probabilities", 48, 24, "candidate rows")
    pi_rows = _rows(policy["rows"], "probabilities", 24, 2, "policy rows")
    loss_rows = _rows(brier["rows"], "losses", 48, 24, "Brier rows")

    kernel = [
        [sum((pi_rows[z][a] * q_rows[2 * z + a][y] for a in range(2)), Fraction(0)) for y in range(24)]
        for z in range(24)
    ]
    risk = [
        sum(
            (
                pi_rows[z][a]
                * sum((q_rows[2 * z + a][y] * loss_rows[2 * z + a][y] for y in range(24)), Fraction(0))
                for a in range(2)
            ),
            Fraction(0),
        )
        for z in range(24)
    ]
    reference_risk = sum(risk, Fraction(0)) / 24
    iterate = [value - reference_risk for value in risk]
    raw_potential = [Fraction(0)] * 24
    for _step in range(12):
        raw_potential = [left + right for left, right in zip(raw_potential, iterate, strict=True)]
        iterate = _apply(kernel, iterate)
    anchor = raw_potential[0]
    potential = [value - anchor for value in raw_potential]
    _exact(min(potential), Fraction(0), "potential minimum")
    span = max(potential)
    invariant = _invariant(kernel)
    stationary_risk = sum((invariant[z] * risk[z] for z in range(24)), Fraction(0))
    next_potential = _apply(kernel, potential)
    residual = [risk[z] + next_potential[z] - potential[z] - stationary_risk for z in range(24)]
    residual_envelope = max(abs(value) for value in residual)
    _exact(receipt["potential_receipt"]["depth"], 12, "receipt potential depth")
    _exact(
        _rat(receipt["potential_receipt"]["shift"], "receipt potential shift"),
        anchor,
        "receipt potential shift",
    )

    states, actions = _decode_trace(files["trace_binary"][1])
    _exact((states[0], actions[0], states[1]), (0, 1, 1), "excluded edge")
    _exact((states[-2], actions[-1], states[-1]), (6, 1, 1), "terminal included edge")
    full_histogram = _histogram(states, actions, 0, 200000)
    suffix_histogram = _histogram(states, actions, 1, 200000)
    wrong_histogram = _histogram(states, actions, 0, 199999)
    tracked_counts = _object(_parse(files["trace_counts"][1], "trace counts"), "trace counts")
    _exact(full_histogram, tracked_counts["counts"]["edge_counts"], "tracked full histogram")
    removed = [[[full_histogram[z][a][y] for y in range(24)] for a in range(2)] for z in range(24)]
    removed[0][1][1] -= 1
    _exact(suffix_histogram, removed, "suffix equals full histogram minus first edge")
    _exact(_sha(_histogram_bytes(suffix_histogram)), "2a484e76850d41fa40e16bdb988bb24131a355800e503e283a26ad22b9d8a874", "suffix histogram hash")
    _exact(_sha(_histogram_bytes(wrong_histogram)), "1f29382a3b672ea83c66fc9f7bc910c0097c3fb974286a2959395fa041cb65bb", "wrong histogram hash")
    _exact(_sha(_histogram_bytes(full_histogram)), "f49a5bdcc9789270b07b80fe2b1c30f81991259d9d273c755ce9d64f2b017ee8", "full histogram hash")
    trace_receipt = receipt["trace_alignment"]
    for key, expected_value in spec["trace_alignment"].items():
        _exact(trace_receipt[key], expected_value, f"receipt trace alignment {key}")
    _exact(trace_receipt["excluded_edge"], [0, 1, 1], "receipt excluded edge")
    _exact(trace_receipt["included_terminal_edge"], [6, 1, 1], "receipt terminal edge")
    _exact(
        trace_receipt["suffix_edge_histogram_sha256"],
        "2a484e76850d41fa40e16bdb988bb24131a355800e503e283a26ad22b9d8a874",
        "receipt suffix histogram hash",
    )
    _exact(
        trace_receipt["off_by_one_edge_histogram_sha256"],
        "1f29382a3b672ea83c66fc9f7bc910c0097c3fb974286a2959395fa041cb65bb",
        "receipt wrong-prefix histogram hash",
    )
    _exact(
        trace_receipt["full_edge_histogram_sha256"],
        "f49a5bdcc9789270b07b80fe2b1c30f81991259d9d273c755ce9d64f2b017ee8",
        "receipt full histogram hash",
    )
    off_by_one_distinct = trace_receipt["off_by_one_histogram_is_distinct"]
    if type(off_by_one_distinct) is not bool:
        raise VerificationError("receipt off-by-one distinction must be a JSON boolean")
    _exact(off_by_one_distinct, True, "receipt off-by-one distinction")

    scale = Fraction(3, 2) * (1 + 2 * span)
    observed = [
        [
            [
                (pi_rows[z][a] / Fraction(1, 2))
                * (loss_rows[2 * z + a][y] + potential[y] - potential[z] + span)
                / scale
                for y in range(24)
            ]
            for a in range(2)
        ]
        for z in range(24)
    ]
    if any(value < 0 or value > 1 for zr in observed for ar in zr for value in ar):
        raise VerificationError("observed score escaped [0,1]")
    score_row_sums = [
        [
            sum(
                (
                    suffix_histogram[z][a][y] * observed[z][a][y]
                    for y in range(24)
                ),
                Fraction(0),
            )
            for a in range(2)
        ]
        for z in range(24)
    ]
    score_square_row_sums = [
        [
            sum(
                (
                    suffix_histogram[z][a][y] * observed[z][a][y] ** 2
                    for y in range(24)
                ),
                Fraction(0),
            )
            for a in range(2)
        ]
        for z in range(24)
    ]
    score_sum = sum(
        (value for row in score_row_sums for value in row), Fraction(0)
    )
    score_square_sum = sum(
        (value for row in score_square_row_sums for value in row), Fraction(0)
    )
    bessel_q = score_square_sum - score_sum * score_sum / N
    hybrid = Fraction(1, 2) + Fraction(3, 2) * bessel_q
    endpoint = (
        scale
        * (score_sum / N + (Fraction(9) + Fraction(1, 240) * hybrid) / (N * Fraction(1, 16)))
        - span
        + residual_envelope
    )
    if endpoint >= Fraction(7, 100):
        raise VerificationError(f"endpoint is not below 7/100: {endpoint}")

    confidence_receipt = receipt["confidence_receipt"]
    for key, expected_value in spec["confidence_contract"].items():
        _exact(confidence_receipt[key], expected_value, f"receipt confidence {key}")
    _exact(
        confidence_receipt["log_cost_identity"],
        "log(12) + log(40) = log(480)",
        "receipt log-cost identity",
    )
    _exact(
        _rat(confidence_receipt["certified_log_cost_upper"], "receipt log cost"),
        Fraction(9),
        "receipt log cost",
    )
    _exact(
        _rat(confidence_receipt["certified_psi_upper"], "receipt psi"),
        Fraction(1, 240),
        "receipt psi",
    )
    _exact(confidence_receipt["certified_threshold"], "7/100", "receipt threshold")
    _exact(
        confidence_receipt["coverage_statement"],
        "the theorem-generated event has complement outer mass at most 1/40",
        "receipt coverage statement",
    )

    expected = {
        "stationary_risk": stationary_risk,
        "potential_span": span,
        "residual_envelope": residual_envelope,
        "score_sum": score_sum,
        "score_sum_squares": score_square_sum,
        "bessel_q": bessel_q,
        "hybrid_first_branch_upper": hybrid,
        "certified_upper_bound": endpoint,
    }
    for key, value in expected.items():
        _exact(_rat(spec["expected_receipt"][key], f"input expected {key}"), value, f"input expected {key}")
    _exact([_rat(value, "receipt invariant") for value in receipt["model_receipt"]["stationary_law"]], invariant, "receipt invariant")
    _exact([_rat(value, "receipt row risk") for value in receipt["model_receipt"]["selected_row_risk"]], risk, "receipt row risk")
    _exact(_rat(receipt["model_receipt"]["uniform_reference_row_risk_mean"], "receipt reference risk"), reference_risk, "receipt reference risk")
    _exact(_rat(receipt["model_receipt"]["stationary_risk"], "receipt stationary risk"), stationary_risk, "receipt stationary risk")
    _exact([_rat(value, "receipt potential") for value in receipt["potential_receipt"]["values"]], potential, "receipt potential")
    _exact([_rat(value, "receipt residual") for value in receipt["potential_receipt"]["residual"]], residual, "receipt residual")
    _exact(_rat(receipt["potential_receipt"]["span"], "receipt span"), span, "receipt span")
    _exact(_rat(receipt["potential_receipt"]["residual_envelope"], "receipt residual envelope"), residual_envelope, "receipt residual envelope")
    _exact(_rat(receipt["potential_receipt"]["normalized_scale"], "receipt scale"), scale, "receipt scale")
    _exact(receipt["trace_alignment"]["suffix_edge_histogram"], suffix_histogram, "receipt suffix histogram")
    _exact(_rat(receipt["score_receipt"]["sum"], "receipt score sum"), score_sum, "receipt score sum")
    _exact(_rat(receipt["score_receipt"]["sum_squares"], "receipt score squares"), score_square_sum, "receipt score squares")
    _exact(
        [[_rat(value, "receipt score row sum") for value in row] for row in receipt["score_receipt"]["row_sums"]],
        score_row_sums,
        "receipt score row sums",
    )
    _exact(
        [[_rat(value, "receipt square-score row sum") for value in row] for row in receipt["score_receipt"]["row_sum_squares"]],
        score_square_row_sums,
        "receipt square-score row sums",
    )
    _exact(_rat(receipt["score_receipt"]["bessel_q"], "receipt Q"), bessel_q, "receipt Q")
    _exact(_rat(receipt["score_receipt"]["hybrid_first_branch_upper"], "receipt hybrid"), hybrid, "receipt hybrid")
    _exact(_rat(receipt["confidence_receipt"]["certified_upper_bound"], "receipt endpoint"), endpoint, "receipt endpoint")
    _exact(receipt["nonclaims"], spec["nonclaims"], "receipt nonclaims")
    _exact(
        receipt["dependency_hashes"],
        {role: _sha(raw) for role, (_path, raw) in sorted(files.items())},
        "receipt dependency hashes",
    )

    _exact(
        set(manifest),
        {
            "artifact_status",
            "generator",
            "independent_verifier",
            "inputs",
            "manifest_note",
            "nonclaims",
            "outputs",
            "receipt_version",
            "schema_version",
        },
        "receipt manifest keys",
    )
    _exact(manifest["artifact_status"], ARTIFACT_STATUS, "receipt manifest status")
    _exact(manifest["schema_version"], SCHEMA_VERSION, "receipt manifest schema")
    _exact(
        manifest["receipt_version"],
        "controlled-queue-known-kernel-receipt-v1",
        "receipt manifest version",
    )
    _exact(
        manifest["manifest_note"],
        "canonical JSON; the manifest is not recursively self-hashed",
        "receipt manifest note",
    )
    _exact(
        manifest["nonclaims"],
        [
            "not a good-event membership proof",
            "not a Lean decoder or SHA-256 proof for the trace binary",
            "not an unknown-kernel certificate",
        ],
        "receipt manifest nonclaims",
    )

    generator_row = _object(manifest["generator"], "receipt generator")
    _exact(
        set(generator_row),
        {"path", "revision", "sha256"},
        "receipt generator keys",
    )
    _exact(generator_row["path"], _display(GENERATOR), "receipt generator path")
    _exact(generator_row["revision"], GENERATOR_REVISION, "receipt generator revision")
    _exact(generator_row["sha256"], _sha(GENERATOR.read_bytes()), "receipt generator hash")
    verifier_row = _object(manifest["independent_verifier"], "receipt verifier")
    _exact(set(verifier_row), {"path", "sha256"}, "receipt verifier keys")
    _exact(verifier_row["path"], _display(Path(__file__)), "receipt verifier path")
    _exact(verifier_row["sha256"], _sha(Path(__file__).read_bytes()), "receipt verifier hash")

    input_rows = _manifest_rows_by_role(
        manifest["inputs"], {"receipt_input", *files.keys()}, "receipt manifest inputs"
    )
    _verify_manifest_row(
        input_rows["receipt_input"], input_path, input_raw, "receipt input row"
    )
    for role, (path, raw) in files.items():
        _verify_manifest_row(input_rows[role], path, raw, f"receipt input row {role}")

    output_rows = _manifest_rows_by_role(
        manifest["outputs"], {"receipt", "lean_data"}, "receipt manifest outputs"
    )
    _verify_manifest_row(
        output_rows["receipt"], receipt_path, receipt_raw, "receipt output row"
    )
    _verify_manifest_row(
        output_rows["lean_data"], lean_path, lean_raw, "Lean output row"
    )

    expected_lean = _render_expected_lean(
        receipt=receipt,
        invariant=invariant,
        risk=risk,
        potential=potential,
        residual=residual,
        histogram=suffix_histogram,
        score_row_sums=score_row_sums,
        score_square_row_sums=score_square_row_sums,
        span=span,
        reference_risk=reference_risk,
        scale=scale,
        residual_envelope=residual_envelope,
        stationary_risk=stationary_risk,
        score_sum=score_sum,
        score_square_sum=score_square_sum,
        bessel_q=bessel_q,
        hybrid=hybrid,
        endpoint=endpoint,
    )
    _exact(lean_raw, expected_lean, "independently rendered Lean data bytes")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--check", action="store_true", help="read-only verification mode")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        verify(args.input, args.receipt, args.manifest, args.lean)
    except (OSError, VerificationError, KeyError, IndexError, ValueError) as error:
        print(f"controlled-queue known-kernel receipt verification failed: {error}", file=sys.stderr)
        return 1
    print("verified controlled-queue known-kernel receipt and provenance")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
