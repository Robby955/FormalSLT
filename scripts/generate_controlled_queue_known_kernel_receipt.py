#!/usr/bin/env python3
"""Generate the deterministic known-kernel controlled-queue receipt.

The receipt binds one fixed policy--predictor atom, one depth-twelve potential,
and the physical transition suffix used by the controlled observation path.
All arithmetic is exact ``Fraction`` arithmetic.  The output is deterministic
preprocessing evidence; it does not assert membership in a theorem-produced
good event and it does not make the raw trace bytes part of Lean's kernel.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import sys
import tempfile
import unicodedata
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = (
    ROOT / "applications" / "controlled_queue" / "known-kernel-receipt-v1.json"
)
DEFAULT_RECEIPT = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "generated"
    / "known-kernel-receipt-v1.json"
)
DEFAULT_MANIFEST = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "generated"
    / "known-kernel-receipt-v1-manifest.json"
)
DEFAULT_LEAN = (
    ROOT
    / "FormalSLT"
    / "Applications"
    / "ControlledQueueKnownKernelReceiptData.lean"
)
DEFAULT_VERIFIER = ROOT / "scripts" / "verify_controlled_queue_known_kernel_receipt.py"

SCHEMA_VERSION = "controlled-queue-known-kernel-receipt-input-v1"
RECEIPT_VERSION = "controlled-queue-known-kernel-receipt-v1"
GENERATOR_REVISION = "controlled-queue-known-kernel-receipt-generator-v1"
ARTIFACT_STATUS = "DETERMINISTIC KNOWN-KERNEL RECEIPT"
INPUT_STATUS = "DETERMINISTIC KNOWN-KERNEL RECEIPT INPUT"
TRACE_MAGIC = bytes.fromhex("4351545256310000")
TRACE_HEADER = struct.Struct(">8sQ")
STATE_COUNT = 24
ACTION_COUNT = 2
HYPOTHESIS_COUNT = 12

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


class ReceiptError(ValueError):
    """Raised when a receipt input or dependency violates the frozen contract."""


def _reject_float(value: str) -> None:
    raise ReceiptError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise ReceiptError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ReceiptError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_booleans(value: Any, where: str) -> None:
    if isinstance(value, bool):
        raise ReceiptError(f"JSON booleans are forbidden at {where}")
    if isinstance(value, dict):
        for key, item in value.items():
            _reject_booleans(item, f"{where}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _reject_booleans(item, f"{where}[{index}]")


def parse_json_bytes(raw: bytes, where: str) -> Any:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
        return value
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReceiptError(f"invalid UTF-8 JSON in {where}: {error}") from error


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ReceiptError(f"{where} must be an object")
    return value


def _list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReceiptError(f"{where} must be an array")
    return value


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise ReceiptError(f"{where} must be {expected!r}, got {actual!r}")


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    if set(value) != expected:
        raise ReceiptError(
            f"{where} keys mismatch; missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def rational_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fraction(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise ReceiptError(f"{where} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ReceiptError(f"invalid rational at {where}: {value!r}") from error
    if rational_text(result) != value:
        raise ReceiptError(f"noncanonical rational at {where}: {value!r}")
    return result


def _resolve_bound_file(binding: dict[str, Any], where: str) -> tuple[Path, bytes]:
    _keys(binding, {"path", "sha256"}, where)
    path_text = binding["path"]
    digest = binding["sha256"]
    if not isinstance(path_text, str) or not isinstance(digest, str):
        raise ReceiptError(f"{where} path and sha256 must be strings")
    path = (ROOT / path_text).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as error:
        raise ReceiptError(f"{where} escapes the repository root") from error
    raw = path.read_bytes()
    _exact(sha256_bytes(raw), digest, f"{where}.sha256")
    return path, raw


def parse_input(path: Path) -> tuple[dict[str, Any], dict[str, tuple[Path, bytes]]]:
    raw = path.read_bytes()
    spec = _object(parse_json_bytes(raw, "receipt input"), "receipt input")
    _reject_booleans(spec, "receipt input")
    if raw != canonical_json_bytes(spec):
        raise ReceiptError("receipt input must use canonical JSON bytes")
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
    _exact(spec["schema_version"], SCHEMA_VERSION, "schema_version")
    _exact(spec["artifact_status"], INPUT_STATUS, "artifact_status")
    bindings = _object(spec["bindings"], "bindings")
    expected_bindings = {
        "model_input",
        "model_manifest",
        "model_tables",
        "trace_binary",
        "trace_counts",
        "trace_input",
        "trace_manifest",
    }
    _keys(bindings, expected_bindings, "bindings")
    binding_rows = {
        key: _object(bindings[key], f"bindings.{key}")
        for key in sorted(expected_bindings)
    }
    for key, binding in binding_rows.items():
        _keys(binding, {"path", "sha256"}, f"bindings.{key}")
        _exact(
            binding["path"],
            EXPECTED_BINDING_PATHS[key],
            f"bindings.{key}.path",
        )
    files = {
        key: _resolve_bound_file(binding_rows[key], f"bindings.{key}")
        for key in sorted(expected_bindings)
    }
    _validate_contract(spec)
    return spec, files


def _validate_contract(spec: dict[str, Any]) -> None:
    selection = _object(spec["selection"], "selection")
    _keys(
        selection,
        {
            "candidate_id",
            "candidate_index",
            "predictor_id",
            "predictor_index",
            "target_policy_id",
            "target_policy_index",
        },
        "selection",
    )
    _exact(selection["candidate_id"], "nominal", "selection.candidate_id")
    _exact(selection["candidate_index"], 1, "selection.candidate_index")
    _exact(
        selection["target_policy_id"],
        "queue_threshold",
        "selection.target_policy_id",
    )
    _exact(selection["target_policy_index"], 1, "selection.target_policy_index")
    _exact(
        selection["predictor_id"],
        "nominal_model_overload",
        "selection.predictor_id",
    )
    _exact(selection["predictor_index"], 2, "selection.predictor_index")

    potential = _object(spec["potential_contract"], "potential_contract")
    _keys(
        potential,
        {
            "centering_reference",
            "depth",
            "selected_potential_shift",
            "unselected_potential",
            "unselected_residual_envelope",
        },
        "potential_contract",
    )
    _exact(potential["centering_reference"], "uniform_physical_state_reference", "centering")
    _exact(potential["depth"], 12, "potential_contract.depth")
    potential_shift = _object(
        potential["selected_potential_shift"], "selected_potential_shift"
    )
    _keys(
        potential_shift,
        {"anchor_state", "definition"},
        "selected_potential_shift",
    )
    _exact(potential_shift["anchor_state"], 0, "potential anchor state")
    _exact(
        potential_shift["definition"],
        "h_shift(z) = h_raw(z) - h_raw(0)",
        "potential shift definition",
    )
    _exact(potential["unselected_potential"], "zero", "unselected potential")
    _exact(_fraction(potential["unselected_residual_envelope"], "unselected envelope"), Fraction(1), "unselected envelope")

    confidence = _object(spec["confidence_contract"], "confidence_contract")
    _keys(
        confidence,
        {
            "failure_budget",
            "importance_ratio_cap",
            "posterior",
            "risk_tilt",
            "risk_tilt_weight",
            "twelve_hypothesis_prior_mass",
        },
        "confidence_contract",
    )
    _exact(_fraction(confidence["failure_budget"], "failure budget"), Fraction(1, 40), "failure budget")
    _exact(_fraction(confidence["importance_ratio_cap"], "ratio cap"), Fraction(3, 2), "ratio cap")
    _exact(confidence["posterior"], "dirac_queue_threshold_nominal_model_overload", "posterior")
    _exact(_fraction(confidence["risk_tilt"], "risk tilt"), Fraction(1, 16), "risk tilt")
    _exact(_fraction(confidence["risk_tilt_weight"], "tilt weight"), Fraction(1), "tilt weight")
    _exact(_fraction(confidence["twelve_hypothesis_prior_mass"], "prior mass"), Fraction(1, 12), "prior mass")

    histogram = _object(spec["edge_histogram_contract"], "edge_histogram_contract")
    _keys(
        histogram,
        {
            "axes",
            "encoded_bytes",
            "flat_index",
            "positive_cells",
            "sha256",
            "shape",
            "total",
            "word_encoding",
        },
        "edge_histogram_contract",
    )
    _exact(histogram["axes"], ["current_state", "action", "next_state"], "histogram axes")
    _exact(histogram["shape"], [24, 2, 24], "histogram shape")
    _exact(histogram["flat_index"], "((current_state * 2 + action) * 24 + next_state)", "histogram flat index")
    _exact(histogram["word_encoding"], "unsigned 64-bit big-endian", "histogram encoding")
    _exact(histogram["encoded_bytes"], 9216, "histogram encoded bytes")
    _exact(histogram["total"], 199999, "histogram total")
    _exact(histogram["positive_cells"], 1152, "histogram positive cells")
    _exact(histogram["sha256"], "2a484e76850d41fa40e16bdb988bb24131a355800e503e283a26ad22b9d8a874", "histogram sha256")

    expected = _object(spec["expected_receipt"], "expected_receipt")
    _keys(
        expected,
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
        "expected_receipt",
    )
    for key, value in expected.items():
        _fraction(value, f"expected_receipt.{key}")

    alignment = _object(spec["trace_alignment"], "trace_alignment")
    _keys(
        alignment,
        {
            "controlled_observation",
            "controlled_observation_range",
            "excluded_transition",
            "initial_controlled_observation",
            "physical_transition_range",
            "score_index_range",
            "score_count",
            "source_horizon",
        },
        "trace_alignment",
    )
    _exact(alignment["controlled_observation"], "x_k = (A_k, S_{k+1})", "controlled observation")
    _exact(
        alignment["initial_controlled_observation"],
        {"action_index": 1, "physical_state_index": 1},
        "initial controlled observation",
    )
    _exact(
        alignment["controlled_observation_range"],
        {"start_inclusive": 0, "stop_exclusive": 200000},
        "controlled observation range",
    )
    _exact(
        alignment["score_index_range"],
        {"start_inclusive": 0, "stop_exclusive": 199999},
        "score index range",
    )
    _exact(
        alignment["physical_transition_range"],
        {"start_inclusive": 1, "stop_exclusive": 200000},
        "physical transition range",
    )
    _exact(
        alignment["excluded_transition"],
        {"action": 1, "current_state": 0, "next_state": 1, "physical_index": 0},
        "excluded transition",
    )
    _exact(alignment["score_count"], 199999, "score count")
    _exact(alignment["source_horizon"], 200000, "source horizon")

    _exact(
        _list(spec["nonclaims"], "nonclaims"),
        [
            "not a proof that the frozen trace belongs to the theorem-produced good event",
            "not a confidence guarantee conditional on this particular frozen trace",
            "not an unknown-kernel certificate",
            "not a data-selected candidate, potential depth, or potential catalog",
            "not a Lean decoder or SHA-256 verification of the raw trace bytes",
        ],
        "nonclaims",
    )


def _table_fraction_rows(rows: list[Any], value_key: str, where: str) -> list[list[Fraction]]:
    result = []
    for row_index, raw_row in enumerate(rows):
        row = _object(raw_row, f"{where}[{row_index}]")
        values = _list(row[value_key], f"{where}[{row_index}].{value_key}")
        result.append([
            _fraction(value, f"{where}[{row_index}].{value_key}[{index}]")
            for index, value in enumerate(values)
        ])
    return result


def _decode_trace(raw: bytes, horizon: int) -> tuple[bytes, bytes]:
    expected_size = TRACE_HEADER.size + (horizon + 1) + horizon + 4 * horizon * 4
    _exact(len(raw), expected_size, "trace binary byte length")
    magic, stored_horizon = TRACE_HEADER.unpack_from(raw)
    _exact(magic, TRACE_MAGIC, "trace magic")
    _exact(stored_horizon, horizon, "trace stored horizon")
    offset = TRACE_HEADER.size
    states = raw[offset : offset + horizon + 1]
    offset += horizon + 1
    actions = raw[offset : offset + horizon]
    if any(state >= STATE_COUNT for state in states):
        raise ReceiptError("trace contains an out-of-range state")
    if any(action >= ACTION_COUNT for action in actions):
        raise ReceiptError("trace contains an out-of-range action")
    return states, actions


def _solve_linear(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    n = len(rhs)
    augmented = [matrix[row][:] + [rhs[row]] for row in range(n)]
    for column in range(n):
        pivot = next((row for row in range(column, n) if augmented[row][column]), None)
        if pivot is None:
            raise ReceiptError(f"singular invariant system at column {column}")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [value / scale for value in augmented[column]]
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            if factor:
                augmented[row] = [
                    value - factor * pivot_value
                    for value, pivot_value in zip(augmented[row], augmented[column], strict=True)
                ]
    return [augmented[row][-1] for row in range(n)]


def _invariant_law(kernel: list[list[Fraction]]) -> list[Fraction]:
    equations: list[list[Fraction]] = []
    rhs: list[Fraction] = []
    for destination in range(STATE_COUNT - 1):
        equations.append([
            kernel[source][destination] - (Fraction(1) if source == destination else Fraction(0))
            for source in range(STATE_COUNT)
        ])
        rhs.append(Fraction(0))
    equations.append([Fraction(1)] * STATE_COUNT)
    rhs.append(Fraction(1))
    law = _solve_linear(equations, rhs)
    if any(value <= 0 for value in law) or sum(law) != 1:
        raise ReceiptError("computed invariant law is not a positive PMF")
    for destination in range(STATE_COUNT):
        if sum(law[source] * kernel[source][destination] for source in range(STATE_COUNT)) != law[destination]:
            raise ReceiptError(f"invariant balance failed at state {destination}")
    return law


def _mat_vec(kernel: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [
        sum((kernel[source][destination] * vector[destination] for destination in range(STATE_COUNT)), Fraction(0))
        for source in range(STATE_COUNT)
    ]


def _fraction_grid_text(values: Any) -> Any:
    if isinstance(values, Fraction):
        return rational_text(values)
    if isinstance(values, list):
        return [_fraction_grid_text(value) for value in values]
    return values


def _histogram_bytes(histogram: list[list[list[int]]]) -> bytes:
    return b"".join(
        struct.pack(">Q", histogram[state][action][destination])
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
        for destination in range(STATE_COUNT)
    )


def _verify_manifest_references(manifest: dict[str, Any], where: str) -> None:
    for collection in ("files", "inputs", "outputs"):
        if collection not in manifest:
            continue
        for index, raw_row in enumerate(_list(manifest[collection], f"{where}.{collection}")):
            row = _object(raw_row, f"{where}.{collection}[{index}]")
            path_text = row.get("path")
            digest = row.get("sha256")
            if not isinstance(path_text, str) or not isinstance(digest, str):
                raise ReceiptError(f"{where}.{collection}[{index}] lacks path/sha256")
            path = (ROOT / path_text).resolve()
            try:
                path.relative_to(ROOT.resolve())
            except ValueError as error:
                raise ReceiptError(f"{where}.{collection}[{index}] escapes the repository") from error
            raw = path.read_bytes()
            _exact(sha256_bytes(raw), digest, f"{where}.{collection}[{index}] sha256")
            if "bytes" in row:
                _exact(len(raw), row["bytes"], f"{where}.{collection}[{index}] bytes")
    for collection in ("generator", "independent_verifier"):
        if collection not in manifest:
            continue
        row = _object(manifest[collection], f"{where}.{collection}")
        path = (ROOT / row["path"]).resolve()
        raw = path.read_bytes()
        _exact(sha256_bytes(raw), row["sha256"], f"{where}.{collection} sha256")
    for index, raw_row in enumerate(manifest.get("generator_dependencies", [])):
        row = _object(raw_row, f"{where}.generator_dependencies[{index}]")
        path = (ROOT / row["path"]).resolve()
        _exact(
            sha256_bytes(path.read_bytes()),
            row["sha256"],
            f"{where}.generator_dependencies[{index}] sha256",
        )


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
    _exact(row["path"], expected_path, f"{where}.path")
    _exact(row["role"], expected_role, f"{where}.role")
    digest = row["sha256"]
    if (
        not isinstance(digest, str)
        or len(digest) != 64
        or any(character not in "0123456789abcdef" for character in digest)
    ):
        raise ReceiptError(f"{where}.sha256 must be a lowercase SHA-256 digest")
    if include_bytes and (
        isinstance(row["bytes"], bool)
        or not isinstance(row["bytes"], int)
        or row["bytes"] < 0
    ):
        raise ReceiptError(f"{where}.bytes must be a nonnegative integer")
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
        "model manifest.artifact_status",
    )
    _exact(
        model_manifest["schema_version"],
        "controlled-queue-input-v1",
        "model manifest.schema_version",
    )
    _exact(
        model_manifest["model_version"],
        "controlled-queue-v1",
        "model manifest.model_version",
    )
    _keys(
        _object(model_manifest["parameters"], "model manifest.parameters"),
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
        "model manifest.parameters",
    )
    _exact(
        model_manifest["nonclaims"],
        [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not a proof bridge",
        ],
        "model manifest.nonclaims",
    )
    model_generator = _object(model_manifest["generator"], "model manifest.generator")
    _keys(
        model_generator,
        {"path", "revision", "sha256"},
        "model manifest.generator",
    )
    _exact(
        model_generator["path"],
        MODEL_GENERATOR_PATH,
        "model manifest.generator.path",
    )
    _exact(
        model_generator["revision"],
        "controlled-queue-preprocess-v1",
        "model manifest.generator.revision",
    )
    model_files = _list(model_manifest["files"], "model manifest.files")
    _exact(len(model_files), 3, "model manifest.files length")
    model_input_row = _manifest_file_row(
        model_files[0],
        expected_path=EXPECTED_BINDING_PATHS["model_input"],
        expected_role="input",
        include_bytes=False,
        where="model manifest.files[0]",
    )
    model_tables_row = _manifest_file_row(
        model_files[1],
        expected_path=EXPECTED_BINDING_PATHS["model_tables"],
        expected_role="output",
        include_bytes=False,
        where="model manifest.files[1]",
    )
    _manifest_file_row(
        model_files[2],
        expected_path=MODEL_LEAN_PATH,
        expected_role="output",
        include_bytes=False,
        where="model manifest.files[2]",
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
        "trace manifest.artifact_status",
    )
    _exact(
        trace_manifest["schema_version"],
        "controlled-queue-trace-input-v1",
        "trace manifest.schema_version",
    )
    _exact(
        trace_manifest["trace_version"],
        "controlled-queue-trace-v1",
        "trace manifest.trace_version",
    )
    _exact(
        trace_manifest["manifest_note"],
        "the manifest is canonical JSON and is not recursively self-hashed",
        "trace manifest.manifest_note",
    )
    _keys(
        _object(trace_manifest["parameters"], "trace manifest.parameters"),
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
        "trace manifest.parameters",
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
        "trace manifest.nonclaims",
    )
    trace_generator = _object(trace_manifest["generator"], "trace manifest.generator")
    _keys(
        trace_generator,
        {"path", "revision", "sha256"},
        "trace manifest.generator",
    )
    _exact(
        trace_generator["path"],
        TRACE_GENERATOR_PATH,
        "trace manifest.generator.path",
    )
    _exact(
        trace_generator["revision"],
        "controlled-queue-trace-generator-v1",
        "trace manifest.generator.revision",
    )
    trace_verifier = _object(
        trace_manifest["independent_verifier"],
        "trace manifest.independent_verifier",
    )
    _keys(
        trace_verifier,
        {"path", "sha256"},
        "trace manifest.independent_verifier",
    )
    _exact(
        trace_verifier["path"],
        TRACE_VERIFIER_PATH,
        "trace manifest.independent_verifier.path",
    )
    trace_files = _list(trace_manifest["files"], "trace manifest.files")
    _exact(len(trace_files), 4, "trace manifest.files length")
    trace_input_row = _manifest_file_row(
        trace_files[0],
        expected_path=EXPECTED_BINDING_PATHS["trace_input"],
        expected_role="trace_input",
        include_bytes=False,
        where="trace manifest.files[0]",
    )
    trace_model_row = _manifest_file_row(
        trace_files[1],
        expected_path=EXPECTED_BINDING_PATHS["model_input"],
        expected_role="model_input",
        include_bytes=False,
        where="trace manifest.files[1]",
    )
    trace_binary_row = _manifest_file_row(
        trace_files[2],
        expected_path=EXPECTED_BINDING_PATHS["trace_binary"],
        expected_role="raw_trace_output",
        include_bytes=True,
        where="trace manifest.files[2]",
    )
    trace_counts_row = _manifest_file_row(
        trace_files[3],
        expected_path=EXPECTED_BINDING_PATHS["trace_counts"],
        expected_role="counts_output",
        include_bytes=True,
        where="trace manifest.files[3]",
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
        "trace manifest.generator_dependencies",
    )
    _exact(len(dependencies), 1, "trace manifest.generator_dependencies length")
    model_dependency = _object(
        dependencies[0],
        "trace manifest.generator_dependencies[0]",
    )
    _keys(
        model_dependency,
        {"path", "sha256"},
        "trace manifest.generator_dependencies[0]",
    )
    _exact(
        model_dependency,
        {"path": model_generator["path"], "sha256": model_generator["sha256"]},
        "trace manifest model-generator dependency",
    )

    _verify_manifest_references(model_manifest, "model manifest")
    _verify_manifest_references(trace_manifest, "trace manifest")


def build_receipt(spec: dict[str, Any], files: dict[str, tuple[Path, bytes]]) -> dict[str, Any]:
    tables_raw = files["model_tables"][1]
    tables = _object(parse_json_bytes(tables_raw, "model tables"), "model tables")
    trace_counts = _object(parse_json_bytes(files["trace_counts"][1], "trace counts"), "trace counts")
    model_manifest = _object(parse_json_bytes(files["model_manifest"][1], "model manifest"), "model manifest")
    trace_manifest = _object(parse_json_bytes(files["trace_manifest"][1], "trace manifest"), "trace manifest")
    _exact(tables_raw, canonical_json_bytes(tables), "canonical model-table bytes")
    _exact(files["trace_counts"][1], canonical_json_bytes(trace_counts), "canonical trace-count bytes")
    _exact(files["model_manifest"][1], canonical_json_bytes(model_manifest), "canonical model-manifest bytes")
    _exact(files["trace_manifest"][1], canonical_json_bytes(trace_manifest), "canonical trace-manifest bytes")
    _verify_upstream_manifests(spec, model_manifest, trace_manifest)

    candidates = _list(tables["candidate_kernels"], "candidate_kernels")
    policies = _list(tables["policies"], "policies")
    brier_tables = _list(tables["fixed_brier_loss"], "fixed_brier_loss")
    candidate = _object(candidates[1], "nominal candidate")
    policy = _object(policies[2], "queue-threshold policy")
    brier = _object(brier_tables[2], "nominal-model Brier table")
    _exact(candidate["id"], "nominal", "candidate id")
    _exact(policy["id"], "queue_threshold", "target-policy id")
    _exact(brier["id"], "nominal_model_overload", "predictor id")
    candidate_rows = _table_fraction_rows(
        _list(candidate["rows"], "candidate rows"), "probabilities", "candidate rows"
    )
    policy_rows = _table_fraction_rows(
        _list(policy["rows"], "policy rows"), "probabilities", "policy rows"
    )
    brier_rows = _table_fraction_rows(
        _list(brier["rows"], "Brier rows"), "losses", "Brier rows"
    )
    _exact(len(candidate_rows), STATE_COUNT * ACTION_COUNT, "candidate row count")
    _exact(len(policy_rows), STATE_COUNT, "policy row count")
    _exact(len(brier_rows), STATE_COUNT * ACTION_COUNT, "Brier row count")
    if any(len(row) != STATE_COUNT for row in candidate_rows + brier_rows):
        raise ReceiptError("candidate and Brier rows must contain 24 entries")
    if any(len(row) != ACTION_COUNT for row in policy_rows):
        raise ReceiptError("policy rows must contain two entries")

    kernel = [
        [
            sum(
                (policy_rows[state][action] * candidate_rows[2 * state + action][destination]
                 for action in range(ACTION_COUNT)),
                Fraction(0),
            )
            for destination in range(STATE_COUNT)
        ]
        for state in range(STATE_COUNT)
    ]
    row_risk = [
        sum(
            (
                policy_rows[state][action]
                * sum(
                    (candidate_rows[2 * state + action][destination]
                     * brier_rows[2 * state + action][destination]
                     for destination in range(STATE_COUNT)),
                    Fraction(0),
                )
                for action in range(ACTION_COUNT)
            ),
            Fraction(0),
        )
        for state in range(STATE_COUNT)
    ]
    uniform_mean = sum(row_risk, Fraction(0)) / STATE_COUNT
    centered = [value - uniform_mean for value in row_risk]
    potential = [Fraction(0)] * STATE_COUNT
    iterate = centered[:]
    depth = spec["potential_contract"]["depth"]
    for _step in range(depth):
        potential = [left + right for left, right in zip(potential, iterate, strict=True)]
        iterate = _mat_vec(kernel, iterate)
    shift = potential[spec["potential_contract"]["selected_potential_shift"]["anchor_state"]]
    potential = [value - shift for value in potential]
    span = max(potential) - min(potential)
    _exact(potential[0], Fraction(0), "shifted potential anchor")
    _exact(min(potential), Fraction(0), "shifted potential minimum")

    invariant = _invariant_law(kernel)
    stationary_risk = sum(
        (invariant[state] * row_risk[state] for state in range(STATE_COUNT)),
        Fraction(0),
    )
    next_potential = _mat_vec(kernel, potential)
    residual = [
        row_risk[state] + next_potential[state] - potential[state] - stationary_risk
        for state in range(STATE_COUNT)
    ]
    residual_envelope = max(abs(value) for value in residual)

    source_horizon = spec["trace_alignment"]["source_horizon"]
    states, actions = _decode_trace(files["trace_binary"][1], source_horizon)
    _exact(states[0], 0, "trace initial state")
    _exact((states[0], actions[0], states[1]), (0, 1, 1), "excluded first edge")
    _exact(
        (states[source_horizon - 1], actions[source_horizon - 1], states[source_horizon]),
        (6, 1, 1),
        "included terminal edge",
    )

    full_histogram = [
        [[0 for _destination in range(STATE_COUNT)] for _action in range(ACTION_COUNT)]
        for _state in range(STATE_COUNT)
    ]
    for time in range(source_horizon):
        full_histogram[states[time]][actions[time]][states[time + 1]] += 1
    _exact(full_histogram, trace_counts["counts"]["edge_counts"], "trace edge counts")

    physical_range = spec["trace_alignment"]["physical_transition_range"]
    first = physical_range["start_inclusive"]
    stop = physical_range["stop_exclusive"]
    histogram = [
        [[0 for _destination in range(STATE_COUNT)] for _action in range(ACTION_COUNT)]
        for _state in range(STATE_COUNT)
    ]
    for time in range(first, stop):
        histogram[states[time]][actions[time]][states[time + 1]] += 1
    score_count = spec["trace_alignment"]["score_count"]
    _exact(
        sum(sum(sum(row) for row in actions_) for actions_ in histogram),
        score_count,
        "suffix histogram total",
    )
    wrong_histogram = [
        [[0 for _destination in range(STATE_COUNT)] for _action in range(ACTION_COUNT)]
        for _state in range(STATE_COUNT)
    ]
    for time in range(0, score_count):
        wrong_histogram[states[time]][actions[time]][states[time + 1]] += 1
    if histogram == wrong_histogram:
        raise ReceiptError("correct and off-by-one suffix histograms unexpectedly agree")
    histogram_raw = _histogram_bytes(histogram)
    histogram_contract = spec["edge_histogram_contract"]
    _exact(len(histogram_raw), histogram_contract["encoded_bytes"], "histogram byte length")
    _exact(
        sum(
            1
            for state_rows in histogram
            for action_row in state_rows
            for count in action_row
            if count > 0
        ),
        histogram_contract["positive_cells"],
        "histogram positive-cell count",
    )
    _exact(sha256_bytes(histogram_raw), histogram_contract["sha256"], "histogram sha256")
    full_histogram_sha256 = sha256_bytes(_histogram_bytes(full_histogram))
    wrong_histogram_sha256 = sha256_bytes(_histogram_bytes(wrong_histogram))
    _exact(
        wrong_histogram_sha256,
        "1f29382a3b672ea83c66fc9f7bc910c0097c3fb974286a2959395fa041cb65bb",
        "off-by-one histogram sha256",
    )
    _exact(
        full_histogram_sha256,
        "f49a5bdcc9789270b07b80fe2b1c30f81991259d9d273c755ce9d64f2b017ee8",
        "full histogram sha256",
    )

    ratio_cap = _fraction(spec["confidence_contract"]["importance_ratio_cap"], "ratio cap")
    behavior_mass = Fraction(1, 2)
    normalized_scale = ratio_cap * (1 + 2 * span)
    observed_score = [
        [
            [
                (policy_rows[state][action] / behavior_mass)
                * (brier_rows[2 * state + action][destination]
                   + potential[destination] - potential[state] + span)
                / normalized_scale
                for destination in range(STATE_COUNT)
            ]
            for action in range(ACTION_COUNT)
        ]
        for state in range(STATE_COUNT)
    ]
    if any(
        value < 0 or value > 1
        for state_rows in observed_score
        for action_row in state_rows
        for value in action_row
    ):
        raise ReceiptError("normalized observed score escaped [0,1]")
    score_row_sums = [
        [
            sum(
                (
                    histogram[state][action][destination]
                    * observed_score[state][action][destination]
                    for destination in range(STATE_COUNT)
                ),
                Fraction(0),
            )
            for action in range(ACTION_COUNT)
        ]
        for state in range(STATE_COUNT)
    ]
    score_square_row_sums = [
        [
            sum(
                (
                    histogram[state][action][destination]
                    * observed_score[state][action][destination] ** 2
                    for destination in range(STATE_COUNT)
                ),
                Fraction(0),
            )
            for action in range(ACTION_COUNT)
        ]
        for state in range(STATE_COUNT)
    ]
    score_sum = sum(
        (value for state_rows in score_row_sums for value in state_rows),
        Fraction(0),
    )
    score_square_sum = sum(
        (value for state_rows in score_square_row_sums for value in state_rows),
        Fraction(0),
    )
    direct_scores = [
        observed_score[states[time]][actions[time]][states[time + 1]]
        for time in range(first, stop)
    ]
    _exact(sum(direct_scores, Fraction(0)), score_sum, "direct score sum")
    _exact(
        sum((value * value for value in direct_scores), Fraction(0)),
        score_square_sum,
        "direct score-square sum",
    )

    n = Fraction(score_count)
    bessel_q = score_square_sum - score_sum * score_sum / n
    hybrid_upper = Fraction(1, 2) + Fraction(3, 2) * bessel_q
    risk_tilt = _fraction(spec["confidence_contract"]["risk_tilt"], "risk tilt")
    certified_log_cost_upper = Fraction(9)
    certified_psi_upper = Fraction(1, 240)
    certified_upper = (
        normalized_scale
        * (
            score_sum / n
            + (certified_log_cost_upper + certified_psi_upper * hybrid_upper)
            / (n * risk_tilt)
        )
        - span
        + residual_envelope
    )
    if certified_upper >= Fraction(7, 100):
        raise ReceiptError(f"certified upper bound is not below 7/100: {certified_upper}")
    expected_values = {
        "bessel_q": bessel_q,
        "certified_upper_bound": certified_upper,
        "hybrid_first_branch_upper": hybrid_upper,
        "potential_span": span,
        "residual_envelope": residual_envelope,
        "score_sum": score_sum,
        "score_sum_squares": score_square_sum,
        "stationary_risk": stationary_risk,
    }
    for key, actual in expected_values.items():
        _exact(
            actual,
            _fraction(spec["expected_receipt"][key], f"expected_receipt.{key}"),
            f"computed {key}",
        )

    return {
        "artifact_status": ARTIFACT_STATUS,
        "receipt_version": RECEIPT_VERSION,
        "schema_version": SCHEMA_VERSION,
        "selection": spec["selection"],
        "trace_alignment": {
            **spec["trace_alignment"],
            "excluded_edge": [states[0], actions[0], states[1]],
            "included_terminal_edge": [
                states[source_horizon - 1],
                actions[source_horizon - 1],
                states[source_horizon],
            ],
            "suffix_edge_histogram": histogram,
            "suffix_edge_histogram_sha256": sha256_bytes(histogram_raw),
            "full_edge_histogram_sha256": full_histogram_sha256,
            "off_by_one_edge_histogram_sha256": wrong_histogram_sha256,
            "off_by_one_histogram_is_distinct": True,
        },
        "model_receipt": {
            "target_kernel": "queue_threshold policy mixed with nominal candidate",
            "stationary_law": _fraction_grid_text(invariant),
            "stationary_risk": rational_text(stationary_risk),
            "uniform_reference_row_risk_mean": rational_text(uniform_mean),
            "selected_row_risk": _fraction_grid_text(row_risk),
        },
        "potential_receipt": {
            "depth": depth,
            "shift": rational_text(shift),
            "values": _fraction_grid_text(potential),
            "span": rational_text(span),
            "residual": _fraction_grid_text(residual),
            "residual_envelope": rational_text(residual_envelope),
            "normalized_scale": rational_text(normalized_scale),
        },
        "score_receipt": {
            "row_sums": _fraction_grid_text(score_row_sums),
            "row_sum_squares": _fraction_grid_text(score_square_row_sums),
            "sum": rational_text(score_sum),
            "sum_squares": rational_text(score_square_sum),
            "bessel_q": rational_text(bessel_q),
            "hybrid_first_branch_upper": rational_text(hybrid_upper),
        },
        "confidence_receipt": {
            **spec["confidence_contract"],
            "log_cost_identity": "log(12) + log(40) = log(480)",
            "certified_log_cost_upper": rational_text(certified_log_cost_upper),
            "certified_psi_upper": rational_text(certified_psi_upper),
            "certified_upper_bound": rational_text(certified_upper),
            "certified_threshold": "7/100",
            "coverage_statement": "the theorem-generated event has complement outer mass at most 1/40",
        },
        "dependency_hashes": {
            key: sha256_bytes(raw) for key, (_path, raw) in sorted(files.items())
        },
        "nonclaims": spec["nonclaims"],
    }


def _lean_rat(text_value: str) -> str:
    value = Fraction(text_value)
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
    return "[\n" + ",\n".join(f"{pad}{row}" for row in rows) + "\n" + " " * (indent - 2) + "]"


def _render_nested_text(value: Any, indent: int = 2) -> str:
    if isinstance(value, str):
        return value
    rows = [_render_nested_text(item, indent + 2) for item in value]
    if not rows:
        return "[]"
    pad = " " * indent
    return "[\n" + ",\n".join(f"{pad}{row}" for row in rows) + "\n" + " " * (indent - 2) + "]"


def render_lean(receipt: dict[str, Any]) -> bytes:
    potential = [_lean_rat(value) for value in receipt["potential_receipt"]["values"]]
    residual = [_lean_rat(value) for value in receipt["potential_receipt"]["residual"]]
    invariant = [_lean_rat(value) for value in receipt["model_receipt"]["stationary_law"]]
    row_risk = [_lean_rat(value) for value in receipt["model_receipt"]["selected_row_risk"]]
    score_row_sums = [
        [_lean_rat(value) for value in row]
        for row in receipt["score_receipt"]["row_sums"]
    ]
    score_square_row_sums = [
        [_lean_rat(value) for value in row]
        for row in receipt["score_receipt"]["row_sum_squares"]
    ]
    histogram = receipt["trace_alignment"]["suffix_edge_histogram"]
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
        f"  | {state}, {action} => {score_row_sums[state][action]}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    score_square_row_branches = "\n".join(
        f"  | {state}, {action} => {score_square_row_sums[state][action]}"
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
def sourceHorizon : Nat := {receipt['trace_alignment']['source_horizon']}

/-- Number of controlled-path scores in the aligned suffix. -/
def receiptHorizon : Nat := {receipt['trace_alignment']['score_count']}

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
def selectedPotentialTable : List ℚ := {_render_list(potential)}

/-- Exact selected residual in physical-state order. -/
def selectedResidualTable : List ℚ := {_render_list(residual)}

/-- Exact selected invariant law in physical-state order. -/
def selectedStationaryLawTable : List ℚ := {_render_list(invariant)}

/-- Exact selected row risk in physical-state order. -/
def selectedRowRiskTable : List ℚ := {_render_list(row_risk)}

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
def selectedScoreRowSums : List (List ℚ) := {_render_nested_text(score_row_sums)}

/-- Exact squared-score subtotal for each source-state/action row. -/
def selectedScoreSquareRowSums : List (List ℚ) := {_render_nested_text(score_square_row_sums)}

/-- Exact potential span. -/
def selectedPotentialSpan : ℚ := {_lean_rat(receipt['potential_receipt']['span'])}

/-- Exact uniform-reference average of the selected row risk. -/
def selectedUniformReferenceRisk : ℚ := {_lean_rat(receipt['model_receipt']['uniform_reference_row_risk_mean'])}

/-- Exact affine normalization `C * (1 + 2B)`. -/
def selectedNormalizedScale : ℚ := {_lean_rat(receipt['potential_receipt']['normalized_scale'])}

/-- Exact selected pointwise residual envelope. -/
def selectedResidualEnvelope : ℚ := {_lean_rat(receipt['potential_receipt']['residual_envelope'])}

/-- Exact selected stationary Brier risk. -/
def selectedStationaryRisk : ℚ := {_lean_rat(receipt['model_receipt']['stationary_risk'])}

/-- Sum of the 199999 normalized observed scores. -/
def observedScoreSum : ℚ := {_lean_rat(receipt['score_receipt']['sum'])}

/-- Sum of squares of the normalized observed scores. -/
def observedScoreSquareSum : ℚ := {_lean_rat(receipt['score_receipt']['sum_squares'])}

/-- Exact Bessel statistic derived from the two score summaries. -/
def observedScoreBesselQ : ℚ := {_lean_rat(receipt['score_receipt']['bessel_q'])}

/-- First-branch hybrid-Bessel upper bound. -/
def observedHybridPenaltyUpper : ℚ := {_lean_rat(receipt['score_receipt']['hybrid_first_branch_upper'])}

/-- Exact rational upper bound obtained from `log(480) ≤ 9` and
`psi(1/16) ≤ 1/240`. -/
def certifiedKnownKernelUpperBound : ℚ := {_lean_rat(receipt['confidence_receipt']['certified_upper_bound'])}

end FormalSLT.Applications.ControlledQueueKnownKernelReceiptData
'''
    return content.encode()


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


def _validate_artifact_paths(
    input_path: Path,
    receipt_path: Path,
    manifest_path: Path,
    lean_path: Path,
) -> None:
    outputs = {
        "receipt": receipt_path.resolve(),
        "manifest": manifest_path.resolve(),
        "lean": lean_path.resolve(),
    }
    output_items = list(outputs.items())
    output_aliases = [
        (left_role, right_role)
        for index, (left_role, left_path) in enumerate(output_items)
        for right_role, right_path in output_items[index + 1 :]
        if _same_file_target(left_path, right_path)
    ]
    if output_aliases:
        raise ReceiptError(
            f"output paths must be distinct: aliases={output_aliases}, paths={outputs}"
        )

    _spec, files = parse_input(input_path)
    protected = {
        "receipt_input": input_path.resolve(),
        "generator": Path(__file__).resolve(),
        "independent_verifier": DEFAULT_VERIFIER.resolve(),
        **{role: path.resolve() for role, (path, _raw) in files.items()},
    }
    collisions = [
        f"{output_role}={output_path} aliases {input_role}"
        for output_role, output_path in outputs.items()
        for input_role, input_path_resolved in protected.items()
        if _same_file_target(output_path, input_path_resolved)
    ]
    if collisions:
        raise ReceiptError("output path aliases protected input: " + "; ".join(collisions))


def build_manifest(
    input_path: Path,
    input_raw: bytes,
    files: dict[str, tuple[Path, bytes]],
    receipt_path: Path,
    receipt_raw: bytes,
    lean_path: Path,
    lean_raw: bytes,
) -> dict[str, Any]:
    generator = Path(__file__).resolve()
    verifier = DEFAULT_VERIFIER.resolve()
    if not verifier.is_file():
        raise ReceiptError(f"independent verifier is missing: {verifier}")
    return {
        "artifact_status": ARTIFACT_STATUS,
        "receipt_version": RECEIPT_VERSION,
        "schema_version": SCHEMA_VERSION,
        "generator": {
            "path": _display(generator),
            "revision": GENERATOR_REVISION,
            "sha256": sha256_bytes(generator.read_bytes()),
        },
        "independent_verifier": {
            "path": _display(verifier),
            "sha256": sha256_bytes(verifier.read_bytes()),
        },
        "inputs": [
            {
                "role": "receipt_input",
                "path": _display(input_path),
                "bytes": len(input_raw),
                "sha256": sha256_bytes(input_raw),
            }
        ]
        + [
            {
                "role": role,
                "path": _display(path),
                "bytes": len(raw),
                "sha256": sha256_bytes(raw),
            }
            for role, (path, raw) in sorted(files.items())
        ],
        "outputs": [
            {
                "role": "receipt",
                "path": _display(receipt_path),
                "bytes": len(receipt_raw),
                "sha256": sha256_bytes(receipt_raw),
            },
            {
                "role": "lean_data",
                "path": _display(lean_path),
                "bytes": len(lean_raw),
                "sha256": sha256_bytes(lean_raw),
            },
        ],
        "manifest_note": "canonical JSON; the manifest is not recursively self-hashed",
        "nonclaims": [
            "not a good-event membership proof",
            "not a Lean decoder or SHA-256 proof for the trace binary",
            "not an unknown-kernel certificate",
        ],
    }


def expected_artifacts(
    input_path: Path,
    receipt_path: Path,
    manifest_path: Path,
    lean_path: Path,
) -> tuple[bytes, bytes, bytes]:
    input_raw = input_path.read_bytes()
    spec, files = parse_input(input_path)
    receipt = build_receipt(spec, files)
    receipt_raw = canonical_json_bytes(receipt)
    lean_raw = render_lean(receipt)
    manifest = build_manifest(
        input_path,
        input_raw,
        files,
        receipt_path,
        receipt_raw,
        lean_path,
        lean_raw,
    )
    return receipt_raw, canonical_json_bytes(manifest), lean_raw


def _write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(data)
        handle.flush()
    temporary.replace(path)


def _check(path: Path, expected: bytes) -> bool:
    if not path.is_file():
        print(f"missing generated artifact: {_display(path)}", file=sys.stderr)
        return False
    if path.read_bytes() != expected:
        print(f"stale generated artifact: {_display(path)}", file=sys.stderr)
        return False
    return True


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--check", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        _validate_artifact_paths(
            args.input, args.receipt, args.manifest, args.lean
        )
        receipt_raw, manifest_raw, lean_raw = expected_artifacts(
            args.input, args.receipt, args.manifest, args.lean
        )
        if args.check:
            ok = all(
                (
                    _check(args.receipt, receipt_raw),
                    _check(args.manifest, manifest_raw),
                    _check(args.lean, lean_raw),
                )
            )
            if not ok:
                return 1
            print("controlled-queue known-kernel receipt is current")
            return 0
        _write_atomic(args.receipt, receipt_raw)
        _write_atomic(args.lean, lean_raw)
        _write_atomic(args.manifest, manifest_raw)
        print(
            "generated controlled-queue known-kernel receipt, manifest, and Lean data"
        )
        return 0
    except (OSError, ReceiptError, KeyError, IndexError, ValueError) as error:
        print(f"controlled-queue known-kernel receipt failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
