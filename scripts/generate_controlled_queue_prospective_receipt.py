#!/usr/bin/env python3
"""Generate the frozen prospective controlled-queue numerical receipt.

This program is deliberately offline.  It consumes the already generated and
independently replayable prospective trace, reduces it by the preregistered
exact-rational rules, renders a bounded-arithmetic Lean receipt module, and writes a
receipt manifest last.  It never fetches registration or beacon data, never
chooses an analysis after seeing the path, and never establishes that the named
path belongs to a theorem-produced good event.

During code freeze the default trace inputs do not exist, so invoking the tool
without future registered inputs fails before creating an artifact.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
import unicodedata
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Iterable, NoReturn, Sequence


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


ROOT = Path(__file__).resolve().parents[1]
CONTROLLED_QUEUE = ROOT / "applications" / "controlled_queue"
PROSPECTIVE = CONTROLLED_QUEUE / "prospective"
GENERATED = PROSPECTIVE / "generated"

DEFAULT_PROTOCOL = CONTROLLED_QUEUE / "structured-ope-protocol-v1.json"
DEFAULT_TRACE = GENERATED / "structured-ope-trace-v1.bin"
DEFAULT_COUNTS = GENERATED / "structured-ope-trace-v1-counts.json"
DEFAULT_TRACE_MANIFEST = GENERATED / "structured-ope-trace-v1-manifest.json"
DEFAULT_MODEL_INPUT = CONTROLLED_QUEUE / "model-v1.json"
DEFAULT_MODEL_MANIFEST = CONTROLLED_QUEUE / "generated" / "model-v1-manifest.json"
DEFAULT_MODEL_TABLES = CONTROLLED_QUEUE / "generated" / "model-v1-tables.json"
DEFAULT_SELECTED_DATA = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueueKnownKernelReceiptData.lean"
)
DEFAULT_KNOWN_KERNEL_SOURCE = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueueKnownKernelReceipt.lean"
)
DEFAULT_PERSISTENCE_SOURCE = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueuePersistenceConfidence.lean"
)
DEFAULT_STRUCTURED_SOURCE = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueueStructuredOPE.lean"
)
DEFAULT_SHARP_STRUCTURED_SOURCE = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueueSharpStructuredOPE.lean"
)
DEFAULT_SHARP_RECEIPT_CORE = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueueSharpStructuredReceiptCore.lean"
)
DEFAULT_RECEIPT = GENERATED / "structured-ope-receipt-v1.json"
DEFAULT_RECEIPT_MANIFEST = GENERATED / "structured-ope-receipt-v1-manifest.json"
DEFAULT_LEAN = (
    ROOT / "FormalSLT" / "Applications" / "ControlledQueueProspectiveStructuredOPEData.lean"
)
DEFAULT_RECEIPT_VERIFIER = ROOT / "scripts" / "verify_controlled_queue_prospective_receipt.py"

PROTOCOL_PATH = "applications/controlled_queue/structured-ope-protocol-v1.json"
TRACE_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1.bin"
)
COUNTS_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-counts.json"
)
TRACE_MANIFEST_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-manifest.json"
)
RECEIPT_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1.json"
)
RECEIPT_MANIFEST_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1-manifest.json"
)
LEAN_PATH = "FormalSLT/Applications/ControlledQueueProspectiveStructuredOPEData.lean"
MODEL_INPUT_PATH = "applications/controlled_queue/model-v1.json"
MODEL_MANIFEST_PATH = "applications/controlled_queue/generated/model-v1-manifest.json"
MODEL_TABLES_PATH = "applications/controlled_queue/generated/model-v1-tables.json"
SELECTED_DATA_PATH = "FormalSLT/Applications/ControlledQueueKnownKernelReceiptData.lean"
KNOWN_KERNEL_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean"
PERSISTENCE_SOURCE_PATH = "FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean"
STRUCTURED_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueStructuredOPE.lean"
SHARP_STRUCTURED_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueSharpStructuredOPE.lean"
SHARP_RECEIPT_CORE_PATH = "FormalSLT/Applications/ControlledQueueSharpStructuredReceiptCore.lean"
GENERATOR_PATH = "scripts/generate_controlled_queue_prospective_receipt.py"
VERIFIER_PATH = "scripts/verify_controlled_queue_prospective_receipt.py"

PROTOCOL_SHA256 = "070519615ba7cdaf0198a72a03ab6f691a7ff9b37c2eaa97a363d7fd4c3bf153"
PROTOCOL_COMMIT = "65d8d56245e3862821fce09bcf30b017f03d2baa"
PROTOCOL_TREE = "8dbe01780fd2cec94b8b954f6ef1c8c210afee53"
PROTOCOL_SCHEMA = "controlled-queue-structured-ope-preregistration-v1"
PROTOCOL_VERSION = "controlled-queue-structured-ope-protocol-v1"
TRACE_COUNTS_SCHEMA = "controlled-queue-prospective-trace-counts-v1"
TRACE_MANIFEST_SCHEMA = "controlled-queue-prospective-trace-manifest-v1"
TRACE_VERSION = "controlled-queue-prospective-trace-v1"
RECEIPT_SCHEMA = "controlled-queue-prospective-structured-ope-receipt-v1"
RECEIPT_MANIFEST_SCHEMA = "controlled-queue-prospective-receipt-manifest-v1"
RECEIPT_VERSION = "controlled-queue-prospective-structured-ope-v1"
GENERATOR_REVISION = "controlled-queue-prospective-receipt-generator-v1"
ARTIFACT_STATUS = "PROSPECTIVE NUMERICAL RECEIPT - CONDITIONAL PATHWISE CERTIFICATES"

HORIZON = 200_000
STATE_COUNT = 24
ACTION_COUNT = 2
AUGMENTED_COUNT = 48
HYPOTHESIS_COUNT = 12
IMPORTANCE_CAP = Fraction(3, 2)
BEHAVIOR_MASS = Fraction(1, 2)
TRUE_GAMMA = Fraction(149, 200)
CANDIDATE_IDS = ("low", "nominal", "high")
CANDIDATE_GAMMAS = (Fraction(5, 8), Fraction(3, 4), Fraction(7, 8))
CANDIDATE_HITS = (Fraction(41, 64), Fraction(73, 96), Fraction(169, 192))
DEPTHS = (0, 1, 2, 3, 5, 8, 12)
TILTS = (Fraction(1, 16), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2))
PSI_UPPER = {
    Fraction(1, 16): Fraction(1, 480),
    Fraction(1, 8): Fraction(1, 112),
    Fraction(1, 4): Fraction(1, 24),
    Fraction(1, 2): Fraction(1, 4),
    Fraction(1, 64): Fraction(1, 8064),
}
PRIMARY_B = Fraction(390176269054599, 2251799813685248)
PRIMARY_DRIFT = Fraction(58989951, 9007199254740992)
PRIMARY_SENSITIVITY = Fraction(831542406207231, 3236962232172544)
PRIMARY_THRESHOLD = Fraction(1, 10)

BINARY_MAGIC = b"FSLTCQSP1\n"
BINARY_HEADER = struct.Struct(">10sQQQ")
BINARY_BYTES = 400_036

SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
GIT_RE = re.compile(r"[0-9a-f]{40}\Z")

ROW_ORDER = (
    "selected_h12_sharp_structured_eb",
    "adaptive_d1_21_atom_eb",
    "oracle_true_kernel_selected_h12_eb",
    "generic_d1_m12_structured_eb",
    "generic_d1_m5_structured_eb",
    "selected_h12_nonvariance_fixed_range",
    "unstructured_4608_coordinate_eb",
)
ROW_FIELDS = {
    "endpoint_id",
    "theorem_or_event",
    "certification_status",
    "empirical_corrected_score",
    "risk_statistical_correction",
    "persistence_or_transition_radius",
    "candidate_or_truncation_residual",
    "total_certified_rhs",
    "confidence_allocation",
    "selected_indices_or_fixed_settings",
    "vacuity_and_threshold_status",
}

NONCLAIMS = [
    "not proof that the named path belongs to a theorem-produced good event",
    "not Lean verification of raw bytes, SHA-256, a drand signature, or an OSF timestamp",
    "not a confidence certificate for the oracle true-kernel PLANNED_NOT_CHECKED row",
    "not a confidence certificate for the fixed-range PLANNED_NOT_CHECKED row",
    "not stationary target-policy certification for the two causal Beta predictors",
    "not a family-membership test or a result outside the frozen refresh family",
]


class ProspectiveReceiptError(ValueError):
    """Raised when a frozen receipt input or invariant fails."""


def _fail(message: str) -> NoReturn:
    raise ProspectiveReceiptError(message)


def _reject_float(value: str) -> NoReturn:
    _fail(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> NoReturn:
    _fail(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _fail(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json_bytes(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProspectiveReceiptError(f"invalid UTF-8 JSON in {where}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def parse_canonical_object(raw: bytes, where: str) -> dict[str, Any]:
    value = _object(parse_json_bytes(raw, where), where)
    _exact(raw, canonical_json_bytes(value), f"canonical {where} bytes")
    return value


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rational_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def decimal_text(value: Fraction) -> str:
    """Fifteen-place, exact-source, half-even decimal display."""

    scale = 10**15
    scaled_numerator = abs(value.numerator) * scale
    quotient, remainder = divmod(scaled_numerator, value.denominator)
    doubled_remainder = 2 * remainder
    if doubled_remainder > value.denominator or (
        doubled_remainder == value.denominator and quotient % 2 == 1
    ):
        quotient += 1
    if value.numerator < 0:
        quotient = -quotient
    absolute = abs(quotient)
    integer_part, fractional_part = divmod(absolute, scale)
    sign = "-" if quotient < 0 else ""
    return f"{sign}{integer_part}.{fractional_part:015d}"


def _balanced_fraction_add(
    partials: list[Fraction | None], value: Fraction
) -> None:
    """Add exactly while keeping intermediate denominators in a balanced tree."""

    level = 0
    while level < len(partials) and partials[level] is not None:
        value = partials[level] + value
        partials[level] = None
        level += 1
    if level == len(partials):
        partials.append(value)
    else:
        partials[level] = value


def _balanced_fraction_total(partials: Sequence[Fraction | None]) -> Fraction:
    return sum((value for value in partials if value is not None), Fraction(0))


def number(value: Fraction | int) -> dict[str, str]:
    exact = value if isinstance(value, Fraction) else Fraction(value)
    return {"rational": rational_text(exact), "decimal": decimal_text(exact)}


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        _fail(f"{where} must be an object")
    return value


def _array(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        _fail(f"{where} must be an array")
    return value


def _string(value: Any, where: str) -> str:
    if not isinstance(value, str):
        _fail(f"{where} must be a string")
    return value


def _integer(value: Any, where: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        _fail(f"{where} must be an integer, not a JSON boolean")
    if minimum is not None and value < minimum:
        _fail(f"{where} must be at least {minimum}")
    return value


def _boolean(value: Any, where: str) -> bool:
    if type(value) is not bool:
        _fail(f"{where} must be a boolean")
    return value


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    if set(value) != expected:
        _fail(
            f"{where} keys mismatch; missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )


def _exact(actual: Any, expected: Any, where: str) -> None:
    scalar = isinstance(expected, (bool, int, str, bytes)) or expected is None
    if actual != expected or (scalar and type(actual) is not type(expected)):
        _fail(f"{where} mismatch: expected {expected!r}, got {actual!r}")


def _fraction(value: Any, where: str) -> Fraction:
    text = _string(value, where)
    try:
        result = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise ProspectiveReceiptError(f"invalid rational at {where}: {text!r}") from error
    _exact(text, rational_text(result), f"canonical {where}")
    return result


def _digest(value: Any, where: str) -> str:
    text = _string(value, where)
    if SHA256_RE.fullmatch(text) is None:
        _fail(f"{where} must be a lowercase SHA-256 digest")
    return text


def _oid(value: Any, where: str) -> str:
    text = _string(value, where)
    if GIT_RE.fullmatch(text) is None:
        _fail(f"{where} must be a lowercase Git object id")
    return text


def _read(path: Path, where: str) -> bytes:
    try:
        return path.read_bytes()
    except OSError as error:
        raise ProspectiveReceiptError(f"cannot read {where} at {path}: {error}") from error


def _git_show(commit: str, path_text: str) -> bytes:
    try:
        completed = subprocess.run(
            ["git", "-C", str(ROOT), "show", f"{commit}:{path_text}"],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin", "GIT_TERMINAL_PROMPT": "0"},
        )
    except OSError as error:
        raise ProspectiveReceiptError(f"cannot execute Git provenance check: {error}") from error
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        _fail(f"Git provenance check failed for {commit}:{path_text}: {detail}")
    return completed.stdout


def _verify_code_freeze_source(commit: str, path: Path, raw: bytes, role: str) -> None:
    path_text = _display(path)
    committed = _git_show(commit, path_text)
    _exact(committed, raw, f"code-freeze committed bytes for {role}")


def _display(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def _manifest_row(role: str, path: Path, raw: bytes) -> dict[str, Any]:
    return {"bytes": len(raw), "path": _display(path), "role": role, "sha256": sha256_bytes(raw)}


def _fraction_grid(value: Any) -> Any:
    if isinstance(value, Fraction):
        return rational_text(value)
    if isinstance(value, list):
        return [_fraction_grid(item) for item in value]
    if isinstance(value, tuple):
        return [_fraction_grid(item) for item in value]
    return value


def _number_grid(value: Any) -> Any:
    if isinstance(value, Fraction):
        return number(value)
    if isinstance(value, list):
        return [_number_grid(item) for item in value]
    if isinstance(value, tuple):
        return [_number_grid(item) for item in value]
    return value


def validate_protocol(raw: bytes) -> dict[str, Any]:
    _exact(sha256_bytes(raw), PROTOCOL_SHA256, "frozen protocol SHA-256")
    protocol = parse_canonical_object(raw, "protocol")
    _exact(protocol.get("schema_version"), PROTOCOL_SCHEMA, "protocol schema")
    _exact(protocol.get("protocol_version"), PROTOCOL_VERSION, "protocol version")
    _exact(protocol.get("artifact_status"), "PROSPECTIVE PROTOCOL ONLY - NO TRACE OR RESULT", "protocol status")
    _exact(protocol["data_generation"]["horizon"], HORIZON, "protocol horizon")
    _exact(protocol["data_generation"]["true_gamma"], "149/200", "protocol true gamma")
    _exact(protocol["reporting_contract"]["row_order"], list(ROW_ORDER), "protocol row order")
    _exact(
        set(protocol["reporting_contract"]["required_fields_per_row"]),
        ROW_FIELDS,
        "protocol row fields",
    )
    _exact(
        protocol["receipt_arithmetic_contract"]["decimal_display"],
        {"digits_after_decimal": 15, "rounding": "ROUND_HALF_EVEN", "source": "authoritative exact reduced rational only"},
        "decimal display contract",
    )
    _exact(
        protocol["receipt_arithmetic_contract"]["hybrid_bessel_upper"],
        "always 1/2 + (3/2)*Q where Q = sum_sq - sum^2/n; never evaluate or data-select the harmonic branch",
        "hybrid branch contract",
    )
    primary = protocol["primary_endpoint"]
    _exact(_fraction(primary["potential_span"], "primary span"), PRIMARY_B, "primary span")
    _exact(_fraction(primary["candidate_drift_oscillation"], "primary drift"), PRIMARY_DRIFT, "primary drift")
    _exact(
        _fraction(primary["refresh_drift_sensitivity_oscillation"], "primary sensitivity"),
        PRIMARY_SENSITIVITY,
        "primary sensitivity",
    )
    return protocol


def _validate_bound_source(
    protocol: dict[str, Any], binding_name: str, path: Path, raw: bytes
) -> None:
    row = _object(protocol["bindings"][binding_name], f"bindings.{binding_name}")
    _keys(row, {"path", "sha256"}, f"bindings.{binding_name}")
    _exact(row["path"], _display(path), f"bindings.{binding_name}.path")
    _exact(_digest(row["sha256"], f"bindings.{binding_name}.sha256"), sha256_bytes(raw), f"bindings.{binding_name}.sha256")


def _validate_trace_counts(
    raw: bytes, trace_raw: bytes, states: list[int], actions: list[int]
) -> tuple[dict[str, Any], dict[str, Any]]:
    value = parse_canonical_object(raw, "trace counts")
    _keys(
        value,
        {
            "artifact_status",
            "counts",
            "final_action",
            "final_state",
            "generator_revision",
            "horizon",
            "initial_action",
            "initial_state",
            "nonclaims",
            "prng_audit",
            "schema_version",
            "trace_sha256",
            "trace_version",
        },
        "trace counts",
    )
    _exact(value["schema_version"], TRACE_COUNTS_SCHEMA, "trace-count schema")
    _exact(value["trace_version"], TRACE_VERSION, "trace-count version")
    _exact(value["horizon"], HORIZON, "trace-count horizon")
    _exact(value["initial_state"], 0, "trace-count initial state")
    _exact(value["initial_action"], 0, "trace-count initial action")
    _exact(value["final_state"], states[-1], "trace-count final state")
    _exact(value["final_action"], actions[-1], "trace-count final action")
    _exact(_digest(value["trace_sha256"], "trace-count trace SHA-256"), sha256_bytes(trace_raw), "trace-count trace SHA-256")
    audit = _object(value["prng_audit"], "trace counts.prng_audit")
    _keys(audit, {"bytes_consumed", "digest_blocks_generated", "rejections_by_modulus", "version", "words_consumed"}, "trace counts.prng_audit")
    for name in ("bytes_consumed", "digest_blocks_generated", "words_consumed"):
        _integer(audit[name], f"trace counts.prng_audit.{name}", minimum=0)
    _exact(audit["bytes_consumed"], 8 * audit["words_consumed"], "PRNG bytes/words identity")
    physical = physical_counts(states, actions)
    counts = _object(value["counts"], "trace counts.counts")
    _keys(
        counts,
        {
            "destination_state_counts",
            "edge_counts",
            "persistence_hit_count",
            "persistence_miss_count",
            "source_state_visits",
            "state_action_counts",
            "transition_action_counts",
        },
        "trace counts.counts",
    )
    for key in counts:
        _exact(counts[key], physical[key], f"trace counts.counts.{key}")
    return value, physical


def _input_rows_by_role(manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for index, raw_row in enumerate(_array(manifest["inputs"], "trace manifest.inputs")):
        row = _object(raw_row, f"trace manifest.inputs[{index}]")
        _keys(row, {"bytes", "path", "role", "sha256"}, f"trace manifest.inputs[{index}]")
        role = _string(row["role"], f"trace manifest.inputs[{index}].role")
        if role in rows:
            _fail(f"duplicate trace-manifest input role: {role}")
        _integer(row["bytes"], f"trace manifest input {role} bytes", minimum=0)
        _digest(row["sha256"], f"trace manifest input {role} sha256")
        rows[role] = row
    return rows


def _validate_file_row(
    row: Any, role: str, path: Path, raw: bytes, where: str
) -> dict[str, Any]:
    value = _object(row, where)
    _keys(value, {"bytes", "path", "role", "sha256"}, where)
    _exact(value["role"], role, f"{where}.role")
    _exact(value["path"], _display(path), f"{where}.path")
    _exact(value["bytes"], len(raw), f"{where}.bytes")
    _exact(_digest(value["sha256"], f"{where}.sha256"), sha256_bytes(raw), f"{where}.sha256")
    return value


def validate_trace_manifest(
    raw: bytes,
    *,
    protocol_path: Path,
    protocol_raw: bytes,
    model_input_path: Path,
    model_input_raw: bytes,
    model_manifest_path: Path,
    model_manifest_raw: bytes,
    model_tables_path: Path,
    model_tables_raw: bytes,
    trace_path: Path,
    trace_raw: bytes,
    counts_path: Path,
    counts_raw: bytes,
) -> dict[str, Any]:
    manifest = parse_canonical_object(raw, "trace manifest")
    _keys(
        manifest,
        {
            "artifact_status",
            "beacon",
            "code_freeze",
            "generator",
            "independent_verifier",
            "inputs",
            "manifest_note",
            "nonclaims",
            "outputs",
            "parameters",
            "registration",
            "schema_version",
            "trace_version",
        },
        "trace manifest",
    )
    _exact(manifest["schema_version"], TRACE_MANIFEST_SCHEMA, "trace-manifest schema")
    _exact(manifest["trace_version"], TRACE_VERSION, "trace-manifest version")
    parameters = _object(manifest["parameters"], "trace manifest.parameters")
    _exact(parameters.get("horizon"), HORIZON, "trace-manifest horizon")
    _exact(parameters.get("state_count"), STATE_COUNT, "trace-manifest state count")
    _exact(parameters.get("action_count"), ACTION_COUNT, "trace-manifest action count")
    _exact(parameters.get("initial_state"), 0, "trace-manifest initial state")
    _exact(parameters.get("initial_action"), 0, "trace-manifest initial action")
    _exact(parameters.get("true_gamma"), "149/200", "trace-manifest true gamma")
    registration = _object(manifest["registration"], "trace manifest.registration")
    _exact(_oid(registration.get("protocol_commit"), "protocol commit"), PROTOCOL_COMMIT, "protocol commit")
    _exact(_oid(registration.get("protocol_tree"), "protocol tree"), PROTOCOL_TREE, "protocol tree")
    code_freeze = _object(manifest["code_freeze"], "trace manifest.code_freeze")
    _oid(code_freeze.get("commit"), "code-freeze commit")
    _oid(code_freeze.get("tree"), "code-freeze tree")
    code_rows = _array(code_freeze.get("code_files"), "trace manifest.code_freeze.code_files")
    _exact(len(code_rows), 4, "code-freeze file count")
    roles = [
        "trace_generator",
        "trace_verifier",
        "receipt_generator",
        "receipt_verifier",
    ]
    expected_paths = [
        "scripts/generate_controlled_queue_prospective_trace.py",
        "scripts/verify_controlled_queue_prospective_trace.py",
        GENERATOR_PATH,
        VERIFIER_PATH,
    ]
    for index, (role, expected_path) in enumerate(zip(roles, expected_paths, strict=True)):
        row = _object(code_rows[index], f"code file {role}")
        _keys(row, {"bytes", "path", "role", "sha256"}, f"code file {role}")
        _exact(row["role"], role, f"code file {role}.role")
        _exact(row["path"], expected_path, f"code file {role}.path")
        _integer(row["bytes"], f"code file {role}.bytes", minimum=1)
        _digest(row["sha256"], f"code file {role}.sha256")

    input_rows = _input_rows_by_role(manifest)
    prefix = [
        "protocol",
        "osf_registration_response",
        "osf_registration_binding",
        "osf_registration_binding_file",
        "quicknet_chain_info",
        "quicknet_round",
        "model_input",
        "model_manifest",
        "model_tables",
    ]
    _exact([row["role"] for row in manifest["inputs"]], prefix, "trace-manifest input order")
    for role, path, file_raw in (
        ("protocol", protocol_path, protocol_raw),
        ("model_input", model_input_path, model_input_raw),
        ("model_manifest", model_manifest_path, model_manifest_raw),
        ("model_tables", model_tables_path, model_tables_raw),
    ):
        _validate_file_row(input_rows[role], role, path, file_raw, f"trace input {role}")
    outputs = _array(manifest["outputs"], "trace manifest.outputs")
    _exact(len(outputs), 2, "trace-manifest output count")
    _validate_file_row(outputs[0], "trace_binary", trace_path, trace_raw, "trace output binary")
    _validate_file_row(outputs[1], "trace_counts", counts_path, counts_raw, "trace output counts")
    beacon = _object(manifest["beacon"], "trace manifest.beacon")
    _exact(_boolean(beacon.get("signature_verified"), "beacon.signature_verified"), True, "beacon signature status")
    return manifest


def decode_trace(raw: bytes, *, expected_horizon: int = HORIZON) -> tuple[list[int], list[int]]:
    expected_bytes = BINARY_HEADER.size + 2 * (expected_horizon + 1)
    if len(raw) != expected_bytes:
        _fail(f"trace byte length mismatch: expected {expected_bytes}, got {len(raw)}")
    if expected_horizon == HORIZON:
        _exact(len(raw), BINARY_BYTES, "frozen trace byte length")
    magic, horizon, state_count, action_count = BINARY_HEADER.unpack_from(raw)
    _exact(magic, BINARY_MAGIC, "trace magic")
    _exact(horizon, expected_horizon, "trace horizon")
    _exact(state_count, expected_horizon + 1, "trace state count")
    _exact(action_count, expected_horizon + 1, "trace action count")
    offset = BINARY_HEADER.size
    states = list(raw[offset : offset + state_count])
    actions = list(raw[offset + state_count : offset + state_count + action_count])
    if any(not 0 <= state < STATE_COUNT for state in states):
        _fail("trace contains a physical-state byte outside [0,24)")
    if any(not 0 <= action < ACTION_COUNT for action in actions):
        _fail("trace contains an action byte outside [0,2)")
    _exact(states[0], 0, "trace initial state")
    _exact(actions[0], 0, "trace dummy initial action")
    return states, actions


def queue_step(state: int, action: int) -> int:
    queue, regime = divmod(state, 3)
    service = (1, 2)[action]
    arrival = (0, 1, 2)[regime]
    return 3 * min(7, max(0, queue - service) + arrival) + (regime + 1) % 3


def physical_counts(states: Sequence[int], actions: Sequence[int]) -> dict[str, Any]:
    if len(states) != len(actions) or len(states) < 2:
        _fail("states/actions must have equal length at least two")
    horizon = len(states) - 1
    source = [0] * STATE_COUNT
    destination = [0] * STATE_COUNT
    action_totals = [0] * ACTION_COUNT
    state_action = [[0] * ACTION_COUNT for _ in range(STATE_COUNT)]
    edges = [[[0] * STATE_COUNT for _ in range(ACTION_COUNT)] for _ in range(STATE_COUNT)]
    hits = 0
    for k in range(horizon):
        state = states[k]
        action = actions[k + 1]
        next_state = states[k + 1]
        source[state] += 1
        destination[next_state] += 1
        action_totals[action] += 1
        state_action[state][action] += 1
        edges[state][action][next_state] += 1
        hits += int(next_state == queue_step(state, action))
    return {
        "destination_state_counts": destination,
        "edge_counts": edges,
        "persistence_hit_count": hits,
        "persistence_miss_count": horizon - hits,
        "source_state_visits": source,
        "state_action_counts": state_action,
        "transition_action_counts": action_totals,
    }


def augmented_counts(states: Sequence[int], actions: Sequence[int]) -> tuple[list[list[int]], list[int]]:
    if len(states) != len(actions) or len(states) < 2:
        _fail("states/actions must have equal length at least two")
    edges = [[0] * AUGMENTED_COUNT for _ in range(AUGMENTED_COUNT)]
    visits = [0] * AUGMENTED_COUNT
    for k in range(len(states) - 1):
        source = 2 * states[k] + actions[k]
        destination = 2 * states[k + 1] + actions[k + 1]
        edges[source][destination] += 1
        visits[source] += 1
    return edges, visits


def _indexed_rows(rows: Any, count: int, where: str) -> list[dict[str, Any]]:
    values = [_object(row, f"{where}[{index}]") for index, row in enumerate(_array(rows, where))]
    _exact(len(values), count, f"{where} length")
    return values


def _fraction_row(values: Any, count: int, where: str) -> list[Fraction]:
    row = _array(values, where)
    _exact(len(row), count, f"{where} length")
    result = [_fraction(value, f"{where}[{index}]") for index, value in enumerate(row)]
    return result


def _mat_vec(matrix: Sequence[Sequence[Fraction]], vector: Sequence[Fraction]) -> list[Fraction]:
    return [
        sum((coefficient * value for coefficient, value in zip(row, vector, strict=True)), Fraction(0))
        for row in matrix
    ]


def refresh_kernel(gamma: Fraction) -> list[list[list[Fraction]]]:
    base = (1 - gamma) / STATE_COUNT
    return [
        [
            [base + (gamma if destination == queue_step(state, action) else 0) for destination in range(STATE_COUNT)]
            for action in range(ACTION_COUNT)
        ]
        for state in range(STATE_COUNT)
    ]


def parse_model_tables(raw: bytes) -> dict[str, Any]:
    value = parse_canonical_object(raw, "model tables")
    dimensions = _object(value.get("dimensions"), "model tables.dimensions")
    _exact(dimensions.get("physical_state_count"), STATE_COUNT, "physical state count")
    _exact(dimensions.get("action_count"), ACTION_COUNT, "action count")
    _exact(dimensions.get("augmented_behavior_state_count"), AUGMENTED_COUNT, "augmented count")
    _exact(dimensions.get("candidate_count"), len(CANDIDATE_IDS), "candidate count")
    _exact(dimensions.get("target_policy_count"), 4, "target-policy count")
    _exact(dimensions.get("fixed_predictor_count"), 3, "fixed-predictor count")

    policy_items = _array(value.get("policies"), "model tables.policies")
    policy_by_id = {_string(item.get("id"), "policy id"): _object(item, "policy") for item in policy_items}
    expected_policy_ids = ("behavior_uniform", "conservative", "queue_threshold", "regime_aware", "aggressive")
    _exact(tuple(policy_by_id), expected_policy_ids, "policy order")
    policies: list[list[list[Fraction]]] = []
    for policy_id in expected_policy_ids:
        rows = _indexed_rows(policy_by_id[policy_id].get("rows"), STATE_COUNT, f"policy {policy_id}.rows")
        parsed_rows = []
        for state, row in enumerate(rows):
            _exact(row.get("state"), state, f"policy {policy_id} state index")
            probabilities = _fraction_row(row.get("probabilities"), ACTION_COUNT, f"policy {policy_id} row {state}")
            _exact(sum(probabilities), Fraction(1), f"policy {policy_id} row mass")
            parsed_rows.append(probabilities)
        policies.append(parsed_rows)
    if any(mass != BEHAVIOR_MASS for row in policies[0] for mass in row):
        _fail("behavior policy is not exactly uniform over two actions")

    candidate_items = _array(value.get("candidate_kernels"), "model tables.candidate_kernels")
    _exact([item.get("id") for item in candidate_items], list(CANDIDATE_IDS), "candidate order")
    candidates: list[list[list[list[Fraction]]]] = []
    for candidate_index, (item, gamma) in enumerate(zip(candidate_items, CANDIDATE_GAMMAS, strict=True)):
        candidate = _object(item, f"candidate {candidate_index}")
        _exact(_fraction(candidate.get("gamma"), f"candidate {candidate_index}.gamma"), gamma, f"candidate {candidate_index}.gamma")
        rows = _indexed_rows(candidate.get("rows"), STATE_COUNT * ACTION_COUNT, f"candidate {candidate_index}.rows")
        kernel = [[[] for _ in range(ACTION_COUNT)] for _ in range(STATE_COUNT)]
        for row_index, row in enumerate(rows):
            state, action = divmod(row_index, ACTION_COUNT)
            _exact(row.get("state"), state, f"candidate {candidate_index} row state")
            _exact(row.get("action"), ("eco", "boost")[action], f"candidate {candidate_index} row action")
            probabilities = _fraction_row(row.get("probabilities"), STATE_COUNT, f"candidate {candidate_index} row {row_index}")
            _exact(sum(probabilities), Fraction(1), f"candidate {candidate_index} row mass")
            kernel[state][action] = probabilities
        _exact(kernel, refresh_kernel(gamma), f"candidate {candidate_index} refresh kernel")
        candidates.append(kernel)

    brier_items = _array(value.get("fixed_brier_loss"), "model tables.fixed_brier_loss")
    predictor_ids = ("global_climatology", "queue_action_threshold", "nominal_model_overload")
    _exact([item.get("id") for item in brier_items], list(predictor_ids), "Brier predictor order")
    losses: list[list[list[list[Fraction]]]] = []
    for predictor_index, item in enumerate(brier_items):
        rows = _indexed_rows(item.get("rows"), STATE_COUNT * ACTION_COUNT, f"Brier {predictor_index}.rows")
        table = [[[] for _ in range(ACTION_COUNT)] for _ in range(STATE_COUNT)]
        for row_index, row in enumerate(rows):
            state, action = divmod(row_index, ACTION_COUNT)
            _exact(row.get("state"), state, f"Brier {predictor_index} row state")
            _exact(row.get("action"), ("eco", "boost")[action], f"Brier {predictor_index} row action")
            entries = _fraction_row(row.get("losses"), STATE_COUNT, f"Brier {predictor_index} row {row_index}")
            if any(entry < 0 or entry > 1 for entry in entries):
                _fail("Brier loss escaped [0,1]")
            table[state][action] = entries
        losses.append(table)

    step_rows = _indexed_rows(value.get("queue_step"), STATE_COUNT * ACTION_COUNT, "model tables.queue_step")
    for row_index, row in enumerate(step_rows):
        state, action = divmod(row_index, ACTION_COUNT)
        _exact(row.get("state"), state, "queue-step state")
        _exact(row.get("action"), ("eco", "boost")[action], "queue-step action")
        _exact(row.get("next_state"), queue_step(state, action), "queue-step next state")

    return {
        "behavior_policy": policies[0],
        "target_policies": policies[1:],
        "candidate_kernels": candidates,
        "losses": losses,
        "predictor_ids": predictor_ids,
    }


def closed_span_bound(gamma: Fraction, depth: int) -> Fraction:
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    return sum((gamma**power for power in range(depth)), Fraction(0))


def compute_potential(
    environment: Sequence[Sequence[Sequence[Fraction]]],
    policy: Sequence[Sequence[Fraction]],
    loss: Sequence[Sequence[Sequence[Fraction]]],
    depth: int,
) -> dict[str, Any]:
    kernel = [
        [
            sum((policy[state][action] * environment[state][action][destination] for action in range(ACTION_COUNT)), Fraction(0))
            for destination in range(STATE_COUNT)
        ]
        for state in range(STATE_COUNT)
    ]
    row_risk = [
        sum(
            (
                policy[state][action]
                * sum(
                    (environment[state][action][destination] * loss[state][action][destination] for destination in range(STATE_COUNT)),
                    Fraction(0),
                )
                for action in range(ACTION_COUNT)
            ),
            Fraction(0),
        )
        for state in range(STATE_COUNT)
    ]
    reference_mean = sum(row_risk, Fraction(0)) / STATE_COUNT
    iterate = [value - reference_mean for value in row_risk]
    potential = [Fraction(0)] * STATE_COUNT
    for _ in range(depth):
        potential = [left + right for left, right in zip(potential, iterate, strict=True)]
        iterate = _mat_vec(kernel, iterate)
    anchor = potential[0]
    potential = [value - anchor for value in potential]
    span = max(potential) - min(potential)
    drift = [
        row_risk[state] + _mat_vec(kernel, potential)[state] - potential[state]
        for state in range(STATE_COUNT)
    ]
    drift_oscillation = max(drift) - min(drift)
    return {
        "depth": depth,
        "potential": potential,
        "actual_span": span,
        "row_risk": row_risk,
        "uniform_reference_mean": reference_mean,
        "drift": drift,
        "drift_oscillation": drift_oscillation,
    }


def refresh_sensitivity_table(
    policy: Sequence[Sequence[Fraction]],
    loss: Sequence[Sequence[Sequence[Fraction]]],
    potential: Sequence[Fraction],
) -> list[Fraction]:
    loss_averages = [
        [sum(loss[state][action], Fraction(0)) / STATE_COUNT for action in range(ACTION_COUNT)]
        for state in range(STATE_COUNT)
    ]
    potential_average = sum(potential, Fraction(0)) / STATE_COUNT
    return [
        Fraction(24, 23)
        * sum(
            (
                policy[state][action]
                * (
                    loss[state][action][queue_step(state, action)]
                    - loss_averages[state][action]
                    + potential[queue_step(state, action)]
                    - potential_average
                )
                for action in range(ACTION_COUNT)
            ),
            Fraction(0),
        )
        for state in range(STATE_COUNT)
    ]


def compute_deterministic_tables(model: dict[str, Any]) -> dict[str, Any]:
    """Compute every potential before any prospective trace is decoded."""

    candidate_tables: list[list[list[dict[str, Any]]]] = []
    for candidate_index, environment in enumerate(model["candidate_kernels"]):
        depth_tables: list[list[dict[str, Any]]] = []
        for depth in DEPTHS:
            hypothesis_tables = []
            for policy_index, policy in enumerate(model["target_policies"]):
                for predictor_index, loss in enumerate(model["losses"]):
                    table = compute_potential(environment, policy, loss, depth)
                    table["candidate_index"] = candidate_index
                    table["policy_index"] = policy_index
                    table["predictor_index"] = predictor_index
                    table["hypothesis_index"] = 3 * policy_index + predictor_index
                    table["closed_span_bound"] = closed_span_bound(CANDIDATE_GAMMAS[candidate_index], depth)
                    hypothesis_tables.append(table)
            depth_tables.append(hypothesis_tables)
        candidate_tables.append(depth_tables)

    selected = candidate_tables[1][DEPTHS.index(12)][3 * 1 + 2]
    _exact(selected["actual_span"], PRIMARY_B, "selected actual potential span")
    _exact(selected["drift_oscillation"], PRIMARY_DRIFT, "selected exact candidate-drift oscillation")
    sensitivity = refresh_sensitivity_table(
        model["target_policies"][1], model["losses"][2], selected["potential"]
    )
    sensitivity_oscillation = max(sensitivity) - min(sensitivity)
    _exact(sensitivity_oscillation, PRIMARY_SENSITIVITY, "selected exact refresh-sensitivity oscillation")
    selected["refresh_sensitivity"] = sensitivity
    selected["refresh_sensitivity_oscillation"] = sensitivity_oscillation

    # The true-kernel oracle is completely determined and must be computed here,
    # before the caller is allowed to decode or inspect the prospective trace.
    oracle = compute_potential(
        refresh_kernel(TRUE_GAMMA),
        model["target_policies"][1],
        model["losses"][2],
        12,
    )
    return {"candidate_tables": candidate_tables, "selected": selected, "oracle": oracle}


def load_deterministic_then_decode(
    model: dict[str, Any],
    trace_raw: bytes,
    *,
    deterministic_builder: Callable[[dict[str, Any]], dict[str, Any]] = compute_deterministic_tables,
    decoder: Callable[..., tuple[list[int], list[int]]] = decode_trace,
) -> tuple[dict[str, Any], list[int], list[int]]:
    deterministic = deterministic_builder(model)
    states, actions = decoder(trace_raw)
    return deterministic, states, actions


def normalized_score_summary(
    histogram: Sequence[Sequence[Sequence[int]]],
    policy: Sequence[Sequence[Fraction]],
    loss: Sequence[Sequence[Sequence[Fraction]]],
    potential: Sequence[Fraction],
    span_bound: Fraction,
) -> dict[str, Any]:
    if span_bound < 0:
        _fail("score span bound must be nonnegative")
    scale = IMPORTANCE_CAP * (1 + 2 * span_bound)
    score_sum = Fraction(0)
    score_sum_squares = Fraction(0)
    row_sums = [[Fraction(0)] * ACTION_COUNT for _ in range(STATE_COUNT)]
    row_sum_squares = [[Fraction(0)] * ACTION_COUNT for _ in range(STATE_COUNT)]
    for state in range(STATE_COUNT):
        for action in range(ACTION_COUNT):
            ratio = policy[state][action] / BEHAVIOR_MASS
            for destination in range(STATE_COUNT):
                score = ratio * (
                    loss[state][action][destination]
                    + potential[destination]
                    - potential[state]
                    + span_bound
                ) / scale
                if score < 0 or score > 1:
                    _fail("normalized score escaped [0,1]")
                count = histogram[state][action][destination]
                score_sum += count * score
                score_sum_squares += count * score * score
                row_sums[state][action] += count * score
                row_sum_squares[state][action] += count * score * score
    n = sum(sum(sum(row) for row in action_rows) for action_rows in histogram)
    if n <= 0:
        _fail("score histogram must contain at least one transition")
    q = score_sum_squares - score_sum * score_sum / n
    if q < 0:
        _fail("exact Bessel statistic is negative")
    hybrid = Fraction(1, 2) + Fraction(3, 2) * q
    empirical = scale * score_sum / n - span_bound
    return {
        "sum": score_sum,
        "sum_squares": score_sum_squares,
        "row_sums": row_sums,
        "row_sum_squares": row_sum_squares,
        "bessel_q": q,
        "hybrid_affine_upper": hybrid,
        "scale": scale,
        "span_bound": span_bound,
        "empirical_corrected_score": empirical,
    }


def empirical_bernstein_correction(
    summary: dict[str, Any], *, log_upper: int, tilt: Fraction
) -> Fraction:
    n = summary.get("count")
    if n is None:
        _fail("score summary is missing its transition count")
    return summary["scale"] * (
        Fraction(log_upper) + PSI_UPPER[tilt] * summary["hybrid_affine_upper"]
    ) / (n * tilt)


def score_summary_with_count(
    histogram: Sequence[Sequence[Sequence[int]]],
    policy: Sequence[Sequence[Fraction]],
    loss: Sequence[Sequence[Sequence[Fraction]]],
    potential: Sequence[Fraction],
    span_bound: Fraction,
) -> dict[str, Any]:
    summary = normalized_score_summary(histogram, policy, loss, potential, span_bound)
    summary["count"] = Fraction(
        sum(sum(sum(row) for row in action_rows) for action_rows in histogram)
    )
    return summary


def indicator_bessel_summary(successes: int, n: int) -> dict[str, Fraction]:
    if isinstance(successes, bool) or isinstance(n, bool) or not 0 <= successes <= n or n <= 0:
        raise ValueError("indicator count must lie in [0,n] with n positive")
    count = Fraction(successes)
    total = Fraction(n)
    q = count - count * count / total
    return {
        "sum": count,
        "sum_squares": count,
        "bessel_q": q,
        "hybrid_affine_upper": Fraction(1, 2) + Fraction(3, 2) * q,
    }


def persistence_radius(
    hits: int, n: int, *, tilt: Fraction, log_upper: int
) -> dict[str, Fraction]:
    direct = indicator_bessel_summary(hits, n)
    complement = indicator_bessel_summary(n - hits, n)
    direct_boundary = (
        Fraction(log_upper) + PSI_UPPER[tilt] * direct["hybrid_affine_upper"]
    ) / (n * tilt)
    complement_boundary = (
        Fraction(log_upper) + PSI_UPPER[tilt] * complement["hybrid_affine_upper"]
    ) / (n * tilt)
    return {
        "direct_sum": direct["sum"],
        "direct_bessel_q": direct["bessel_q"],
        "direct_hybrid_affine_upper": direct["hybrid_affine_upper"],
        "direct_boundary": direct_boundary,
        "complement_sum": complement["sum"],
        "complement_bessel_q": complement["bessel_q"],
        "complement_hybrid_affine_upper": complement["hybrid_affine_upper"],
        "complement_boundary": complement_boundary,
        "radius": max(direct_boundary, complement_boundary),
    }


def structured_eta(
    candidate_hit: Fraction,
    hits: int,
    n: int,
    *,
    tilt: Fraction,
    log_upper: int,
) -> dict[str, Fraction]:
    confidence = persistence_radius(hits, n, tilt=tilt, log_upper=log_upper)
    discrepancy = abs(candidate_hit - Fraction(hits, n))
    return {**confidence, "candidate_discrepancy": discrepancy, "eta": discrepancy + confidence["radius"]}


def fixed_range_eta(candidate_hit: Fraction, hits: int, n: int) -> dict[str, Fraction]:
    tilt = Fraction(1, 64)
    correction = tilt / (8 * (1 - tilt / 3)) + Fraction(7, n) / tilt
    discrepancy = abs(candidate_hit - Fraction(hits, n))
    return {"candidate_discrepancy": discrepancy, "fixed_range_radius": correction, "eta": discrepancy + correction}


def fixed_range_risk_correction(scale: Fraction, n: int) -> Fraction:
    tilt = Fraction(1, 16)
    return scale * (tilt / (8 * (1 - tilt / 3)) + Fraction(9, n) / tilt)


def augmented_candidate_kernel(
    environment: Sequence[Sequence[Sequence[Fraction]]]
) -> list[list[Fraction]]:
    rows: list[list[Fraction]] = []
    for source in range(AUGMENTED_COUNT):
        state = source // 2
        row = [Fraction(0)] * AUGMENTED_COUNT
        for action in range(ACTION_COUNT):
            for destination in range(STATE_COUNT):
                row[2 * destination + action] = BEHAVIOR_MASS * environment[state][action][destination]
        _exact(sum(row), Fraction(1), "augmented candidate row mass")
        rows.append(row)
    return rows


def unstructured_transition_summary(
    edges: Sequence[Sequence[int]],
    visits: Sequence[int],
    candidate_environment: Sequence[Sequence[Sequence[Fraction]]],
    n: int,
) -> dict[str, Any]:
    if len(edges) != AUGMENTED_COUNT or len(visits) != AUGMENTED_COUNT:
        _fail("augmented histogram dimensions mismatch")
    candidate = augmented_candidate_kernel(candidate_environment)
    source_rows: list[dict[str, Any]] = []
    eta = Fraction(0)
    all_visited = True
    coordinate_count = 0
    orientation_count = 0
    tilt = Fraction(1, 64)
    psi = PSI_UPPER[tilt]
    for source in range(AUGMENTED_COUNT):
        row = list(edges[source])
        if len(row) != AUGMENTED_COUNT:
            _fail("augmented edge row length mismatch")
        visit = visits[source]
        _exact(sum(row), visit, f"augmented source {source} visit identity")
        if visit == 0:
            all_visited = False
            source_rows.append(
                {
                    "source": source,
                    "visits": 0,
                    "premise_visited": False,
                    "empirical_row_tv": Fraction(0),
                    "coordinate_radius_sum_half": Fraction(0),
                    "row_eta": Fraction(0),
                    "coordinate_radii": [Fraction(0)] * AUGMENTED_COUNT,
                }
            )
            coordinate_count += AUGMENTED_COUNT
            orientation_count += 2 * AUGMENTED_COUNT
            continue
        empirical_tv = Fraction(1, 2) * sum(
            (abs(candidate[source][destination] - Fraction(row[destination], visit)) for destination in range(AUGMENTED_COUNT)),
            Fraction(0),
        )
        coordinate_radii: list[Fraction] = []
        for observed in row:
            direct = indicator_bessel_summary(observed, n)
            complement = indicator_bessel_summary(n - observed, n)
            direct_boundary = (Fraction(18) + psi * direct["hybrid_affine_upper"]) / (n * tilt)
            complement_boundary = (Fraction(18) + psi * complement["hybrid_affine_upper"]) / (n * tilt)
            coordinate_radii.append(Fraction(n, visit) * max(direct_boundary, complement_boundary))
            coordinate_count += 1
            orientation_count += 2
        radius_half = Fraction(1, 2) * sum(coordinate_radii, Fraction(0))
        row_eta = empirical_tv + radius_half
        eta = max(eta, row_eta)
        source_rows.append(
            {
                "source": source,
                "visits": visit,
                "premise_visited": True,
                "empirical_row_tv": empirical_tv,
                "coordinate_radius_sum_half": radius_half,
                "row_eta": row_eta,
                "coordinate_radii": coordinate_radii,
            }
        )
    _exact(coordinate_count, 2304, "unstructured coordinate count")
    _exact(orientation_count, 4608, "unstructured oriented-coordinate count")
    return {
        "all_augmented_source_rows_visited": all_visited,
        "coordinate_count": coordinate_count,
        "oriented_coordinate_count": orientation_count,
        "source_rows": source_rows,
        "eta_augmented": eta,
    }


def causal_beta_summaries(
    states: Sequence[int], actions: Sequence[int]
) -> dict[str, Any]:
    if len(states) != len(actions) or len(states) < 2:
        _fail("causal predictor path dimensions mismatch")
    n = len(states) - 1
    global_alpha = 1
    global_beta = 1
    band_cells = [[[1, 1] for _action in range(ACTION_COUNT)] for _band in range(3)]
    global_loss_partials: list[Fraction | None] = []
    band_loss_partials: list[Fraction | None] = []
    for k in range(n):
        state = states[k]
        action = actions[k + 1]
        next_state = states[k + 1]
        outcome = int(next_state // 3 >= 6)

        global_probability = Fraction(global_alpha, global_alpha + global_beta)
        _balanced_fraction_add(
            global_loss_partials, (global_probability - outcome) ** 2
        )

        queue = state // 3
        band = 0 if queue <= 3 else (1 if queue <= 5 else 2)
        alpha, beta = band_cells[band][action]
        band_probability = Fraction(alpha, alpha + beta)
        _balanced_fraction_add(
            band_loss_partials, (band_probability - outcome) ** 2
        )

        global_alpha += outcome
        global_beta += 1 - outcome
        band_cells[band][action][0] += outcome
        band_cells[band][action][1] += 1 - outcome

    global_loss = _balanced_fraction_total(global_loss_partials)
    band_loss = _balanced_fraction_total(band_loss_partials)
    return {
        "evaluation_contract": "score with the pre-update Beta probability, then update using the transition outcome",
        "outcome": "queue(next_state) >= 6",
        "predictors": [
            {
                "id": "global_beta",
                "cumulative_brier_loss": number(global_loss),
                "mean_brier_loss": number(global_loss / n),
                "final_alpha": global_alpha,
                "final_beta": global_beta,
            },
            {
                "id": "queue_band_action_beta",
                "cumulative_brier_loss": number(band_loss),
                "mean_brier_loss": number(band_loss / n),
                "final_cells_alpha_beta": band_cells,
            },
        ],
        "confidence_status": "DESCRIPTIVE_DYNAMIC_ENCOUNTERED_RISK_ONLY",
    }


def build_score_catalog(
    histogram: Sequence[Sequence[Sequence[int]]],
    model: dict[str, Any],
    deterministic: dict[str, Any],
) -> list[dict[str, Any]]:
    catalog: list[dict[str, Any]] = []
    for candidate_index in range(len(CANDIDATE_IDS)):
        for depth_index, depth in enumerate(DEPTHS):
            for posterior_index in range(HYPOTHESIS_COUNT):
                policy_index, predictor_index = divmod(posterior_index, 3)
                table = deterministic["candidate_tables"][candidate_index][depth_index][posterior_index]
                summary = score_summary_with_count(
                    histogram,
                    model["target_policies"][policy_index],
                    model["losses"][predictor_index],
                    table["potential"],
                    table["closed_span_bound"],
                )
                catalog.append(
                    {
                        "candidate_index": candidate_index,
                        "depth_index": depth_index,
                        "depth": depth,
                        "posterior_index": posterior_index,
                        "policy_index": policy_index,
                        "predictor_index": predictor_index,
                        "summary": summary,
                    }
                )
    _exact(len(catalog), 252, "adaptive score-summary count")
    return catalog


def select_adaptive_endpoint(
    score_catalog: Sequence[dict[str, Any]], hits: int, n: int
) -> dict[str, Any]:
    """Select the frozen catalog minimum; no true-gamma argument is accepted."""

    by_key = {
        (row["candidate_index"], row["depth_index"], row["posterior_index"]): row
        for row in score_catalog
    }
    persistence = {
        (candidate_index, tilt_index): structured_eta(
            CANDIDATE_HITS[candidate_index], hits, n, tilt=tilt, log_upper=9
        )
        for candidate_index in range(3)
        for tilt_index, tilt in enumerate(TILTS)
    }
    candidates: list[dict[str, Any]] = []
    best_key: tuple[Fraction, int, int, int, int, int] | None = None
    best: dict[str, Any] | None = None
    for candidate_index in range(3):
        gamma = CANDIDATE_GAMMAS[candidate_index]
        for depth_index, depth in enumerate(DEPTHS):
            for risk_tilt_index, risk_tilt in enumerate(TILTS):
                for persistence_tilt_index, _persistence_tilt in enumerate(TILTS):
                    eta = persistence[(candidate_index, persistence_tilt_index)]["eta"]
                    for posterior_index in range(HYPOTHESIS_COUNT):
                        score = by_key[(candidate_index, depth_index, posterior_index)]["summary"]
                        risk = empirical_bernstein_correction(score, log_upper=16, tilt=risk_tilt)
                        residual = gamma**depth + 2 * (1 + score["span_bound"]) * eta
                        total = score["empirical_corrected_score"] + risk + residual
                        indices = (
                            candidate_index,
                            depth_index,
                            risk_tilt_index,
                            persistence_tilt_index,
                            posterior_index,
                        )
                        row = {"indices": list(indices), "total_certified_rhs": total}
                        candidates.append(row)
                        key = (total, *indices)
                        if best_key is None or key < best_key:
                            best_key = key
                            best = {
                                **row,
                                "empirical_corrected_score": score["empirical_corrected_score"],
                                "risk_statistical_correction": risk,
                                "persistence_eta": eta,
                                "candidate_or_truncation_residual": residual,
                                "score_summary": score,
                            }
    _exact(len(candidates), 4032, "adaptive selector tuple count")
    if best is None:
        raise AssertionError("nonempty frozen adaptive catalog produced no minimum")
    return {"selected": best, "catalog_minimum_certificate": candidates, "persistence_summaries": persistence}


def _public_score_summary(summary: dict[str, Any]) -> dict[str, Any]:
    return {
        key: (
            number(value)
            if isinstance(value, Fraction)
            else [[number(entry) for entry in row] for row in value]
        )
        for key, value in summary.items()
    }


def _public_fraction_dict(value: dict[str, Any]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, item in value.items():
        if isinstance(item, Fraction):
            result[key] = number(item)
        elif isinstance(item, dict):
            result[key] = _public_fraction_dict(item)
        elif isinstance(item, list):
            result[key] = [number(entry) if isinstance(entry, Fraction) else entry for entry in item]
        else:
            result[key] = item
    return result


def _event(
    label: str,
    theorem: str | None,
    claim_kind: str,
    *,
    checked_outer_mass: Fraction | None,
    planned_allocation: Fraction | None,
) -> dict[str, Any]:
    return {
        "event_label": label,
        "lean_theorem": theorem,
        "claim_kind": claim_kind,
        "checked_outer_mass": None if checked_outer_mass is None else number(checked_outer_mass),
        "planned_allocation": None if planned_allocation is None else number(planned_allocation),
    }


def _vacuity(total: Fraction, *, primary: bool = False, planned: bool = False, premise_ok: bool = True) -> dict[str, Any]:
    if planned:
        status = "PLANNED_NOT_CHECKED"
    elif not premise_ok:
        status = "PREMISE_FAILED"
    elif primary:
        status = "PRIMARY_SUCCESS" if total < PRIMARY_THRESHOLD else "PRIMARY_THRESHOLD_NOT_MET"
    else:
        status = "INFORMATIVE_BELOW_ONE" if total < 1 else "VACUOUS_AT_OR_ABOVE_ONE"
    return {
        "above_or_equal_one": total >= 1,
        "below_one": total < 1,
        "below_primary_threshold": total < PRIMARY_THRESHOLD,
        "primary_threshold": number(PRIMARY_THRESHOLD),
        "strict_comparison_uses_exact_rational": True,
        "status": status,
    }


def _validate_planned_reporting_rows(rows: Sequence[dict[str, Any]]) -> None:
    if len(rows) != len(ROW_ORDER):
        _fail("receipt must contain exactly seven reporting rows")
    for index, label, event_label in (
        (2, "oracle", "oracle_true_kernel_planned_arithmetic"),
        (5, "fixed-range", "fixed_range_planned_arithmetic"),
    ):
        row = _object(rows[index], f"{label} reporting row")
        _exact(row.get("endpoint_id"), ROW_ORDER[index], f"{label} endpoint")
        expected_event = _event(
            event_label,
            None,
            "PLANNED_ARITHMETIC_ONLY",
            checked_outer_mass=None,
            planned_allocation=Fraction(1, 20),
        )
        _exact(
            row.get("theorem_or_event"), expected_event, f"{label} theorem or event"
        )
        _exact(
            row.get("certification_status"),
            "PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE",
            f"{label} certification status",
        )
        vacuity = _object(
            row.get("vacuity_and_threshold_status"), f"{label} vacuity status"
        )
        _exact(vacuity.get("status"), "PLANNED_NOT_CHECKED", f"{label} status")


def _report_row(
    *,
    endpoint_id: str,
    theorem_or_event: dict[str, Any],
    certification_status: str,
    empirical: Fraction,
    risk: Fraction,
    radius: Fraction,
    residual: Fraction,
    total: Fraction,
    confidence: dict[str, Any],
    settings: dict[str, Any],
    vacuity: dict[str, Any],
) -> dict[str, Any]:
    row = {
        "endpoint_id": endpoint_id,
        "theorem_or_event": theorem_or_event,
        "certification_status": certification_status,
        "empirical_corrected_score": number(empirical),
        "risk_statistical_correction": number(risk),
        "persistence_or_transition_radius": number(radius),
        "candidate_or_truncation_residual": number(residual),
        "total_certified_rhs": number(total),
        "confidence_allocation": confidence,
        "selected_indices_or_fixed_settings": settings,
        "vacuity_and_threshold_status": vacuity,
    }
    _keys(row, ROW_FIELDS, f"reporting row {endpoint_id}")
    return row


def build_receipt(
    *,
    protocol: dict[str, Any],
    protocol_path: Path,
    protocol_raw: bytes,
    trace_path: Path,
    trace_raw: bytes,
    counts_path: Path,
    counts_raw: bytes,
    trace_manifest_path: Path,
    trace_manifest_raw: bytes,
    trace_manifest: dict[str, Any],
    model_input_path: Path,
    model_input_raw: bytes,
    model_manifest_path: Path,
    model_manifest_raw: bytes,
    model_tables_path: Path,
    model_tables_raw: bytes,
    selected_data_path: Path,
    selected_data_raw: bytes,
    known_kernel_source_path: Path,
    known_kernel_source_raw: bytes,
    persistence_source_path: Path,
    persistence_source_raw: bytes,
    structured_source_path: Path,
    structured_source_raw: bytes,
    sharp_structured_source_path: Path,
    sharp_structured_source_raw: bytes,
    sharp_receipt_core_path: Path,
    sharp_receipt_core_raw: bytes,
    deterministic: dict[str, Any],
    states: list[int],
    actions: list[int],
    physical: dict[str, Any],
) -> dict[str, Any]:
    n = len(states) - 1
    _exact(n, HORIZON, "receipt horizon")
    histogram = physical["edge_counts"]
    hits = physical["persistence_hit_count"]
    augmented_edges, augmented_visits = augmented_counts(states, actions)
    _exact(sum(augmented_visits), n, "augmented histogram total")

    model = parse_model_tables(model_tables_raw)
    # Ensure the deterministic precomputation belongs to the same parsed model.
    _exact(deterministic["selected"]["actual_span"], PRIMARY_B, "deterministic selected table")

    selected = deterministic["selected"]
    primary_score = score_summary_with_count(
        histogram,
        model["target_policies"][1],
        model["losses"][2],
        selected["potential"],
        PRIMARY_B,
    )
    primary_risk = empirical_bernstein_correction(primary_score, log_upper=9, tilt=Fraction(1, 16))
    primary_persistence = structured_eta(CANDIDATE_HITS[1], hits, n, tilt=Fraction(1, 64), log_upper=7)
    primary_residual = PRIMARY_DRIFT + PRIMARY_SENSITIVITY * primary_persistence["eta"]
    primary_total = primary_score["empirical_corrected_score"] + primary_risk + primary_residual

    score_catalog = build_score_catalog(histogram, model, deterministic)
    adaptive = select_adaptive_endpoint(score_catalog, hits, n)
    adaptive_selected = adaptive["selected"]

    oracle = deterministic["oracle"]
    oracle_score = score_summary_with_count(
        histogram,
        model["target_policies"][1],
        model["losses"][2],
        oracle["potential"],
        oracle["actual_span"],
    )
    oracle_risk = empirical_bernstein_correction(oracle_score, log_upper=8, tilt=Fraction(1, 16))
    oracle_residual = oracle["drift_oscillation"]
    oracle_total = oracle_score["empirical_corrected_score"] + oracle_risk + oracle_residual

    catalog_by_key = {
        (row["candidate_index"], row["depth_index"], row["posterior_index"]): row
        for row in score_catalog
    }
    generic_rows: dict[int, dict[str, Any]] = {}
    for depth in (12, 5):
        depth_index = DEPTHS.index(depth)
        score = catalog_by_key[(1, depth_index, 5)]["summary"]
        risk = empirical_bernstein_correction(score, log_upper=9, tilt=Fraction(1, 16))
        residual = CANDIDATE_GAMMAS[1] ** depth + 2 * (1 + score["span_bound"]) * primary_persistence["eta"]
        generic_rows[depth] = {
            "score": score,
            "risk": risk,
            "residual": residual,
            "total": score["empirical_corrected_score"] + risk + residual,
        }

    fixed_eta = fixed_range_eta(CANDIDATE_HITS[1], hits, n)
    fixed_risk = fixed_range_risk_correction(primary_score["scale"], n)
    fixed_residual = PRIMARY_DRIFT + PRIMARY_SENSITIVITY * fixed_eta["eta"]
    fixed_total = primary_score["empirical_corrected_score"] + fixed_risk + fixed_residual

    unstructured = unstructured_transition_summary(
        augmented_edges, augmented_visits, model["candidate_kernels"][1], n
    )
    generic12 = generic_rows[12]
    unstructured_residual = CANDIDATE_GAMMAS[1] ** 12 + 4 * (
        1 + generic12["score"]["span_bound"]
    ) * unstructured["eta_augmented"]
    unstructured_total = (
        generic12["score"]["empirical_corrected_score"]
        + generic12["risk"]
        + unstructured_residual
    )

    fixed_confidence = {
        "delta_risk": "1/40",
        "delta_persistence": "1/40",
        "delta_total": "1/20",
        "risk_tilt": "1/16",
        "persistence_tilt": "1/64",
    }
    checked_status = "CHECKED_EVENT_CONDITIONAL_PATHWISE_UPPER_BOUND"
    rows = [
        _report_row(
            endpoint_id=ROW_ORDER[0],
            theorem_or_event=_event(
                "primary_sharp_structured_event",
                "exists_controlledQueueSharpStructuredReceipt_event",
                "CHECKED_OUTER_EVENT_PLUS_HISTOGRAM_REDUCTION",
                checked_outer_mass=Fraction(1, 20),
                planned_allocation=None,
            ),
            certification_status=checked_status,
            empirical=primary_score["empirical_corrected_score"],
            risk=primary_risk,
            radius=primary_persistence["eta"],
            residual=primary_residual,
            total=primary_total,
            confidence=fixed_confidence,
            settings={
                "candidate_index": 1,
                "depth": 12,
                "policy_index": 1,
                "predictor_index": 2,
                "posterior_index": 5,
                "fixed_before_data": True,
            },
            vacuity=_vacuity(primary_total, primary=True),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[1],
            theorem_or_event=_event(
                "adaptive_21_atom_event",
                "exists_controlledQueueStructuredAdaptiveOPE_event",
                "SEPARATE_CHECKED_ADAPTIVE_EVENT",
                checked_outer_mass=Fraction(1, 20),
                planned_allocation=None,
            ),
            certification_status=checked_status,
            empirical=adaptive_selected["empirical_corrected_score"],
            risk=adaptive_selected["risk_statistical_correction"],
            radius=adaptive_selected["persistence_eta"],
            residual=adaptive_selected["candidate_or_truncation_residual"],
            total=adaptive_selected["total_certified_rhs"],
            confidence={
                "delta_risk": "1/40",
                "delta_persistence": "1/40",
                "delta_total": "1/20",
                "candidate_depth_weight": "1/21",
                "risk_tilt_weight": "1/4",
                "persistence_tilt_weight": "1/4",
            },
            settings={
                "indices": adaptive_selected["indices"],
                "tie_break_order": [
                    "candidate_index",
                    "depth_index",
                    "risk_tilt_index",
                    "persistence_tilt_index",
                    "posterior_index",
                ],
                "selector_received_true_gamma": False,
            },
            vacuity=_vacuity(adaptive_selected["total_certified_rhs"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[2],
            theorem_or_event=_event(
                "oracle_true_kernel_planned_arithmetic",
                None,
                "PLANNED_ARITHMETIC_ONLY",
                checked_outer_mass=None,
                planned_allocation=Fraction(1, 20),
            ),
            certification_status="PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE",
            empirical=oracle_score["empirical_corrected_score"],
            risk=oracle_risk,
            radius=Fraction(0),
            residual=oracle_residual,
            total=oracle_total,
            confidence={"delta_risk": "1/20", "delta_total": "1/20", "risk_tilt": "1/16"},
            settings={"true_gamma": "149/200", "depth": 12, "policy_index": 1, "predictor_index": 2, "precomputed_before_trace_decode": True, "oracle_arithmetic_only": True},
            vacuity=_vacuity(oracle_total, planned=True),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[3],
            theorem_or_event=_event("generic_nominal_depth12_event", "exists_structuredControlledQueueFiniteCatalogOPE_event", "SEPARATE_CHECKED_FIXED_ATOM_EVENT", checked_outer_mass=Fraction(1, 20), planned_allocation=None),
            certification_status=checked_status,
            empirical=generic_rows[12]["score"]["empirical_corrected_score"],
            risk=generic_rows[12]["risk"],
            radius=primary_persistence["eta"],
            residual=generic_rows[12]["residual"],
            total=generic_rows[12]["total"],
            confidence=fixed_confidence,
            settings={"candidate_index": 1, "depth": 12, "policy_index": 1, "predictor_index": 2, "fixed_before_data": True},
            vacuity=_vacuity(generic_rows[12]["total"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[4],
            theorem_or_event=_event("generic_nominal_depth5_event", "exists_structuredControlledQueueFiniteCatalogOPE_event", "SEPARATE_CHECKED_FIXED_ATOM_EVENT", checked_outer_mass=Fraction(1, 20), planned_allocation=None),
            certification_status=checked_status,
            empirical=generic_rows[5]["score"]["empirical_corrected_score"],
            risk=generic_rows[5]["risk"],
            radius=primary_persistence["eta"],
            residual=generic_rows[5]["residual"],
            total=generic_rows[5]["total"],
            confidence=fixed_confidence,
            settings={"candidate_index": 1, "depth": 5, "policy_index": 1, "predictor_index": 2, "fixed_before_data": True},
            vacuity=_vacuity(generic_rows[5]["total"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[5],
            theorem_or_event=_event("fixed_range_planned_arithmetic", None, "PLANNED_ARITHMETIC_ONLY", checked_outer_mass=None, planned_allocation=Fraction(1, 20)),
            certification_status="PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE",
            empirical=primary_score["empirical_corrected_score"],
            risk=fixed_risk,
            radius=fixed_eta["eta"],
            residual=fixed_residual,
            total=fixed_total,
            confidence={**fixed_confidence, "confidence_claim": "NOT_A_CONFIDENCE_CERTIFICATE"},
            settings={"candidate_index": 1, "depth": 12, "fixed_range_arithmetic_only": True},
            vacuity=_vacuity(fixed_total, planned=True),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[6],
            theorem_or_event=_event("unstructured_4608_coordinate_event", "exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event", "SEPARATE_CHECKED_EVENT_WITH_VISIT_PREMISE", checked_outer_mass=Fraction(1, 20), planned_allocation=None),
            certification_status=(checked_status if unstructured["all_augmented_source_rows_visited"] else "PREMISE_FAILED_ZERO_AUGMENTED_SOURCE_VISIT"),
            empirical=generic12["score"]["empirical_corrected_score"],
            risk=generic12["risk"],
            radius=unstructured["eta_augmented"],
            residual=unstructured_residual,
            total=unstructured_total,
            confidence={"delta_risk": "1/40", "delta_transition": "1/40", "delta_total": "1/20", "coordinate_prior_mass": "1/4608", "risk_tilt": "1/16", "transition_tilt": "1/64"},
            settings={"candidate_index": 1, "depth": 12, "coordinate_count": 2304, "oriented_coordinate_count": 4608, "all_augmented_source_rows_visited": unstructured["all_augmented_source_rows_visited"]},
            vacuity=_vacuity(unstructured_total, premise_ok=unstructured["all_augmented_source_rows_visited"]),
        ),
    ]
    _exact([row["endpoint_id"] for row in rows], list(ROW_ORDER), "receipt row order")
    _validate_planned_reporting_rows(rows)

    trace_input_prefix = [dict(row) for row in trace_manifest["inputs"]]
    receipt_only_inputs = [
        _manifest_row("trace_binary", trace_path, trace_raw),
        _manifest_row("trace_counts", counts_path, counts_raw),
        _manifest_row("trace_manifest", trace_manifest_path, trace_manifest_raw),
        _manifest_row("pilot_selected_potential_data", selected_data_path, selected_data_raw),
        _manifest_row("known_kernel_receipt_source", known_kernel_source_path, known_kernel_source_raw),
        _manifest_row("persistence_confidence_source", persistence_source_path, persistence_source_raw),
        _manifest_row("structured_ope_source", structured_source_path, structured_source_raw),
        _manifest_row("sharp_structured_ope_source", sharp_structured_source_path, sharp_structured_source_raw),
        _manifest_row("sharp_receipt_core_source", sharp_receipt_core_path, sharp_receipt_core_raw),
    ]

    adaptive_stats = []
    for row in score_catalog:
        adaptive_stats.append(
            {
                **{key: row[key] for key in ("candidate_index", "depth_index", "depth", "posterior_index", "policy_index", "predictor_index")},
                "score_summary": _public_score_summary(row["summary"]),
            }
        )
    adaptive_minimum = [
        {"indices": row["indices"], "total_certified_rhs": number(row["total_certified_rhs"])}
        for row in adaptive["catalog_minimum_certificate"]
    ]
    persistence_catalog = [
        {
            "candidate_index": candidate_index,
            "persistence_tilt_index": tilt_index,
            "summary": _public_fraction_dict(summary),
        }
        for (candidate_index, tilt_index), summary in sorted(adaptive["persistence_summaries"].items())
    ]
    unstructured_public = {
        "all_augmented_source_rows_visited": unstructured["all_augmented_source_rows_visited"],
        "coordinate_count": unstructured["coordinate_count"],
        "oriented_coordinate_count": unstructured["oriented_coordinate_count"],
        "eta_augmented": number(unstructured["eta_augmented"]),
        "source_rows": [
            {
                **{key: row[key] for key in ("source", "visits", "premise_visited")},
                "empirical_row_tv": number(row["empirical_row_tv"]),
                "coordinate_radius_sum_half": number(row["coordinate_radius_sum_half"]),
                "row_eta": number(row["row_eta"]),
                "coordinate_radii": [number(value) for value in row["coordinate_radii"]],
            }
            for row in unstructured["source_rows"]
        ],
    }

    receipt = {
        "schema_version": RECEIPT_SCHEMA,
        "receipt_version": RECEIPT_VERSION,
        "artifact_status": ARTIFACT_STATUS,
        "protocol_binding": {
            "path": _display(protocol_path),
            "bytes": len(protocol_raw),
            "sha256": sha256_bytes(protocol_raw),
            "commit": PROTOCOL_COMMIT,
            "tree": PROTOCOL_TREE,
        },
        "trace_manifest_binding": {
            "path": _display(trace_manifest_path),
            "bytes": len(trace_manifest_raw),
            "sha256": sha256_bytes(trace_manifest_raw),
            "schema_version": TRACE_MANIFEST_SCHEMA,
            "trace_version": TRACE_VERSION,
        },
        "registration": trace_manifest["registration"],
        "beacon": trace_manifest["beacon"],
        "code_freeze": trace_manifest["code_freeze"],
        "inputs": trace_input_prefix + receipt_only_inputs,
        "trace_summary": {
            "horizon": n,
            "initial_state": states[0],
            "dummy_initial_action": actions[0],
            "final_state": states[-1],
            "final_action": actions[-1],
            "first_scored_transition": [states[0], actions[1], states[1]],
            "terminal_scored_transition": [states[n - 1], actions[n], states[n]],
            "action_indexing": "score k uses A_(k+1), never dummy A_0 or A_k",
            "trace_sha256": sha256_bytes(trace_raw),
            "physical_transition_total": n,
            "augmented_transition_total": n,
        },
        "deterministic_tables": {
            "computed_before_trace_decode": True,
            "candidate_ids": list(CANDIDATE_IDS),
            "candidate_gammas": [rational_text(value) for value in CANDIDATE_GAMMAS],
            "depths": list(DEPTHS),
            "tilts": [rational_text(value) for value in TILTS],
            "selected_primary": {
                "potential": [number(value) for value in selected["potential"]],
                "actual_span": number(selected["actual_span"]),
                "candidate_drift": [number(value) for value in selected["drift"]],
                "candidate_drift_oscillation_bound": number(PRIMARY_DRIFT),
                "refresh_sensitivity": [number(value) for value in selected["refresh_sensitivity"]],
                "refresh_sensitivity_oscillation_bound": number(PRIMARY_SENSITIVITY),
            },
            "oracle_true_kernel": {
                "true_gamma": "149/200",
                "potential": [number(value) for value in oracle["potential"]],
                "actual_span": number(oracle["actual_span"]),
                "drift": [number(value) for value in oracle["drift"]],
                "drift_oscillation": number(oracle["drift_oscillation"]),
            },
        },
        "sufficient_statistics": {
            "physical_transition_histogram": histogram,
            "physical_source_visits": physical["source_state_visits"],
            "physical_state_action_counts": physical["state_action_counts"],
            "augmented_transition_histogram": augmented_edges,
            "augmented_source_visits": augmented_visits,
            "all_augmented_source_rows_visited": all(visit > 0 for visit in augmented_visits),
            "persistence_hit_count": hits,
            "persistence_miss_count": n - hits,
            "primary_persistence": _public_fraction_dict(primary_persistence),
            "primary_score": _public_score_summary(primary_score),
            "oracle_score": _public_score_summary(oracle_score),
            "adaptive_score_catalog": adaptive_stats,
            "adaptive_persistence_catalog": persistence_catalog,
            "adaptive_selected_indices": adaptive_selected["indices"],
            "adaptive_exact_minimum": number(adaptive_selected["total_certified_rhs"]),
            "adaptive_catalog_minimum_certificate": adaptive_minimum,
            "fixed_range_persistence": _public_fraction_dict(fixed_eta),
            "unstructured_transition": unstructured_public,
        },
        "reporting_rows": rows,
        "dynamic_encountered_risk": causal_beta_summaries(states, actions),
        "nonclaims": list(NONCLAIMS),
    }
    _keys(
        receipt,
        {
            "schema_version", "receipt_version", "artifact_status", "protocol_binding",
            "trace_manifest_binding", "registration", "beacon", "code_freeze", "inputs",
            "trace_summary", "deterministic_tables", "sufficient_statistics", "reporting_rows",
            "dynamic_encountered_risk", "nonclaims",
        },
        "receipt top-level",
    )
    return receipt


def _lean_rat(text: str) -> str:
    value = Fraction(text)
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def _render_list(values: Sequence[str], indent: int = 2) -> str:
    if not values:
        return "[]"
    pad = " " * indent
    return "[\n" + ",\n".join(f"{pad}{value}" for value in values) + "\n" + " " * (indent - 2) + "]"


def _render_nested_nat(value: Any, indent: int = 2) -> str:
    if isinstance(value, bool) or not isinstance(value, list):
        if isinstance(value, bool) or not isinstance(value, int):
            raise ValueError("Lean Nat table contains a non-integer")
        return str(value)
    return _render_list([_render_nested_nat(item, indent + 2) for item in value], indent)


def render_lean(receipt: dict[str, Any]) -> bytes:
    stats = receipt["sufficient_statistics"]
    histogram = stats["physical_transition_histogram"]
    row_definitions = "\n\n".join(
        f"private def prospectivePhysicalRow_{state}_{action} : List Nat := "
        f"{_render_list([str(value) for value in histogram[state][action]])}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    row_branches = "\n".join(
        f"  | {state}, {action} => prospectivePhysicalRow_{state}_{action}.getD nextState.val 0"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    primary = receipt["reporting_rows"][0]
    primary_score = stats["primary_score"]
    score_row_branches = "\n".join(
        f"  | {state}, {action} => {_lean_rat(primary_score['row_sums'][state][action]['rational'])}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    square_row_branches = "\n".join(
        f"  | {state}, {action} => {_lean_rat(primary_score['row_sum_squares'][state][action]['rational'])}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    hit_row_branches = "\n".join(
        f"  | {state}, {action} => {histogram[state][action][queue_step(state, action)]}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    score_state_branches = "\n".join(
        f"  | {state} => {_lean_rat(str(sum((Fraction(primary_score['row_sums'][state][action]['rational']) for action in range(ACTION_COUNT)), Fraction(0))))}"
        for state in range(STATE_COUNT)
    )
    square_state_branches = "\n".join(
        f"  | {state} => {_lean_rat(str(sum((Fraction(primary_score['row_sum_squares'][state][action]['rational']) for action in range(ACTION_COUNT)), Fraction(0))))}"
        for state in range(STATE_COUNT)
    )
    hit_state_branches = "\n".join(
        f"  | {state} => {sum(histogram[state][action][queue_step(state, action)] for action in range(ACTION_COUNT))}"
        for state in range(STATE_COUNT)
    )
    certificate_tactic_definitions = """prospectivePhysicalTransitionHistogram,
        prospectiveActualScoreRow, prospectiveActualSquareRow,
        prospectiveActualPersistenceHitRowCount,
        prospectiveScoreRowSum, prospectiveSquareRowSum,
        prospectivePersistenceHitRowCount,
        knownKernelSelectedTransitionScore, knownKernelSelectedPotential,
        knownKernelPotentialSpan, selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, candidateKernelStepStateAction,
        ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable,
        ControlledQueueData.candidateKernelStepByRow, Fin.sum_univ_succ"""
    row_certificates = "\n\n".join(
        f"""private theorem prospectiveCertificate_{state}_{action} :
    ProspectiveRowCertificate ({state} : PhysicalState) ({action} : Action) := by
  constructor
  · norm_num [prospectivePhysicalRow_{state}_{action}, {certificate_tactic_definitions}]
  · norm_num [prospectivePhysicalRow_{state}_{action}, {certificate_tactic_definitions}]
  · norm_num [prospectivePhysicalRow_{state}_{action}, {certificate_tactic_definitions}]"""
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    certificate_dispatch = "\n".join(
        f"  · exact prospectiveCertificate_{state}_{action}"
        for state in range(STATE_COUNT)
        for action in range(ACTION_COUNT)
    )
    state_certificates = "\n\n".join(
        f"""private theorem prospectiveStateCertificate_{state} :
    ProspectiveStateSubtotalCertificate ({state} : PhysicalState) := by
  constructor
  · norm_num [prospectiveScoreRowSum, prospectiveScoreStateSum,
      Fin.sum_univ_succ]
  · norm_num [prospectiveSquareRowSum, prospectiveSquareStateSum,
      Fin.sum_univ_succ]
  · norm_num [prospectivePersistenceHitRowCount,
      prospectivePersistenceHitStateCount, Fin.sum_univ_succ]"""
        for state in range(STATE_COUNT)
    )
    state_certificate_dispatch = "\n".join(
        f"  · exact prospectiveStateCertificate_{state}"
        for state in range(STATE_COUNT)
    )
    primary_upper_fraction = Fraction(primary["total_certified_rhs"]["rational"])
    threshold_corollary = ""
    if primary_upper_fraction < PRIMARY_THRESHOLD:
        threshold_corollary = f'''\n/-- The preregistered strict threshold follows only because the generated exact
rational upper bound is below `1/10`.  The histogram premise remains explicit. -/
theorem prospectiveSharpStructuredEndpoint_lt_one_tenth
    (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram
      prospectivePhysicalTransitionHistogram sharpStructuredHorizon path) :
    sharpStructuredOPEBoundary sharpStructuredHorizon path < (1 / 10 : ℝ) := by
  exact lt_of_le_of_lt (prospectiveSharpStructuredEndpoint_le path hhist)
    (by norm_num [prospectivePrimaryUpper])
'''
    threshold_axiom_check = ""
    if primary_upper_fraction < PRIMARY_THRESHOLD:
        threshold_axiom_check = """
#check FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData.prospectiveSharpStructuredEndpoint_lt_one_tenth
#print axioms FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData.prospectiveSharpStructuredEndpoint_lt_one_tenth
"""
    row_ids = [f'"{endpoint}"' for endpoint in ROW_ORDER]
    row_totals = [
        _lean_rat(row["total_certified_rhs"]["rational"])
        for row in receipt["reporting_rows"]
    ]
    selected = stats["adaptive_selected_indices"]
    code_freeze = receipt["code_freeze"]
    registration = receipt["registration"]
    beacon = receipt["beacon"]
    content = f'''/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueSharpStructuredReceiptCore

/-!
# Generated prospective structured controlled-queue receipt data

This generated arithmetic module is rendered byte-for-byte by
`scripts/generate_controlled_queue_prospective_receipt.py`.  It contains the
frozen physical histogram and exact rational sufficient statistics.  It does
not prove the source hashes, the beacon signature, registration chronology,
good-event membership, or a confidence theorem.  The oracle true-kernel and
fixed-range rows remain `PLANNED_NOT_CHECKED`.
-/

namespace FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData

open FormalSLT.Applications.ControlledQueue
open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

noncomputable section

def schemaVersion : String := "{RECEIPT_SCHEMA}"
def receiptVersion : String := "{RECEIPT_VERSION}"
def artifactStatus : String := "{ARTIFACT_STATUS}"

/-- Provenance strings are labels, not kernel-verified hash propositions. -/
def sourceProtocolSHA256 : String := "{receipt['protocol_binding']['sha256']}"
def sourceTraceSHA256 : String := "{receipt['trace_summary']['trace_sha256']}"
def sourceTraceManifestSHA256 : String := "{receipt['trace_manifest_binding']['sha256']}"
def codeFreezeCommit : String := "{code_freeze['commit']}"
def codeFreezeTree : String := "{code_freeze['tree']}"
def osfRegistrationID : String := "{registration['id']}"
def quicknetRound : Nat := {beacon['round']}

def receiptHorizon : Nat := {receipt['trace_summary']['horizon']}
def receiptInitialStateIndex : Nat := {receipt['trace_summary']['initial_state']}
def receiptInitialActionIndex : Nat := {receipt['trace_summary']['dummy_initial_action']}

{row_definitions}

/-- Frozen 24-by-2-by-24 physical histogram.  Its indexing is current state,
next action `A_(k+1)`, and next state. -/
def prospectivePhysicalTransitionHistogram : PhysicalTransitionHistogram :=
  fun state action nextState =>
    match state.val, action.val with
{row_branches}
    | _, _ => 0

/-- The same histogram as nested public data for downstream receipt checks. -/
def prospectivePhysicalTransitionCounts : List (List (List Nat)) :=
  {_render_nested_nat(histogram)}

def prospectiveAugmentedSourceVisits : List Nat :=
  {_render_list([str(value) for value in stats['augmented_source_visits']])}

def prospectivePersistenceHitCount : Nat := {stats['persistence_hit_count']}
def prospectivePrimaryScoreSum : ℚ := {_lean_rat(primary_score['sum']['rational'])}
def prospectivePrimaryScoreSquareSum : ℚ := {_lean_rat(primary_score['sum_squares']['rational'])}
def prospectivePrimaryScoreBesselQ : ℚ := {_lean_rat(primary_score['bessel_q']['rational'])}
def prospectivePrimaryScoreAffinePenalty : ℚ := {_lean_rat(primary_score['hybrid_affine_upper']['rational'])}

def prospectivePrimaryEmpiricalCorrectedScore : ℚ :=
  {_lean_rat(primary['empirical_corrected_score']['rational'])}
def prospectivePrimaryRiskCorrection : ℚ :=
  {_lean_rat(primary['risk_statistical_correction']['rational'])}
def prospectivePrimaryPersistenceBudget : ℚ :=
  {_lean_rat(primary['persistence_or_transition_radius']['rational'])}
def prospectivePrimaryResidual : ℚ :=
  {_lean_rat(primary['candidate_or_truncation_residual']['rational'])}
def prospectivePrimaryUpper : ℚ :=
  {_lean_rat(primary['total_certified_rhs']['rational'])}

def prospectiveAdaptiveSelectedIndices : List Nat :=
  {_render_list([str(value) for value in selected])}

def prospectiveEndpointIDs : List String := {_render_list(row_ids)}
def prospectiveEndpointUpperBounds : List ℚ := {_render_list(row_totals)}

def oracleTrueKernelCertificationStatus : String :=
  "PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE"

def fixedRangeCertificationStatus : String :=
  "PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE"

/-! ## Bounded arithmetic certificates and conditional core instantiation -/

private def prospectiveScoreRowSum
    (state : PhysicalState) (action : Action) : ℚ :=
  match state.val, action.val with
{score_row_branches}
  | _, _ => 0

private def prospectiveSquareRowSum
    (state : PhysicalState) (action : Action) : ℚ :=
  match state.val, action.val with
{square_row_branches}
  | _, _ => 0

private def prospectivePersistenceHitRowCount
    (state : PhysicalState) (action : Action) : Nat :=
  match state.val, action.val with
{hit_row_branches}
  | _, _ => 0

private def prospectiveScoreStateSum (state : PhysicalState) : ℚ :=
  match state.val with
{score_state_branches}
  | _ => 0

private def prospectiveSquareStateSum (state : PhysicalState) : ℚ :=
  match state.val with
{square_state_branches}
  | _ => 0

private def prospectivePersistenceHitStateCount
    (state : PhysicalState) : Nat :=
  match state.val with
{hit_state_branches}
  | _ => 0

private noncomputable def prospectiveActualScoreRow
    (state : PhysicalState) (action : Action) : ℝ :=
  ∑ nextState : PhysicalState,
    (prospectivePhysicalTransitionHistogram state action nextState : ℝ) *
      knownKernelSelectedTransitionScore state action nextState

private noncomputable def prospectiveActualSquareRow
    (state : PhysicalState) (action : Action) : ℝ :=
  ∑ nextState : PhysicalState,
    (prospectivePhysicalTransitionHistogram state action nextState : ℝ) *
      (knownKernelSelectedTransitionScore state action nextState) ^ 2

private def prospectiveActualPersistenceHitRowCount
    (state : PhysicalState) (action : Action) : Nat :=
  prospectivePhysicalTransitionHistogram state action
    (candidateKernelStepStateAction state action)

private structure ProspectiveRowCertificate
    (state : PhysicalState) (action : Action) : Prop where
  score :
    prospectiveActualScoreRow state action =
      (prospectiveScoreRowSum state action : ℝ)
  square :
    prospectiveActualSquareRow state action =
      (prospectiveSquareRowSum state action : ℝ)
  hit :
    prospectiveActualPersistenceHitRowCount state action =
      prospectivePersistenceHitRowCount state action

{row_certificates}

private theorem prospectiveRowCertificate
    (state : PhysicalState) (action : Action) :
    ProspectiveRowCertificate state action := by
  fin_cases state <;> fin_cases action
{certificate_dispatch}

private structure ProspectiveStateSubtotalCertificate
    (state : PhysicalState) : Prop where
  score :
    (∑ action : Action, (prospectiveScoreRowSum state action : ℝ)) =
      (prospectiveScoreStateSum state : ℝ)
  square :
    (∑ action : Action, (prospectiveSquareRowSum state action : ℝ)) =
      (prospectiveSquareStateSum state : ℝ)
  hit :
    (∑ action : Action, prospectivePersistenceHitRowCount state action) =
      prospectivePersistenceHitStateCount state

{state_certificates}

private theorem prospectiveStateSubtotalCertificate
    (state : PhysicalState) : ProspectiveStateSubtotalCertificate state := by
  fin_cases state
{state_certificate_dispatch}

private theorem prospectiveHistogramScoreSum_eq :
    sharpStructuredHistogramScoreSum prospectivePhysicalTransitionHistogram =
      (prospectivePrimaryScoreSum : ℝ) := by
  unfold sharpStructuredHistogramScoreSum
  change (∑ state : PhysicalState, ∑ action : Action,
      prospectiveActualScoreRow state action) =
    (prospectivePrimaryScoreSum : ℝ)
  calc
    (∑ state : PhysicalState, ∑ action : Action,
        prospectiveActualScoreRow state action) =
        ∑ state : PhysicalState, ∑ action : Action,
          (prospectiveScoreRowSum state action : ℝ) := by
      apply Finset.sum_congr rfl
      intro state _hstate
      apply Finset.sum_congr rfl
      intro action _haction
      exact (prospectiveRowCertificate state action).score
    _ = (prospectivePrimaryScoreSum : ℝ) := by
      calc
        (∑ state : PhysicalState, ∑ action : Action,
            (prospectiveScoreRowSum state action : ℝ)) =
            ∑ state : PhysicalState,
              (prospectiveScoreStateSum state : ℝ) := by
          apply Finset.sum_congr rfl
          intro state _hstate
          exact (prospectiveStateSubtotalCertificate state).score
        _ = (prospectivePrimaryScoreSum : ℝ) := by
          norm_num [prospectiveScoreStateSum, prospectivePrimaryScoreSum,
            Fin.sum_univ_succ]

private theorem prospectiveHistogramSquaredScoreSum_eq :
    sharpStructuredHistogramSquaredScoreSum
        prospectivePhysicalTransitionHistogram =
      (prospectivePrimaryScoreSquareSum : ℝ) := by
  unfold sharpStructuredHistogramSquaredScoreSum
  change (∑ state : PhysicalState, ∑ action : Action,
      prospectiveActualSquareRow state action) =
    (prospectivePrimaryScoreSquareSum : ℝ)
  calc
    (∑ state : PhysicalState, ∑ action : Action,
        prospectiveActualSquareRow state action) =
        ∑ state : PhysicalState, ∑ action : Action,
          (prospectiveSquareRowSum state action : ℝ) := by
      apply Finset.sum_congr rfl
      intro state _hstate
      apply Finset.sum_congr rfl
      intro action _haction
      exact (prospectiveRowCertificate state action).square
    _ = (prospectivePrimaryScoreSquareSum : ℝ) := by
      calc
        (∑ state : PhysicalState, ∑ action : Action,
            (prospectiveSquareRowSum state action : ℝ)) =
            ∑ state : PhysicalState,
              (prospectiveSquareStateSum state : ℝ) := by
          apply Finset.sum_congr rfl
          intro state _hstate
          exact (prospectiveStateSubtotalCertificate state).square
        _ = (prospectivePrimaryScoreSquareSum : ℝ) := by
          norm_num [prospectiveSquareStateSum,
            prospectivePrimaryScoreSquareSum, Fin.sum_univ_succ]

private theorem prospectiveHistogramPersistenceHitCount_eq :
    sharpStructuredHistogramPersistenceHitCount
        prospectivePhysicalTransitionHistogram =
      prospectivePersistenceHitCount := by
  unfold sharpStructuredHistogramPersistenceHitCount
  change (∑ state : PhysicalState, ∑ action : Action,
      prospectiveActualPersistenceHitRowCount state action) =
    prospectivePersistenceHitCount
  calc
    (∑ state : PhysicalState, ∑ action : Action,
        prospectiveActualPersistenceHitRowCount state action) =
        ∑ state : PhysicalState, ∑ action : Action,
          prospectivePersistenceHitRowCount state action := by
      apply Finset.sum_congr rfl
      intro state _hstate
      apply Finset.sum_congr rfl
      intro action _haction
      exact (prospectiveRowCertificate state action).hit
    _ = prospectivePersistenceHitCount := by
      calc
        (∑ state : PhysicalState, ∑ action : Action,
            prospectivePersistenceHitRowCount state action) =
            ∑ state : PhysicalState,
              prospectivePersistenceHitStateCount state := by
          apply Finset.sum_congr rfl
          intro state _hstate
          exact (prospectiveStateSubtotalCertificate state).hit
        _ = prospectivePersistenceHitCount := by
          norm_num [prospectivePersistenceHitStateCount,
            prospectivePersistenceHitCount, Fin.sum_univ_succ]

private theorem prospectiveHistogramUpper_eq :
    sharpStructuredHistogramUpper prospectivePhysicalTransitionHistogram =
      (prospectivePrimaryUpper : ℝ) := by
  unfold sharpStructuredHistogramUpper
    sharpStructuredHistogramRiskUpper
    sharpStructuredHistogramScoreAffinePenalty
    sharpStructuredHistogramScoreBesselQ
    sharpStructuredHistogramResidualUpper
    sharpStructuredHistogramPersistenceBudgetUpper
    sharpStructuredHistogramPersistenceRadiusUpper
    sharpStructuredHistogramPersistenceAffinePenalty
    sharpStructuredHistogramPersistenceBesselQ
  rw [prospectiveHistogramScoreSum_eq,
    prospectiveHistogramSquaredScoreSum_eq,
    prospectiveHistogramPersistenceHitCount_eq]
  norm_num [
    prospectivePrimaryScoreSum, prospectivePrimaryScoreSquareSum,
    prospectivePersistenceHitCount, prospectivePrimaryUpper,
    sharpStructuredHorizon,
    knownKernelNormalizedScale, knownKernelPotentialSpan,
    selectedNormalizedScale, selectedPotentialSpan,
    sharpSelectedCandidateDriftOscillation,
    sharpSelectedRefreshSensitivityOscillation,
    candidatePersistenceHitProbability, candidatePersistenceParameter,
    nominalCandidateIndex, persistenceHitProbability, candidateGamma,
    candidateGammaRat, ControlledQueueData.candidateGammaTable]

/-- Conditional instantiation of the pre-data histogram reduction.  This
theorem assumes only the histogram/path relation.  It does not assert that a
named path is in a theorem-produced good event or verify any external bytes. -/
theorem prospectiveSharpStructuredEndpoint_le
    (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram
      prospectivePhysicalTransitionHistogram sharpStructuredHorizon path) :
    sharpStructuredOPEBoundary sharpStructuredHorizon path ≤
      (prospectivePrimaryUpper : ℝ) := by
  calc
    sharpStructuredOPEBoundary sharpStructuredHorizon path ≤
        sharpStructuredHistogramUpper prospectivePhysicalTransitionHistogram :=
      sharpStructuredReceiptBoundary_evaluation_of_histogram
        prospectivePhysicalTransitionHistogram path hhist
    _ = (prospectivePrimaryUpper : ℝ) := prospectiveHistogramUpper_eq
{threshold_corollary}

end
end FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData

#check FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData.prospectiveSharpStructuredEndpoint_le
#print axioms FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData.prospectiveSharpStructuredEndpoint_le
{threshold_axiom_check}
'''
    return content.encode("utf-8")


def build_receipt_manifest(
    *,
    receipt: dict[str, Any],
    receipt_path: Path,
    receipt_raw: bytes,
    lean_path: Path,
    lean_raw: bytes,
    generator_path: Path,
    generator_raw: bytes,
    verifier_path: Path,
    verifier_raw: bytes,
) -> dict[str, Any]:
    return {
        "artifact_status": ARTIFACT_STATUS,
        "receipt_version": RECEIPT_VERSION,
        "schema_version": RECEIPT_MANIFEST_SCHEMA,
        "protocol_binding": receipt["protocol_binding"],
        "trace_manifest_binding": receipt["trace_manifest_binding"],
        "registration": receipt["registration"],
        "beacon": receipt["beacon"],
        "code_freeze": receipt["code_freeze"],
        "generator": {
            "bytes": len(generator_raw),
            "path": _display(generator_path),
            "revision": GENERATOR_REVISION,
            "sha256": sha256_bytes(generator_raw),
        },
        "independent_verifier": {
            "bytes": len(verifier_raw),
            "path": _display(verifier_path),
            "sha256": sha256_bytes(verifier_raw),
        },
        "inputs": receipt["inputs"],
        "outputs": [
            _manifest_row("receipt", receipt_path, receipt_raw),
            _manifest_row("lean_data", lean_path, lean_raw),
        ],
        "manifest_note": "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "nonclaims": list(NONCLAIMS),
    }


def _verify_code_freeze_files(
    trace_manifest: dict[str, Any], code_paths: dict[str, Path]
) -> dict[str, bytes]:
    rows = trace_manifest["code_freeze"]["code_files"]
    result: dict[str, bytes] = {}
    for row in rows:
        role = row["role"]
        if role not in code_paths:
            _fail(f"no current code path supplied for frozen role {role}")
        raw = _read(code_paths[role], f"code-freeze file {role}")
        _exact(_display(code_paths[role]), row["path"], f"code-freeze path {role}")
        _exact(len(raw), row["bytes"], f"code-freeze byte length {role}")
        _exact(sha256_bytes(raw), row["sha256"], f"code-freeze SHA-256 {role}")
        result[role] = raw
    return result


def expected_artifacts(
    *,
    protocol_path: Path,
    trace_path: Path,
    counts_path: Path,
    trace_manifest_path: Path,
    model_input_path: Path,
    model_manifest_path: Path,
    model_tables_path: Path,
    selected_data_path: Path,
    known_kernel_source_path: Path,
    persistence_source_path: Path,
    structured_source_path: Path,
    sharp_structured_source_path: Path,
    sharp_receipt_core_path: Path,
    receipt_path: Path,
    lean_path: Path,
    code_paths: dict[str, Path] | None = None,
) -> tuple[bytes, bytes, bytes]:
    protocol_raw = _read(protocol_path, "protocol")
    protocol = validate_protocol(protocol_raw)
    model_input_raw = _read(model_input_path, "model input")
    model_manifest_raw = _read(model_manifest_path, "model manifest")
    model_tables_raw = _read(model_tables_path, "model tables")
    selected_data_raw = _read(selected_data_path, "selected potential data")
    known_kernel_source_raw = _read(known_kernel_source_path, "known-kernel source")
    persistence_source_raw = _read(persistence_source_path, "persistence source")
    structured_source_raw = _read(structured_source_path, "structured-OPE source")
    sharp_structured_source_raw = _read(sharp_structured_source_path, "sharp structured-OPE source")
    sharp_receipt_core_raw = _read(sharp_receipt_core_path, "sharp receipt-core source")

    for binding_name, path, raw in (
        ("model_input", model_input_path, model_input_raw),
        ("model_manifest", model_manifest_path, model_manifest_raw),
        ("model_tables", model_tables_path, model_tables_raw),
        ("pilot_selected_potential_data", selected_data_path, selected_data_raw),
        ("known_kernel_receipt_source", known_kernel_source_path, known_kernel_source_raw),
        ("persistence_confidence_source", persistence_source_path, persistence_source_raw),
        ("structured_ope_source", structured_source_path, structured_source_raw),
    ):
        _validate_bound_source(protocol, binding_name, path, raw)
    _object(parse_json_bytes(model_input_raw, "model input"), "model input")
    _object(parse_json_bytes(model_manifest_raw, "model manifest"), "model manifest")
    model = parse_model_tables(model_tables_raw)

    # The oracle and all candidate/depth tables are frozen before even decoding
    # the future trace.  This call order is a tested chronology invariant.
    deterministic = compute_deterministic_tables(model)
    trace_raw = _read(trace_path, "prospective trace")
    deterministic, states, actions = load_deterministic_then_decode(
        model,
        trace_raw,
        deterministic_builder=lambda _model: deterministic,
    )
    counts_raw = _read(counts_path, "prospective trace counts")
    _counts, physical = _validate_trace_counts(counts_raw, trace_raw, states, actions)
    trace_manifest_raw = _read(trace_manifest_path, "prospective trace manifest")
    trace_manifest = validate_trace_manifest(
        trace_manifest_raw,
        protocol_path=protocol_path,
        protocol_raw=protocol_raw,
        model_input_path=model_input_path,
        model_input_raw=model_input_raw,
        model_manifest_path=model_manifest_path,
        model_manifest_raw=model_manifest_raw,
        model_tables_path=model_tables_path,
        model_tables_raw=model_tables_raw,
        trace_path=trace_path,
        trace_raw=trace_raw,
        counts_path=counts_path,
        counts_raw=counts_raw,
    )
    freeze_commit = trace_manifest["code_freeze"]["commit"]
    _verify_code_freeze_source(
        freeze_commit,
        sharp_structured_source_path,
        sharp_structured_source_raw,
        "sharp_structured_ope_source",
    )
    _verify_code_freeze_source(
        freeze_commit,
        sharp_receipt_core_path,
        sharp_receipt_core_raw,
        "sharp_receipt_core_source",
    )

    if code_paths is None:
        code_paths = {
            "trace_generator": ROOT / "scripts" / "generate_controlled_queue_prospective_trace.py",
            "trace_verifier": ROOT / "scripts" / "verify_controlled_queue_prospective_trace.py",
            "receipt_generator": ROOT / GENERATOR_PATH,
            "receipt_verifier": ROOT / VERIFIER_PATH,
        }
    code_raw = _verify_code_freeze_files(trace_manifest, code_paths)
    receipt = build_receipt(
        protocol=protocol,
        protocol_path=protocol_path,
        protocol_raw=protocol_raw,
        trace_path=trace_path,
        trace_raw=trace_raw,
        counts_path=counts_path,
        counts_raw=counts_raw,
        trace_manifest_path=trace_manifest_path,
        trace_manifest_raw=trace_manifest_raw,
        trace_manifest=trace_manifest,
        model_input_path=model_input_path,
        model_input_raw=model_input_raw,
        model_manifest_path=model_manifest_path,
        model_manifest_raw=model_manifest_raw,
        model_tables_path=model_tables_path,
        model_tables_raw=model_tables_raw,
        selected_data_path=selected_data_path,
        selected_data_raw=selected_data_raw,
        known_kernel_source_path=known_kernel_source_path,
        known_kernel_source_raw=known_kernel_source_raw,
        persistence_source_path=persistence_source_path,
        persistence_source_raw=persistence_source_raw,
        structured_source_path=structured_source_path,
        structured_source_raw=structured_source_raw,
        sharp_structured_source_path=sharp_structured_source_path,
        sharp_structured_source_raw=sharp_structured_source_raw,
        sharp_receipt_core_path=sharp_receipt_core_path,
        sharp_receipt_core_raw=sharp_receipt_core_raw,
        deterministic=deterministic,
        states=states,
        actions=actions,
        physical=physical,
    )
    receipt_raw = canonical_json_bytes(receipt)
    lean_raw = render_lean(receipt)
    manifest = build_receipt_manifest(
        receipt=receipt,
        receipt_path=receipt_path,
        receipt_raw=receipt_raw,
        lean_path=lean_path,
        lean_raw=lean_raw,
        generator_path=code_paths["receipt_generator"],
        generator_raw=code_raw["receipt_generator"],
        verifier_path=code_paths["receipt_verifier"],
        verifier_raw=code_raw["receipt_verifier"],
    )
    return receipt_raw, canonical_json_bytes(manifest), lean_raw


def _path_identity(path: Path) -> str:
    return unicodedata.normalize("NFC", path.absolute().as_posix()).casefold()


def _same_target(left: Path, right: Path) -> bool:
    if _path_identity(left) == _path_identity(right):
        return True
    try:
        return left.exists() and right.exists() and left.samefile(right)
    except OSError:
        return False


def _has_symlink_component(path: Path) -> bool:
    absolute = path.absolute()
    current = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        current = current / part
        if current.is_symlink():
            return True
    return False


def _require_exact_path(actual: Path, expected: Path, role: str) -> None:
    if actual.absolute() != expected.absolute():
        _fail(f"{role} must use the canonical path {expected}, got {actual}")
    if _has_symlink_component(actual):
        _fail(f"{role} path contains a symbolic-link component: {actual}")


def validate_artifact_paths(inputs: dict[str, Path], outputs: dict[str, Path]) -> None:
    for role, path in inputs.items():
        if _has_symlink_component(path):
            _fail(f"input {role} path contains a symbolic-link component: {path}")
    output_items = list(outputs.items())
    for index, (left_role, left) in enumerate(output_items):
        if _has_symlink_component(left):
            _fail(f"output {left_role} path contains a symbolic-link component: {left}")
        for right_role, right in output_items[index + 1 :]:
            if _same_target(left, right):
                _fail(f"output paths alias: {left_role} and {right_role}")
        for input_role, input_path in inputs.items():
            if _same_target(left, input_path):
                _fail(f"output {left_role} aliases protected input {input_role}")


def _exclusive_atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError as error:
            raise ProspectiveReceiptError(f"refusing to overwrite existing artifact: {path}") from error
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def write_artifacts_manifest_last(
    receipt_path: Path,
    receipt_raw: bytes,
    lean_path: Path,
    lean_raw: bytes,
    manifest_path: Path,
    manifest_raw: bytes,
    *,
    writer: Callable[[Path, bytes], None] = _exclusive_atomic_write,
) -> None:
    writer(receipt_path, receipt_raw)
    writer(lean_path, lean_raw)
    writer(manifest_path, manifest_raw)


def _check_exact(path: Path, expected: bytes) -> bool:
    try:
        actual = path.read_bytes()
    except FileNotFoundError:
        print(f"missing generated artifact: {_display(path)}", file=sys.stderr)
        return False
    if actual != expected:
        print(f"stale generated artifact: {_display(path)}", file=sys.stderr)
        return False
    return True


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    parser.add_argument("--trace", type=Path, default=DEFAULT_TRACE)
    parser.add_argument("--counts", type=Path, default=DEFAULT_COUNTS)
    parser.add_argument("--trace-manifest", type=Path, default=DEFAULT_TRACE_MANIFEST)
    parser.add_argument("--model-input", type=Path, default=DEFAULT_MODEL_INPUT)
    parser.add_argument("--model-manifest", type=Path, default=DEFAULT_MODEL_MANIFEST)
    parser.add_argument("--model-tables", type=Path, default=DEFAULT_MODEL_TABLES)
    parser.add_argument("--selected-data", type=Path, default=DEFAULT_SELECTED_DATA)
    parser.add_argument("--known-kernel-source", type=Path, default=DEFAULT_KNOWN_KERNEL_SOURCE)
    parser.add_argument("--persistence-source", type=Path, default=DEFAULT_PERSISTENCE_SOURCE)
    parser.add_argument("--structured-source", type=Path, default=DEFAULT_STRUCTURED_SOURCE)
    parser.add_argument("--sharp-structured-source", type=Path, default=DEFAULT_SHARP_STRUCTURED_SOURCE)
    parser.add_argument("--sharp-receipt-core", type=Path, default=DEFAULT_SHARP_RECEIPT_CORE)
    parser.add_argument("--receipt-output", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--manifest-output", type=Path, default=DEFAULT_RECEIPT_MANIFEST)
    parser.add_argument("--lean-output", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--check", action="store_true", help="read-only byte-exact artifact check")
    return parser.parse_args(argv)


def _validate_cli_paths(args: argparse.Namespace) -> None:
    expected = {
        "protocol": DEFAULT_PROTOCOL,
        "trace": DEFAULT_TRACE,
        "counts": DEFAULT_COUNTS,
        "trace_manifest": DEFAULT_TRACE_MANIFEST,
        "model_input": DEFAULT_MODEL_INPUT,
        "model_manifest": DEFAULT_MODEL_MANIFEST,
        "model_tables": DEFAULT_MODEL_TABLES,
        "selected_data": DEFAULT_SELECTED_DATA,
        "known_kernel_source": DEFAULT_KNOWN_KERNEL_SOURCE,
        "persistence_source": DEFAULT_PERSISTENCE_SOURCE,
        "structured_source": DEFAULT_STRUCTURED_SOURCE,
        "sharp_structured_source": DEFAULT_SHARP_STRUCTURED_SOURCE,
        "sharp_receipt_core": DEFAULT_SHARP_RECEIPT_CORE,
        "receipt_output": DEFAULT_RECEIPT,
        "manifest_output": DEFAULT_RECEIPT_MANIFEST,
        "lean_output": DEFAULT_LEAN,
    }
    for role, expected_path in expected.items():
        _require_exact_path(getattr(args, role), expected_path, role)
    inputs = {
        role: getattr(args, role)
        for role in (
            "protocol", "trace", "counts", "trace_manifest", "model_input",
            "model_manifest", "model_tables", "selected_data", "known_kernel_source",
            "persistence_source", "structured_source",
            "sharp_structured_source", "sharp_receipt_core",
        )
    }
    inputs.update(
        {
            "receipt_generator": ROOT / GENERATOR_PATH,
            "receipt_verifier": ROOT / VERIFIER_PATH,
        }
    )
    outputs = {
        "receipt": args.receipt_output,
        "receipt_manifest": args.manifest_output,
        "lean_data": args.lean_output,
    }
    validate_artifact_paths(inputs, outputs)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        _validate_cli_paths(args)
        if not args.check:
            existing = [
                _display(path)
                for path in (args.receipt_output, args.lean_output, args.manifest_output)
                if path.exists()
            ]
            if existing:
                _fail("single-run receipt generation refuses existing outputs: " + ", ".join(existing))
        receipt_raw, manifest_raw, lean_raw = expected_artifacts(
            protocol_path=args.protocol,
            trace_path=args.trace,
            counts_path=args.counts,
            trace_manifest_path=args.trace_manifest,
            model_input_path=args.model_input,
            model_manifest_path=args.model_manifest,
            model_tables_path=args.model_tables,
            selected_data_path=args.selected_data,
            known_kernel_source_path=args.known_kernel_source,
            persistence_source_path=args.persistence_source,
            structured_source_path=args.structured_source,
            sharp_structured_source_path=args.sharp_structured_source,
            sharp_receipt_core_path=args.sharp_receipt_core,
            receipt_path=args.receipt_output,
            lean_path=args.lean_output,
        )
        if args.check:
            ok = all(
                (
                    _check_exact(args.receipt_output, receipt_raw),
                    _check_exact(args.lean_output, lean_raw),
                    _check_exact(args.manifest_output, manifest_raw),
                )
            )
            if ok:
                print("controlled-queue prospective receipt artifacts are current")
                return 0
            return 1
        write_artifacts_manifest_last(
            args.receipt_output,
            receipt_raw,
            args.lean_output,
            lean_raw,
            args.manifest_output,
            manifest_raw,
        )
        print("generated prospective receipt, Lean data, and manifest")
        return 0
    except (OSError, ProspectiveReceiptError, ValueError) as error:
        print(f"controlled-queue prospective receipt generation failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
