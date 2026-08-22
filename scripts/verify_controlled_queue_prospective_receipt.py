#!/usr/bin/env python3
"""Independently verify the prospective controlled-queue receipt.

The verifier is intentionally self-contained.  It does not import either
prospective generator.  It reconstructs all deterministic potentials before
decoding the trace, recomputes every sufficient statistic and reporting row
with :class:`fractions.Fraction`, renders the expected JSON and Lean bytes, and
then checks the receipt manifest.  No network access is performed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import subprocess
import sys
import unicodedata
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path, PurePosixPath
from typing import Any, NoReturn, Sequence


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


ROOT = Path(__file__).resolve().parents[1]
CONTROLLED_QUEUE = ROOT / "applications" / "controlled_queue"
PROSPECTIVE = CONTROLLED_QUEUE / "prospective"
EVIDENCE = PROSPECTIVE / "evidence"
GENERATED = PROSPECTIVE / "generated"

DEFAULT_PROTOCOL = CONTROLLED_QUEUE / "structured-ope-protocol-v1.json"
DEFAULT_TRACE = GENERATED / "structured-ope-trace-v1.bin"
DEFAULT_COUNTS = GENERATED / "structured-ope-trace-v1-counts.json"
DEFAULT_TRACE_MANIFEST = GENERATED / "structured-ope-trace-v1-manifest.json"
DEFAULT_OSF_REGISTRATION = EVIDENCE / "osf-registration-v1.json"
DEFAULT_OSF_BINDING = EVIDENCE / "code-freeze-binding-v1.json"
DEFAULT_OSF_BINDING_FILE = EVIDENCE / "osf-code-freeze-binding-file-v1.json"
DEFAULT_QUICKNET_CHAIN = EVIDENCE / "quicknet-chain-info-v1.json"
DEFAULT_QUICKNET_ROUND = EVIDENCE / "quicknet-round-v1.json"
DEFAULT_MODEL_INPUT = CONTROLLED_QUEUE / "model-v1.json"
DEFAULT_MODEL_MANIFEST = CONTROLLED_QUEUE / "generated" / "model-v1-manifest.json"
DEFAULT_MODEL_TABLES = CONTROLLED_QUEUE / "generated" / "model-v1-tables.json"
DEFAULT_SELECTED_DATA = ROOT / "FormalSLT" / "Applications" / "ControlledQueueKnownKernelReceiptData.lean"
DEFAULT_KNOWN_KERNEL_SOURCE = ROOT / "FormalSLT" / "Applications" / "ControlledQueueKnownKernelReceipt.lean"
DEFAULT_PERSISTENCE_SOURCE = ROOT / "FormalSLT" / "Applications" / "ControlledQueuePersistenceConfidence.lean"
DEFAULT_STRUCTURED_SOURCE = ROOT / "FormalSLT" / "Applications" / "ControlledQueueStructuredOPE.lean"
DEFAULT_SHARP_STRUCTURED_SOURCE = ROOT / "FormalSLT" / "Applications" / "ControlledQueueSharpStructuredOPE.lean"
DEFAULT_SHARP_RECEIPT_CORE_SOURCE = ROOT / "FormalSLT" / "Applications" / "ControlledQueueSharpStructuredReceiptCore.lean"
DEFAULT_RECEIPT = GENERATED / "structured-ope-receipt-v1.json"
DEFAULT_RECEIPT_MANIFEST = GENERATED / "structured-ope-receipt-v1-manifest.json"
DEFAULT_LEAN = ROOT / "FormalSLT" / "Applications" / "ControlledQueueProspectiveStructuredOPEData.lean"
DEFAULT_GENERATOR = ROOT / "scripts" / "generate_controlled_queue_prospective_receipt.py"
DEFAULT_VERIFIER = Path(__file__).resolve()

TRACE_EVIDENCE_PATHS: dict[str, Path] = {
    "osf_registration_response": DEFAULT_OSF_REGISTRATION,
    "osf_registration_binding": DEFAULT_OSF_BINDING,
    "osf_registration_binding_file": DEFAULT_OSF_BINDING_FILE,
    "quicknet_chain_info": DEFAULT_QUICKNET_CHAIN,
    "quicknet_round": DEFAULT_QUICKNET_ROUND,
}
EXPECTED_SUPPLIED_PATHS: dict[str, Path] = {
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
    "sharp_receipt_core_source": DEFAULT_SHARP_RECEIPT_CORE_SOURCE,
    "receipt": DEFAULT_RECEIPT,
    "receipt_manifest": DEFAULT_RECEIPT_MANIFEST,
    "lean": DEFAULT_LEAN,
}

PROTOCOL_PATH = "applications/controlled_queue/structured-ope-protocol-v1.json"
TRACE_PATH = "applications/controlled_queue/prospective/generated/structured-ope-trace-v1.bin"
COUNTS_PATH = "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-counts.json"
TRACE_MANIFEST_PATH = "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-manifest.json"
MODEL_INPUT_PATH = "applications/controlled_queue/model-v1.json"
MODEL_MANIFEST_PATH = "applications/controlled_queue/generated/model-v1-manifest.json"
MODEL_TABLES_PATH = "applications/controlled_queue/generated/model-v1-tables.json"
SELECTED_DATA_PATH = "FormalSLT/Applications/ControlledQueueKnownKernelReceiptData.lean"
KNOWN_KERNEL_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean"
PERSISTENCE_SOURCE_PATH = "FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean"
STRUCTURED_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueStructuredOPE.lean"
SHARP_STRUCTURED_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueSharpStructuredOPE.lean"
SHARP_RECEIPT_CORE_SOURCE_PATH = "FormalSLT/Applications/ControlledQueueSharpStructuredReceiptCore.lean"
RECEIPT_PATH = "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1.json"
RECEIPT_MANIFEST_PATH = "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1-manifest.json"
LEAN_PATH = "FormalSLT/Applications/ControlledQueueProspectiveStructuredOPEData.lean"
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
VERIFIER_REVISION = "controlled-queue-prospective-receipt-verifier-v1"
ARTIFACT_STATUS = "PROSPECTIVE NUMERICAL RECEIPT - CONDITIONAL PATHWISE CERTIFICATES"

HORIZON = 200_000
STATE_COUNT = 24
ACTION_COUNT = 2
AUGMENTED_COUNT = 48
HYPOTHESIS_COUNT = 12
BEHAVIOR_MASS = Fraction(1, 2)
IMPORTANCE_CAP = Fraction(3, 2)
TRUE_GAMMA = Fraction(149, 200)
CANDIDATE_IDS = ("low", "nominal", "high")
CANDIDATE_GAMMAS = (Fraction(5, 8), Fraction(3, 4), Fraction(7, 8))
CANDIDATE_HITS = (Fraction(41, 64), Fraction(73, 96), Fraction(169, 192))
DEPTHS = (0, 1, 2, 3, 5, 8, 12)
TILTS = (Fraction(1, 16), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2))
PSI_UPPER = {
    Fraction(1, 64): Fraction(1, 8064),
    Fraction(1, 16): Fraction(1, 480),
    Fraction(1, 8): Fraction(1, 112),
    Fraction(1, 4): Fraction(1, 24),
    Fraction(1, 2): Fraction(1, 4),
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
ROUND_RE = re.compile(r"[0-9]+\Z")
RFC3339_UTC_RE = re.compile(
    r"(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(?:\.(\d+))?Z\Z"
)

TRACE_GENERATOR_PATH = "scripts/generate_controlled_queue_prospective_trace.py"
TRACE_VERIFIER_PATH = "scripts/verify_controlled_queue_prospective_trace.py"
TRACE_GENERATOR = ROOT / TRACE_GENERATOR_PATH
TRACE_VERIFIER = ROOT / TRACE_VERIFIER_PATH
CODE_FILES: tuple[tuple[str, str, Path], ...] = (
    ("trace_generator", TRACE_GENERATOR_PATH, TRACE_GENERATOR),
    ("trace_verifier", TRACE_VERIFIER_PATH, TRACE_VERIFIER),
    ("receipt_generator", GENERATOR_PATH, DEFAULT_GENERATOR),
    ("receipt_verifier", VERIFIER_PATH, DEFAULT_VERIFIER),
)
BINDING_SCHEMA = "controlled-queue-prospective-code-freeze-binding-v1"
BINDING_STATUS = "PUBLIC OSF CODE FREEZE BINDING"
TRACE_ARTIFACT_STATUS = "PROSPECTIVE TRACE/PREPROCESSING ONLY - NO ENDPOINT"
TRACE_GENERATOR_REVISION = "controlled-queue-prospective-trace-generator-v1"
CHAIN_HASH = "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971"
GROUP_HASH = "f477d5c89f21a17c863a7f937c6a6d15859414d2be09cd448d4279af331c5d3e"
PUBLIC_KEY = (
    "83cf0f2896adee7eb8b5f01fcad3912212c437e0073e911fb90022d3e760183c"
    "8c4b450b6a0a6c3ac6a5776a2d1064510d1fec758c921cc22b0e17e63aaf4bcb"
    "5ed66304de9cf809bd274ca73bab4af5a6e9c76a4bc09e76eae8991ef5ece45a"
)
SCHEME_ID = "bls-unchained-g1-rfc9380"
BEACON_ID = "quicknet"
GENESIS_SECONDS = 1_692_803_367
PERIOD_SECONDS = 3
REGISTRATION_DELAY_SECONDS = 3_600
PY_ECC_VERSION = "8.0.0"
BLS_IMPLEMENTATION = "py_ecc_low_level_rfc9380"
BLS_DST = "BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_"
PRNG_VERSION = "sha256-counter-stream-v1"
SAMPLING_VERSION = "exact-categorical-u64-rejection-v1"
BINARY_VERSION = "controlled-queue-prospective-trace-binary-v1"

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
    "not a confidence certificate for the fixed-range PLANNED_NOT_CHECKED row",
    "not stationary target-policy certification for the two causal Beta predictors",
    "not a family-membership test or a result outside the frozen refresh family",
]
TRACE_NONCLAIMS = [
    "not a numerical endpoint or confidence certificate",
    "not proof that the named path belongs to a theorem-produced good event",
    "not Lean verification of the beacon signature or raw trace bytes",
]


class VerificationError(ValueError):
    """Raised when a prospective receipt or one of its bindings is invalid."""


def _fail(message: str) -> NoReturn:
    raise VerificationError(message)


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


def parse_json(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"invalid UTF-8 JSON in {where}: {error}") from error


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def parse_canonical_object(raw: bytes, where: str) -> dict[str, Any]:
    value = _object(parse_json(raw, where), where)
    _exact(raw, canonical_json(value), f"canonical {where} bytes")
    return value


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rational_text(value: Fraction | int) -> str:
    exact = value if isinstance(value, Fraction) else Fraction(value)
    if exact.denominator == 1:
        return str(exact.numerator)
    return f"{exact.numerator}/{exact.denominator}"


def decimal_text(value: Fraction | int) -> str:
    exact = value if isinstance(value, Fraction) else Fraction(value)
    scale = 10**15
    quotient, remainder = divmod(abs(exact.numerator) * scale, exact.denominator)
    doubled_remainder = 2 * remainder
    if doubled_remainder > exact.denominator or (
        doubled_remainder == exact.denominator and quotient % 2 == 1
    ):
        quotient += 1
    whole, fractional = divmod(quotient, scale)
    sign = "-" if exact.numerator < 0 and quotient != 0 else ""
    return f"{sign}{whole}.{fractional:015d}"


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
        exact = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError(f"invalid rational at {where}: {text!r}") from error
    _exact(text, rational_text(exact), f"canonical {where}")
    return exact


def _number(value: Any, where: str) -> Fraction:
    row = _object(value, where)
    _keys(row, {"rational", "decimal"}, where)
    exact = _fraction(row["rational"], f"{where}.rational")
    _exact(row["decimal"], decimal_text(exact), f"{where}.decimal")
    return exact


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
        raise VerificationError(f"cannot read {where} at {path}: {error}") from error


def _display(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def _file_row(role: str, path: Path, raw: bytes) -> dict[str, Any]:
    return {"bytes": len(raw), "path": _display(path), "role": role, "sha256": sha256(raw)}


def _number_grid(value: Any) -> Any:
    if isinstance(value, Fraction):
        return number(value)
    if isinstance(value, list):
        return [_number_grid(item) for item in value]
    if isinstance(value, tuple):
        return [_number_grid(item) for item in value]
    if isinstance(value, dict):
        return {key: _number_grid(item) for key, item in value.items()}
    return value


def validate_protocol(raw: bytes) -> dict[str, Any]:
    _exact(sha256(raw), PROTOCOL_SHA256, "frozen protocol SHA-256")
    protocol = parse_canonical_object(raw, "protocol")
    _exact(protocol.get("schema_version"), PROTOCOL_SCHEMA, "protocol schema")
    _exact(protocol.get("protocol_version"), PROTOCOL_VERSION, "protocol version")
    _exact(protocol.get("artifact_status"), "PROSPECTIVE PROTOCOL ONLY - NO TRACE OR RESULT", "protocol artifact status")
    generation = _object(protocol.get("data_generation"), "protocol.data_generation")
    _exact(generation.get("horizon"), HORIZON, "protocol horizon")
    _exact(_fraction(generation.get("true_gamma"), "protocol true gamma"), TRUE_GAMMA, "protocol true gamma")
    _exact(protocol["reporting_contract"]["row_order"], list(ROW_ORDER), "protocol row order")
    _exact(set(protocol["reporting_contract"]["required_fields_per_row"]), ROW_FIELDS, "protocol row fields")
    arithmetic = _object(protocol.get("receipt_arithmetic_contract"), "protocol.receipt_arithmetic_contract")
    _exact(
        arithmetic.get("hybrid_bessel_upper"),
        "always 1/2 + (3/2)*Q where Q = sum_sq - sum^2/n; never evaluate or data-select the harmonic branch",
        "protocol affine Bessel branch",
    )
    _exact(
        arithmetic.get("decimal_display"),
        {"digits_after_decimal": 15, "rounding": "ROUND_HALF_EVEN", "source": "authoritative exact reduced rational only"},
        "protocol decimal display",
    )
    psi = arithmetic.get("psi_upper_by_tilt")
    _exact(
        psi,
        {"1/2": "1/4", "1/4": "1/24", "1/8": "1/112", "1/16": "1/480", "1/64": "1/8064"},
        "protocol psi table",
    )
    primary = _object(protocol.get("primary_endpoint"), "protocol.primary_endpoint")
    _exact(_fraction(primary.get("potential_span"), "primary span"), PRIMARY_B, "primary span")
    _exact(_fraction(primary.get("candidate_drift_oscillation"), "primary drift"), PRIMARY_DRIFT, "primary drift")
    _exact(
        _fraction(primary.get("refresh_drift_sensitivity_oscillation"), "primary sensitivity"),
        PRIMARY_SENSITIVITY,
        "primary sensitivity",
    )
    fixed = next(row for row in protocol["matched_baselines"] if row["baseline_id"] == "selected_h12_nonvariance_fixed_range")
    _exact(fixed.get("checked_status_until_theorem_exists"), "PLANNED_NOT_CHECKED", "fixed-range checked status")
    _exact(fixed.get("confidence_claim_until_theorem_exists"), "NOT_A_CONFIDENCE_CERTIFICATE", "fixed-range confidence status")
    return protocol


def decode_trace(raw: bytes, *, expected_horizon: int = HORIZON) -> tuple[list[int], list[int]]:
    if len(raw) < BINARY_HEADER.size:
        _fail("prospective trace is shorter than its binary header")
    magic, horizon, state_count, action_count = BINARY_HEADER.unpack(raw[: BINARY_HEADER.size])
    _exact(magic, BINARY_MAGIC, "trace magic")
    _exact(horizon, expected_horizon, "trace horizon")
    _exact(state_count, expected_horizon + 1, "trace state count")
    _exact(action_count, expected_horizon + 1, "trace action count")
    expected_bytes = BINARY_HEADER.size + state_count + action_count
    _exact(len(raw), expected_bytes, "trace byte length")
    if expected_horizon == HORIZON:
        _exact(len(raw), BINARY_BYTES, "frozen trace byte length")
    states = list(raw[BINARY_HEADER.size : BINARY_HEADER.size + state_count])
    actions = list(raw[BINARY_HEADER.size + state_count :])
    if any(state >= STATE_COUNT for state in states):
        _fail("trace contains an out-of-range physical state")
    if any(action >= ACTION_COUNT for action in actions):
        _fail("trace contains an out-of-range action")
    _exact(states[0], 0, "trace initial state")
    _exact(actions[0], 0, "trace dummy initial action")
    return states, actions


def queue_step(state: int, action: int) -> int:
    if not 0 <= state < STATE_COUNT or not 0 <= action < ACTION_COUNT:
        raise ValueError("invalid physical state/action")
    queue, regime = divmod(state, 3)
    service = (1, 2)[action]
    arrival = (0, 1, 2)[regime]
    next_queue = min(7, max(0, queue - service) + arrival)
    return 3 * next_queue + (regime + 1) % 3


def physical_counts(states: Sequence[int], actions: Sequence[int]) -> dict[str, Any]:
    if len(states) != len(actions) or len(states) < 2:
        _fail("trace arrays must have equal positive transition length")
    edges = [[[0] * STATE_COUNT for _ in range(ACTION_COUNT)] for _ in range(STATE_COUNT)]
    state_action = [[0] * ACTION_COUNT for _ in range(STATE_COUNT)]
    source_visits = [0] * STATE_COUNT
    destination_counts = [0] * STATE_COUNT
    action_counts = [0] * ACTION_COUNT
    hits = 0
    for k in range(len(states) - 1):
        source = states[k]
        action = actions[k + 1]
        destination = states[k + 1]
        edges[source][action][destination] += 1
        state_action[source][action] += 1
        source_visits[source] += 1
        destination_counts[destination] += 1
        action_counts[action] += 1
        hits += int(destination == queue_step(source, action))
    n = len(states) - 1
    return {
        "edge_counts": edges,
        "state_action_counts": state_action,
        "source_state_visits": source_visits,
        "destination_state_counts": destination_counts,
        "transition_action_counts": action_counts,
        "persistence_hit_count": hits,
        "persistence_miss_count": n - hits,
    }


def augmented_counts(states: Sequence[int], actions: Sequence[int]) -> tuple[list[list[int]], list[int]]:
    edges = [[0] * AUGMENTED_COUNT for _ in range(AUGMENTED_COUNT)]
    visits = [0] * AUGMENTED_COUNT
    for k in range(len(states) - 1):
        source = 2 * states[k] + actions[k]
        destination = 2 * states[k + 1] + actions[k + 1]
        edges[source][destination] += 1
        visits[source] += 1
    return edges, visits


def _indexed_rows(value: Any, count: int, where: str) -> list[dict[str, Any]]:
    rows = [_object(row, f"{where}[{index}]") for index, row in enumerate(_array(value, where))]
    _exact(len(rows), count, f"{where} length")
    return rows


def _fraction_row(value: Any, count: int, where: str) -> list[Fraction]:
    row = _array(value, where)
    _exact(len(row), count, f"{where} length")
    return [_fraction(entry, f"{where}[{index}]") for index, entry in enumerate(row)]


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
    for key, expected in (
        ("physical_state_count", STATE_COUNT),
        ("action_count", ACTION_COUNT),
        ("augmented_behavior_state_count", AUGMENTED_COUNT),
        ("candidate_count", 3),
        ("target_policy_count", 4),
        ("fixed_predictor_count", 3),
    ):
        _exact(dimensions.get(key), expected, f"model dimensions.{key}")

    policy_ids = ("behavior_uniform", "conservative", "queue_threshold", "regime_aware", "aggressive")
    items = [_object(item, "model policy") for item in _array(value.get("policies"), "model policies")]
    _exact([item.get("id") for item in items], list(policy_ids), "model policy order")
    policies: list[list[list[Fraction]]] = []
    for policy_id, item in zip(policy_ids, items, strict=True):
        parsed: list[list[Fraction]] = []
        for state, row in enumerate(_indexed_rows(item.get("rows"), STATE_COUNT, f"policy {policy_id}.rows")):
            _exact(row.get("state"), state, f"policy {policy_id} state")
            probabilities = _fraction_row(row.get("probabilities"), ACTION_COUNT, f"policy {policy_id} row {state}")
            _exact(sum(probabilities), Fraction(1), f"policy {policy_id} row mass")
            parsed.append(probabilities)
        policies.append(parsed)
    if any(mass != BEHAVIOR_MASS for row in policies[0] for mass in row):
        _fail("behavior policy is not exactly uniform")

    candidates: list[list[list[list[Fraction]]]] = []
    candidate_items = [_object(item, "candidate kernel") for item in _array(value.get("candidate_kernels"), "candidate kernels")]
    _exact([item.get("id") for item in candidate_items], list(CANDIDATE_IDS), "candidate order")
    for candidate_index, (item, gamma) in enumerate(zip(candidate_items, CANDIDATE_GAMMAS, strict=True)):
        _exact(_fraction(item.get("gamma"), f"candidate {candidate_index} gamma"), gamma, f"candidate {candidate_index} gamma")
        kernel = [[[] for _ in range(ACTION_COUNT)] for _ in range(STATE_COUNT)]
        for row_index, row in enumerate(_indexed_rows(item.get("rows"), STATE_COUNT * ACTION_COUNT, f"candidate {candidate_index}.rows")):
            state, action = divmod(row_index, ACTION_COUNT)
            _exact(row.get("state"), state, f"candidate {candidate_index} state")
            _exact(row.get("action"), ("eco", "boost")[action], f"candidate {candidate_index} action")
            probabilities = _fraction_row(row.get("probabilities"), STATE_COUNT, f"candidate {candidate_index} row {row_index}")
            _exact(sum(probabilities), Fraction(1), f"candidate {candidate_index} row mass")
            kernel[state][action] = probabilities
        _exact(kernel, refresh_kernel(gamma), f"candidate {candidate_index} refresh kernel")
        candidates.append(kernel)

    predictor_ids = ("global_climatology", "queue_action_threshold", "nominal_model_overload")
    loss_items = [_object(item, "fixed Brier loss") for item in _array(value.get("fixed_brier_loss"), "fixed Brier losses")]
    _exact([item.get("id") for item in loss_items], list(predictor_ids), "fixed predictor order")
    losses: list[list[list[list[Fraction]]]] = []
    for predictor_index, item in enumerate(loss_items):
        table = [[[] for _ in range(ACTION_COUNT)] for _ in range(STATE_COUNT)]
        for row_index, row in enumerate(_indexed_rows(item.get("rows"), STATE_COUNT * ACTION_COUNT, f"loss {predictor_index}.rows")):
            state, action = divmod(row_index, ACTION_COUNT)
            _exact(row.get("state"), state, f"loss {predictor_index} state")
            _exact(row.get("action"), ("eco", "boost")[action], f"loss {predictor_index} action")
            entries = _fraction_row(row.get("losses"), STATE_COUNT, f"loss {predictor_index} row {row_index}")
            if any(entry < 0 or entry > 1 for entry in entries):
                _fail("Brier loss escaped [0,1]")
            table[state][action] = entries
        losses.append(table)

    for row_index, row in enumerate(_indexed_rows(value.get("queue_step"), STATE_COUNT * ACTION_COUNT, "queue_step")):
        state, action = divmod(row_index, ACTION_COUNT)
        _exact(row.get("state"), state, "queue_step state")
        _exact(row.get("action"), ("eco", "boost")[action], "queue_step action")
        _exact(row.get("next_state"), queue_step(state, action), "queue_step next_state")
    return {
        "behavior_policy": policies[0],
        "target_policies": policies[1:],
        "candidate_kernels": candidates,
        "losses": losses,
        "predictor_ids": predictor_ids,
    }


def _mat_vec(matrix: Sequence[Sequence[Fraction]], vector: Sequence[Fraction]) -> list[Fraction]:
    return [
        sum((coefficient * value for coefficient, value in zip(row, vector, strict=True)), Fraction(0))
        for row in matrix
    ]


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
                * sum((environment[state][action][destination] * loss[state][action][destination] for destination in range(STATE_COUNT)), Fraction(0))
                for action in range(ACTION_COUNT)
            ),
            Fraction(0),
        )
        for state in range(STATE_COUNT)
    ]
    reference_mean = sum(row_risk, Fraction(0)) / STATE_COUNT
    iterate = [entry - reference_mean for entry in row_risk]
    potential = [Fraction(0)] * STATE_COUNT
    for _ in range(depth):
        potential = [left + right for left, right in zip(potential, iterate, strict=True)]
        iterate = _mat_vec(kernel, iterate)
    anchor = potential[0]
    potential = [entry - anchor for entry in potential]
    span = max(potential) - min(potential)
    next_potential = _mat_vec(kernel, potential)
    drift = [row_risk[state] + next_potential[state] - potential[state] for state in range(STATE_COUNT)]
    return {
        "depth": depth,
        "potential": potential,
        "actual_span": span,
        "row_risk": row_risk,
        "uniform_reference_mean": reference_mean,
        "drift": drift,
        "drift_oscillation": max(drift) - min(drift),
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
    """Compute all candidate and oracle potentials before any trace decoding."""

    candidate_tables: list[list[list[dict[str, Any]]]] = []
    for candidate_index, environment in enumerate(model["candidate_kernels"]):
        depth_tables: list[list[dict[str, Any]]] = []
        for depth in DEPTHS:
            hypothesis_tables: list[dict[str, Any]] = []
            for posterior_index in range(HYPOTHESIS_COUNT):
                policy_index, predictor_index = divmod(posterior_index, 3)
                table = compute_potential(
                    environment,
                    model["target_policies"][policy_index],
                    model["losses"][predictor_index],
                    depth,
                )
                table.update(
                    candidate_index=candidate_index,
                    policy_index=policy_index,
                    predictor_index=predictor_index,
                    hypothesis_index=posterior_index,
                    closed_span_bound=closed_span_bound(CANDIDATE_GAMMAS[candidate_index], depth),
                )
                hypothesis_tables.append(table)
            depth_tables.append(hypothesis_tables)
        candidate_tables.append(depth_tables)
    selected = candidate_tables[1][DEPTHS.index(12)][5]
    _exact(selected["actual_span"], PRIMARY_B, "selected actual potential span")
    _exact(selected["drift_oscillation"], PRIMARY_DRIFT, "selected exact candidate-drift oscillation")
    sensitivity = refresh_sensitivity_table(
        model["target_policies"][1], model["losses"][2], selected["potential"]
    )
    sensitivity_oscillation = max(sensitivity) - min(sensitivity)
    _exact(sensitivity_oscillation, PRIMARY_SENSITIVITY, "selected exact refresh-sensitivity oscillation")
    selected["refresh_sensitivity"] = sensitivity
    selected["refresh_sensitivity_oscillation"] = sensitivity_oscillation
    oracle = compute_potential(
        refresh_kernel(TRUE_GAMMA),
        model["target_policies"][1],
        model["losses"][2],
        12,
    )
    return {"candidate_tables": candidate_tables, "selected": selected, "oracle": oracle}


def deterministic_then_decode(
    model: dict[str, Any],
    trace_raw: bytes,
    *,
    deterministic_builder: Any = compute_deterministic_tables,
    decoder: Any = decode_trace,
) -> tuple[dict[str, Any], list[int], list[int]]:
    """Make the oracle-before-trace chronology explicit and directly testable."""

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
    scale = IMPORTANCE_CAP * (1 + 2 * span_bound)
    total = Fraction(0)
    total_sq = Fraction(0)
    row_sums = [[Fraction(0)] * ACTION_COUNT for _ in range(STATE_COUNT)]
    row_sum_squares = [[Fraction(0)] * ACTION_COUNT for _ in range(STATE_COUNT)]
    n = 0
    for state in range(STATE_COUNT):
        for action in range(ACTION_COUNT):
            ratio = policy[state][action] / BEHAVIOR_MASS
            for destination in range(STATE_COUNT):
                score = ratio * (loss[state][action][destination] + potential[destination] - potential[state] + span_bound) / scale
                if score < 0 or score > 1:
                    _fail("normalized score escaped [0,1]")
                count = histogram[state][action][destination]
                n += count
                total += count * score
                total_sq += count * score * score
                row_sums[state][action] += count * score
                row_sum_squares[state][action] += count * score * score
    if n <= 0:
        _fail("score histogram is empty")
    q = total_sq - total * total / n
    if q < 0:
        _fail("Bessel statistic is negative")
    return {
        "count": Fraction(n),
        "sum": total,
        "sum_squares": total_sq,
        "row_sums": row_sums,
        "row_sum_squares": row_sum_squares,
        "bessel_q": q,
        "hybrid_affine_upper": Fraction(1, 2) + Fraction(3, 2) * q,
        "scale": scale,
        "span_bound": span_bound,
        "empirical_corrected_score": scale * total / n - span_bound,
    }


def empirical_bernstein_correction(summary: dict[str, Any], *, log_upper: int, tilt: Fraction) -> Fraction:
    return summary["scale"] * (log_upper + PSI_UPPER[tilt] * summary["hybrid_affine_upper"]) / (summary["count"] * tilt)


def indicator_summary(successes: int, n: int) -> dict[str, Fraction]:
    if isinstance(successes, bool) or isinstance(n, bool) or n <= 0 or not 0 <= successes <= n:
        raise ValueError("indicator count must be in [0,n]")
    count = Fraction(successes)
    q = count - count * count / n
    return {
        "sum": count,
        "sum_squares": count,
        "bessel_q": q,
        "hybrid_affine_upper": Fraction(1, 2) + Fraction(3, 2) * q,
    }


def persistence_radius(hits: int, n: int, *, tilt: Fraction, log_upper: int) -> dict[str, Fraction]:
    direct = indicator_summary(hits, n)
    complement = indicator_summary(n - hits, n)
    direct_boundary = (log_upper + PSI_UPPER[tilt] * direct["hybrid_affine_upper"]) / (n * tilt)
    complement_boundary = (log_upper + PSI_UPPER[tilt] * complement["hybrid_affine_upper"]) / (n * tilt)
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


def structured_eta(candidate_hit: Fraction, hits: int, n: int, *, tilt: Fraction, log_upper: int) -> dict[str, Fraction]:
    confidence = persistence_radius(hits, n, tilt=tilt, log_upper=log_upper)
    discrepancy = abs(candidate_hit - Fraction(hits, n))
    return {**confidence, "candidate_discrepancy": discrepancy, "eta": discrepancy + confidence["radius"]}


def fixed_range_eta(candidate_hit: Fraction, hits: int, n: int) -> dict[str, Fraction]:
    tilt = Fraction(1, 64)
    radius = tilt / (8 * (1 - tilt / 3)) + Fraction(7, n * tilt)
    discrepancy = abs(candidate_hit - Fraction(hits, n))
    return {"candidate_discrepancy": discrepancy, "fixed_range_radius": radius, "eta": discrepancy + radius}


def fixed_range_risk_correction(scale: Fraction, n: int) -> Fraction:
    tilt = Fraction(1, 16)
    return scale * (tilt / (8 * (1 - tilt / 3)) + Fraction(9, n * tilt))


def augmented_candidate_kernel(environment: Sequence[Sequence[Sequence[Fraction]]]) -> list[list[Fraction]]:
    rows: list[list[Fraction]] = []
    for source in range(AUGMENTED_COUNT):
        state = source // ACTION_COUNT
        row = [Fraction(0)] * AUGMENTED_COUNT
        for next_action in range(ACTION_COUNT):
            for destination in range(STATE_COUNT):
                row[ACTION_COUNT * destination + next_action] = BEHAVIOR_MASS * environment[state][next_action][destination]
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
    rows: list[dict[str, Any]] = []
    eta = Fraction(0)
    all_visited = True
    coordinates = 0
    orientations = 0
    tilt = Fraction(1, 64)
    for source in range(AUGMENTED_COUNT):
        observed_row = list(edges[source])
        if len(observed_row) != AUGMENTED_COUNT:
            _fail("augmented histogram row length mismatch")
        visit = visits[source]
        _exact(sum(observed_row), visit, f"augmented row {source} visit identity")
        if visit == 0:
            all_visited = False
            rows.append(
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
            coordinates += AUGMENTED_COUNT
            orientations += 2 * AUGMENTED_COUNT
            continue
        empirical_tv = Fraction(1, 2) * sum(
            (abs(candidate[source][destination] - Fraction(observed_row[destination], visit)) for destination in range(AUGMENTED_COUNT)),
            Fraction(0),
        )
        radii: list[Fraction] = []
        for observed in observed_row:
            direct = indicator_summary(observed, n)
            complement = indicator_summary(n - observed, n)
            direct_boundary = (18 + PSI_UPPER[tilt] * direct["hybrid_affine_upper"]) / (n * tilt)
            complement_boundary = (18 + PSI_UPPER[tilt] * complement["hybrid_affine_upper"]) / (n * tilt)
            radii.append(Fraction(n, visit) * max(direct_boundary, complement_boundary))
            coordinates += 1
            orientations += 2
        radius_half = Fraction(1, 2) * sum(radii, Fraction(0))
        row_eta = empirical_tv + radius_half
        eta = max(eta, row_eta)
        rows.append(
            {
                "source": source,
                "visits": visit,
                "premise_visited": True,
                "empirical_row_tv": empirical_tv,
                "coordinate_radius_sum_half": radius_half,
                "row_eta": row_eta,
                "coordinate_radii": radii,
            }
        )
    _exact(coordinates, 2304, "unstructured coordinate count")
    _exact(orientations, 4608, "unstructured oriented-coordinate count")
    return {
        "all_augmented_source_rows_visited": all_visited,
        "coordinate_count": coordinates,
        "oriented_coordinate_count": orientations,
        "source_rows": rows,
        "eta_augmented": eta,
    }


def balanced_fraction_sum(terms: Sequence[Fraction]) -> Fraction:
    """Sum exact fractions without a horizon-long left-associated denominator."""
    level = list(terms)
    if not level:
        return Fraction(0)
    while len(level) > 1:
        next_level = [
            level[index] + level[index + 1]
            for index in range(0, len(level) - 1, 2)
        ]
        if len(level) % 2:
            next_level.append(level[-1])
        level = next_level
    return level[0]


def causal_beta_summaries(states: Sequence[int], actions: Sequence[int]) -> dict[str, Any]:
    if len(states) != len(actions) or len(states) < 2:
        _fail("causal predictor path dimensions mismatch")
    n = len(states) - 1
    global_alpha = 1
    global_beta = 1
    cells = [[[1, 1] for _ in range(ACTION_COUNT)] for _ in range(3)]
    global_loss_terms: list[Fraction] = []
    band_loss_terms: list[Fraction] = []
    for k in range(n):
        state = states[k]
        action = actions[k + 1]
        destination = states[k + 1]
        outcome = int(destination // 3 >= 6)
        probability = Fraction(global_alpha, global_alpha + global_beta)
        global_loss_terms.append((probability - outcome) ** 2)
        queue = state // 3
        band = 0 if queue <= 3 else (1 if queue <= 5 else 2)
        alpha, beta = cells[band][action]
        probability = Fraction(alpha, alpha + beta)
        band_loss_terms.append((probability - outcome) ** 2)
        global_alpha += outcome
        global_beta += 1 - outcome
        cells[band][action][0] += outcome
        cells[band][action][1] += 1 - outcome
    global_loss = balanced_fraction_sum(global_loss_terms)
    band_loss = balanced_fraction_sum(band_loss_terms)
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
                "final_cells_alpha_beta": cells,
            },
        ],
        "confidence_status": "DESCRIPTIVE_DYNAMIC_ENCOUNTERED_RISK_ONLY",
    }


def build_score_catalog(histogram: Sequence[Sequence[Sequence[int]]], model: dict[str, Any], deterministic: dict[str, Any]) -> list[dict[str, Any]]:
    catalog: list[dict[str, Any]] = []
    for candidate_index in range(3):
        for depth_index, depth in enumerate(DEPTHS):
            for posterior_index in range(HYPOTHESIS_COUNT):
                policy_index, predictor_index = divmod(posterior_index, 3)
                table = deterministic["candidate_tables"][candidate_index][depth_index][posterior_index]
                summary = normalized_score_summary(
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
    _exact(len(catalog), 252, "adaptive score catalog length")
    return catalog


def select_adaptive_endpoint(score_catalog: Sequence[dict[str, Any]], hits: int, n: int) -> dict[str, Any]:
    """Select the frozen minimum; the true gamma is deliberately not an input."""

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
    best: dict[str, Any] | None = None
    best_key: tuple[Fraction, int, int, int, int, int] | None = None
    for candidate_index in range(3):
        for depth_index, depth in enumerate(DEPTHS):
            for risk_tilt_index, risk_tilt in enumerate(TILTS):
                for persistence_tilt_index in range(len(TILTS)):
                    eta = persistence[(candidate_index, persistence_tilt_index)]["eta"]
                    for posterior_index in range(HYPOTHESIS_COUNT):
                        summary = by_key[(candidate_index, depth_index, posterior_index)]["summary"]
                        risk = empirical_bernstein_correction(summary, log_upper=16, tilt=risk_tilt)
                        residual = CANDIDATE_GAMMAS[candidate_index] ** depth + 2 * (1 + summary["span_bound"]) * eta
                        total = summary["empirical_corrected_score"] + risk + residual
                        indices = (candidate_index, depth_index, risk_tilt_index, persistence_tilt_index, posterior_index)
                        row = {"indices": list(indices), "total_certified_rhs": total}
                        candidates.append(row)
                        key = (total, *indices)
                        if best_key is None or key < best_key:
                            best_key = key
                            best = {
                                **row,
                                "empirical_corrected_score": summary["empirical_corrected_score"],
                                "risk_statistical_correction": risk,
                                "persistence_eta": eta,
                                "candidate_or_truncation_residual": residual,
                                "score_summary": summary,
                            }
    _exact(len(candidates), 4032, "adaptive selector catalog length")
    if best is None:
        raise AssertionError("nonempty adaptive catalog has no minimum")
    return {"selected": best, "catalog_minimum_certificate": candidates, "persistence_summaries": persistence}


def _git(*arguments: str) -> bytes:
    try:
        completed = subprocess.run(
            ["git", "-C", str(ROOT), *arguments],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin", "GIT_TERMINAL_PROMPT": "0"},
        )
    except OSError as error:
        raise VerificationError(f"cannot execute Git object check: {error}") from error
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        _fail(f"Git object check failed for {arguments!r}: {detail}")
    return completed.stdout


def _verify_git_tree(commit: str, tree: str, where: str) -> None:
    _exact(_git("cat-file", "-t", commit).strip(), b"commit", f"{where} object type")
    actual = _git("rev-parse", "--verify", f"{commit}^{{tree}}").decode("ascii").strip()
    _exact(actual, tree, f"{where} tree")


def _verify_git_file(commit: str, path: str, raw: bytes, where: str) -> None:
    committed = _git("show", f"{commit}:{path}")
    _exact(committed, raw, f"{where} current versus committed bytes")


def _verify_git_ancestor(ancestor: str, descendant: str) -> None:
    _git("merge-base", "--is-ancestor", ancestor, descendant)


def _hex_bytes(value: Any, byte_length: int, where: str) -> bytes:
    text = _string(value, where)
    if len(text) != 2 * byte_length or re.fullmatch(r"[0-9a-f]+", text) is None:
        _fail(f"{where} must encode exactly {byte_length} bytes in lowercase hex")
    return bytes.fromhex(text)


def _registration_second(value: Any) -> tuple[str, int]:
    text = _string(value, "OSF date_registered")
    match = RFC3339_UTC_RE.fullmatch(text)
    if match is None:
        _fail("OSF date_registered must be canonical RFC3339 UTC")
    year, month, day, hour, minute, second = (int(part) for part in match.groups()[:6])
    fractional = match.group(7)
    try:
        base = int(datetime(year, month, day, hour, minute, second, tzinfo=timezone.utc).timestamp())
    except ValueError as error:
        raise VerificationError(f"invalid OSF date_registered: {text}") from error
    ceiling = base + int(fractional is not None and int(fractional) != 0)
    return text, ceiling


def _formula_round(registration_second: int) -> tuple[int, int]:
    target = registration_second + REGISTRATION_DELAY_SECONDS
    delta = target - GENESIS_SECONDS
    if delta < 0:
        _fail("OSF registration precedes the frozen quicknet genesis window")
    round_number = 1 + (delta + PERIOD_SECONDS - 1) // PERIOD_SECONDS
    round_time = GENESIS_SECONDS + (round_number - 1) * PERIOD_SECONDS
    if round_time < target or round_time - PERIOD_SECONDS >= target:
        _fail("formula-selected quicknet round is not the first eligible round")
    return round_number, round_time


def _resolve_manifest_path(text: Any, where: str) -> Path:
    value = _string(text, where)
    if unicodedata.normalize("NFC", value) != value:
        _fail(f"{where} must be NFC-normalized")
    pure = PurePosixPath(value)
    if (
        not value
        or "\\" in value
        or value.startswith("//")
        or value.endswith("/")
        or pure.as_posix() != value
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        _fail(f"{where} is not a canonical POSIX path")
    return Path(value) if pure.is_absolute() else ROOT / value


def _read_manifest_row(row: Any, where: str) -> tuple[str, Path, bytes, dict[str, Any]]:
    value = _object(row, where)
    _keys(value, {"bytes", "path", "role", "sha256"}, where)
    role = _string(value["role"], f"{where}.role")
    path = _resolve_manifest_path(value["path"], f"{where}.path")
    raw = _read(path, f"{where} file")
    _exact(_integer(value["bytes"], f"{where}.bytes", minimum=0), len(raw), f"{where}.bytes")
    _exact(_digest(value["sha256"], f"{where}.sha256"), sha256(raw), f"{where}.sha256")
    return role, path, raw, value


def _verify_osf_registration(value: dict[str, Any]) -> tuple[str, str, int]:
    data = _object(value.get("data"), "OSF response.data")
    registration_id = _string(data.get("id"), "OSF registration id")
    if re.fullmatch(r"[a-z0-9]{5}", registration_id) is None:
        _fail("OSF registration id must contain five lowercase letters or digits")
    _exact(data.get("type"), "registrations", "OSF response type")
    attributes = _object(data.get("attributes"), "OSF response.attributes")
    _exact(_boolean(attributes.get("public"), "OSF public flag"), True, "OSF public flag")
    _exact(_boolean(attributes.get("registration"), "OSF registration flag"), True, "OSF registration flag")
    _exact(_boolean(attributes.get("withdrawn"), "OSF withdrawn flag"), False, "OSF withdrawn flag")
    date_registered, second = _registration_second(attributes.get("date_registered"))
    return registration_id, date_registered, second


def _verify_osf_binding_file(value: dict[str, Any], registration_id: str, binding_raw: bytes) -> None:
    data = _object(value.get("data"), "OSF binding-file response.data")
    if not _string(data.get("id"), "OSF binding-file id"):
        _fail("OSF binding-file id must be nonempty")
    _exact(data.get("type"), "files", "OSF binding-file response type")
    attributes = _object(data.get("attributes"), "OSF binding-file attributes")
    _exact(attributes.get("name"), "code-freeze-binding-v1.json", "OSF binding filename")
    _exact(attributes.get("kind"), "file", "OSF binding-file kind")
    _exact(_integer(attributes.get("current_version"), "OSF binding-file version", minimum=1), 1, "OSF binding-file version")
    materialized = _string(attributes.get("materialized_path"), "OSF binding materialized path")
    pure = PurePosixPath(materialized)
    if (
        not materialized.startswith("/")
        or materialized.startswith("//")
        or materialized.endswith("/")
        or pure.as_posix() != materialized
        or any(part in {"", ".", ".."} for part in pure.parts[1:])
        or unicodedata.normalize("NFC", materialized) != materialized
    ):
        _fail("OSF binding materialized path is not canonical absolute POSIX")
    _exact(pure.name, "code-freeze-binding-v1.json", "OSF binding materialized filename")
    _exact(_integer(attributes.get("size"), "OSF binding size", minimum=1), len(binding_raw), "OSF binding size")
    hashes = _object(_object(attributes.get("extra"), "OSF binding extra").get("hashes"), "OSF binding hashes")
    _exact(_digest(hashes.get("sha256"), "OSF binding SHA-256"), sha256(binding_raw), "OSF binding SHA-256")
    relationships = _object(data.get("relationships"), "OSF binding relationships")
    target = _object(relationships.get("target"), "OSF binding target")
    _exact(_object(target.get("data"), "OSF binding target data"), {"id": registration_id, "type": "registrations"}, "OSF binding target data")
    href = _string(_object(_object(target.get("links"), "OSF target links").get("related"), "OSF related link").get("href"), "OSF related href")
    _exact(href, f"https://api.osf.io/v2/registrations/{registration_id}/", "OSF binding target URL")
    if "node" in relationships:
        node = _object(_object(relationships["node"], "OSF binding node").get("data"), "OSF binding node data")
        _exact(node.get("id"), registration_id, "OSF binding node id")


def _validate_code_freeze_binding(
    binding: dict[str, Any], protocol_raw: bytes
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    _keys(binding, {"artifact_status", "schema_version", "protocol", "code_freeze", "code_files"}, "code-freeze binding")
    _exact(binding["artifact_status"], BINDING_STATUS, "binding status")
    _exact(binding["schema_version"], BINDING_SCHEMA, "binding schema")
    protocol = _object(binding["protocol"], "binding protocol")
    _keys(protocol, {"path", "bytes", "sha256", "commit", "tree"}, "binding protocol")
    _exact(protocol["path"], PROTOCOL_PATH, "binding protocol path")
    _exact(protocol["bytes"], len(protocol_raw), "binding protocol bytes")
    _exact(protocol["sha256"], PROTOCOL_SHA256, "binding protocol hash")
    _exact(_oid(protocol["commit"], "binding protocol commit"), PROTOCOL_COMMIT, "binding protocol commit")
    _exact(_oid(protocol["tree"], "binding protocol tree"), PROTOCOL_TREE, "binding protocol tree")
    _verify_git_tree(PROTOCOL_COMMIT, PROTOCOL_TREE, "protocol")
    _verify_git_file(PROTOCOL_COMMIT, PROTOCOL_PATH, protocol_raw, "protocol")

    frozen = _object(binding["code_freeze"], "binding code_freeze")
    _keys(frozen, {"commit", "tree"}, "binding code_freeze")
    commit = _oid(frozen["commit"], "binding code-freeze commit")
    tree = _oid(frozen["tree"], "binding code-freeze tree")
    if commit == PROTOCOL_COMMIT or tree == PROTOCOL_TREE:
        _fail("code-freeze objects must postdate protocol-only objects")
    _verify_git_tree(commit, tree, "code freeze")
    _verify_git_ancestor(PROTOCOL_COMMIT, commit)

    rows = _array(binding["code_files"], "binding code_files")
    _exact(len(rows), len(CODE_FILES), "binding code-file count")
    checked: list[dict[str, Any]] = []
    for index, (role, path_text, path) in enumerate(CODE_FILES):
        row = _object(rows[index], f"binding code_files[{index}]")
        raw = _read(path, f"code file {role}")
        _exact(row, _file_row(role, path, raw), f"binding code file {role}")
        _exact(row["path"], path_text, f"binding code file {role} path")
        _verify_git_file(commit, path_text, raw, f"code file {role}")
        checked.append(row)
    return {"commit": commit, "tree": tree}, checked


def validate_model_input(raw: bytes) -> dict[str, Any]:
    # This checked-in, SHA-bound human source intentionally preserves semantic
    # source order; unlike generated receipts it is not sorted canonical JSON.
    model = _object(parse_json(raw, "model input"), "model input")
    _exact(model.get("schema_version"), "controlled-queue-input-v1", "model input schema")
    _exact(model.get("model_version"), "controlled-queue-v1", "model input version")
    state_space = _object(model.get("state_space"), "model state_space")
    _exact(state_space.get("queue_capacity"), 7, "queue capacity")
    _exact(state_space.get("regime_count"), 3, "regime count")
    _exact(state_space.get("arrival_by_regime"), [0, 1, 2], "arrival table")
    actions = _array(model.get("actions"), "model actions")
    _exact(len(actions), 2, "model action count")
    for index, (action_id, service) in enumerate((("eco", 1), ("boost", 2))):
        action = _object(actions[index], f"model action {index}")
        _exact(action.get("id"), action_id, f"model action {index} id")
        _exact(action.get("service_capacity"), service, f"model action {index} service")
    behavior = _object(model.get("behavior_policy"), "model behavior policy")
    _exact(behavior.get("id"), "behavior_uniform", "model behavior policy id")
    probabilities = _array(behavior.get("boost_probability_by_state"), "model behavior probabilities")
    _exact(len(probabilities), STATE_COUNT, "behavior probability count")
    if any(_fraction(value, "behavior probability") != BEHAVIOR_MASS for value in probabilities):
        _fail("model behavior policy must be exactly uniform")
    return model


def validate_model_manifest(raw: bytes, model_input_path: Path, model_input_raw: bytes, model_tables_path: Path, model_tables_raw: bytes) -> dict[str, Any]:
    manifest = parse_canonical_object(raw, "model manifest")
    _exact(manifest.get("schema_version"), "controlled-queue-input-v1", "model manifest schema")
    _exact(manifest.get("model_version"), "controlled-queue-v1", "model manifest version")
    files = _array(manifest.get("files"), "model manifest files")
    _exact(len(files), 3, "model manifest file count")
    expected = (
        ("input", model_input_path, model_input_raw),
        ("output", model_tables_path, model_tables_raw),
    )
    for index, (role, path, file_raw) in enumerate(expected):
        row = _object(files[index], f"model manifest files[{index}]")
        _exact(row, {"path": _display(path), "role": role, "sha256": sha256(file_raw)}, f"model manifest files[{index}]")
    lean_row = _object(files[2], "model manifest Lean row")
    lean_path = _resolve_manifest_path(lean_row.get("path"), "model manifest Lean path")
    lean_raw = _read(lean_path, "model manifest Lean output")
    _exact(lean_row, {"path": _display(lean_path), "role": "output", "sha256": sha256(lean_raw)}, "model manifest Lean row")
    return manifest


def validate_trace_counts(raw: bytes, trace_raw: bytes, states: list[int], actions: list[int]) -> tuple[dict[str, Any], dict[str, Any]]:
    value = parse_canonical_object(raw, "trace counts")
    _keys(
        value,
        {"artifact_status", "counts", "final_action", "final_state", "generator_revision", "horizon", "initial_action", "initial_state", "nonclaims", "prng_audit", "schema_version", "trace_sha256", "trace_version"},
        "trace counts",
    )
    _exact(value["artifact_status"], TRACE_ARTIFACT_STATUS, "trace counts status")
    _exact(value["schema_version"], TRACE_COUNTS_SCHEMA, "trace counts schema")
    _exact(value["trace_version"], TRACE_VERSION, "trace counts version")
    _exact(value["generator_revision"], TRACE_GENERATOR_REVISION, "trace counts generator revision")
    _exact(value["horizon"], HORIZON, "trace counts horizon")
    _exact(value["initial_state"], 0, "trace counts initial state")
    _exact(value["initial_action"], 0, "trace counts initial action")
    _exact(value["final_state"], states[-1], "trace counts final state")
    _exact(value["final_action"], actions[-1], "trace counts final action")
    _exact(value["trace_sha256"], sha256(trace_raw), "trace counts trace hash")
    _exact(value["nonclaims"], TRACE_NONCLAIMS, "trace counts nonclaims")
    audit = _object(value["prng_audit"], "trace counts PRNG audit")
    _keys(audit, {"bytes_consumed", "digest_blocks_generated", "rejections_by_modulus", "version", "words_consumed"}, "trace counts PRNG audit")
    _exact(audit["version"], PRNG_VERSION, "trace counts PRNG version")
    words = _integer(audit["words_consumed"], "PRNG words", minimum=0)
    _exact(audit["bytes_consumed"], 8 * words, "PRNG bytes/words")
    _exact(
        _integer(audit["digest_blocks_generated"], "PRNG digest blocks", minimum=0),
        (words + 3) // 4,
        "PRNG digest blocks/words",
    )
    rejections = _object(audit["rejections_by_modulus"], "PRNG rejection counts")
    rejection_total = 0
    for modulus_text, rejection_count in rejections.items():
        if ROUND_RE.fullmatch(modulus_text) is None or str(int(modulus_text)) != modulus_text:
            _fail("PRNG rejection modulus is not a canonical positive integer")
        modulus = int(modulus_text)
        if not 1 <= modulus <= 1 << 64:
            _fail("PRNG rejection modulus lies outside the uint64 sampler range")
        rejection_total += _integer(
            rejection_count, f"PRNG rejections for modulus {modulus_text}", minimum=1
        )
    _exact(words, 2 * HORIZON + rejection_total, "PRNG accepted draws plus rejections")
    expected = physical_counts(states, actions)
    _exact(_object(value["counts"], "trace counts.counts"), expected, "replayed physical histogram")
    return value, expected


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
    _keys(manifest, {"artifact_status", "schema_version", "trace_version", "generator", "independent_verifier", "code_freeze", "registration", "beacon", "parameters", "inputs", "outputs", "manifest_note", "nonclaims"}, "trace manifest")
    _exact(manifest["artifact_status"], TRACE_ARTIFACT_STATUS, "trace manifest status")
    _exact(manifest["schema_version"], TRACE_MANIFEST_SCHEMA, "trace manifest schema")
    _exact(manifest["trace_version"], TRACE_VERSION, "trace manifest version")
    _exact(
        manifest["manifest_note"],
        "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "trace manifest note",
    )
    _exact(manifest["nonclaims"], TRACE_NONCLAIMS, "trace manifest nonclaims")
    inputs = _array(manifest["inputs"], "trace manifest inputs")
    roles = ["protocol", "osf_registration_response", "osf_registration_binding", "osf_registration_binding_file", "quicknet_chain_info", "quicknet_round", "model_input", "model_manifest", "model_tables"]
    _exact([_object(row, "trace input").get("role") for row in inputs], roles, "trace manifest input order")
    loaded: dict[str, tuple[Path, bytes, dict[str, Any]]] = {}
    for index, row in enumerate(inputs):
        role, path, file_raw, checked = _read_manifest_row(row, f"trace manifest inputs[{index}]")
        loaded[role] = (path, file_raw, checked)
    for role, path, file_raw in (
        ("protocol", protocol_path, protocol_raw),
        ("model_input", model_input_path, model_input_raw),
        ("model_manifest", model_manifest_path, model_manifest_raw),
        ("model_tables", model_tables_path, model_tables_raw),
    ):
        actual_path, actual_raw, _ = loaded[role]
        _exact(actual_path.resolve(), path.resolve(), f"trace input {role} path")
        _exact(actual_raw, file_raw, f"trace input {role} bytes")
    for role, expected_path in TRACE_EVIDENCE_PATHS.items():
        actual_path, _actual_raw, checked = loaded[role]
        _exact(actual_path.resolve(), expected_path.resolve(), f"trace input {role} path")
        _exact(checked["path"], _display(expected_path), f"trace input {role} manifest path")

    registration_value = _object(
        parse_json(loaded["osf_registration_response"][1], "OSF registration response"),
        "OSF registration response",
    )
    registration_id, date_registered, registration_second = _verify_osf_registration(registration_value)
    binding_raw = loaded["osf_registration_binding"][1]
    binding = parse_canonical_object(binding_raw, "OSF code-freeze binding")
    code_freeze, code_rows = _validate_code_freeze_binding(binding, protocol_raw)
    binding_file = _object(
        parse_json(loaded["osf_registration_binding_file"][1], "OSF binding-file response"),
        "OSF binding-file response",
    )
    _verify_osf_binding_file(binding_file, registration_id, binding_raw)

    chain = _object(
        parse_json(loaded["quicknet_chain_info"][1], "quicknet chain info"),
        "quicknet chain info",
    )
    _keys(
        chain,
        {"public_key", "period", "genesis_time", "genesis_seed", "chain_hash", "scheme", "beacon_id"},
        "quicknet chain info",
    )
    _exact(chain.get("public_key"), PUBLIC_KEY, "quicknet public key")
    _exact(chain.get("chain_hash"), CHAIN_HASH, "quicknet chain hash")
    _exact(chain.get("genesis_seed"), GROUP_HASH, "quicknet group hash")
    _exact(chain.get("scheme"), SCHEME_ID, "quicknet scheme")
    _exact(chain.get("beacon_id"), BEACON_ID, "quicknet beacon id")
    _exact(chain.get("period"), PERIOD_SECONDS, "quicknet period")
    _exact(chain.get("genesis_time"), GENESIS_SECONDS, "quicknet genesis")
    round_number, round_time = _formula_round(registration_second)
    round_value = _object(
        parse_json(loaded["quicknet_round"][1], "quicknet round"),
        "quicknet round",
    )
    _keys(round_value, {"round", "signature", "randomness"}, "quicknet round")
    _exact(round_value["round"], round_number, "quicknet formula-selected round")
    signature = _hex_bytes(round_value["signature"], 48, "quicknet signature")
    _exact(round_value["randomness"], sha256(signature), "quicknet randomness identity")
    seed = hashlib.sha256(
        b"FormalSLT/controlled-queue/prospective-structured-ope-v1\0"
        + bytes.fromhex(CHAIN_HASH)
        + round_number.to_bytes(8, "big")
        + signature
    ).digest()

    registration = _object(manifest["registration"], "trace manifest registration")
    _exact(registration, {
        "api_response_sha256": sha256(loaded["osf_registration_response"][1]),
        "binding_file_api_response_sha256": sha256(loaded["osf_registration_binding_file"][1]),
        "binding_sha256": sha256(binding_raw),
        "date_registered": date_registered,
        "id": registration_id,
        "protocol_commit": PROTOCOL_COMMIT,
        "protocol_tree": PROTOCOL_TREE,
        "unix_seconds_ceiling": registration_second,
    }, "trace manifest registration")
    beacon = _object(manifest["beacon"], "trace manifest beacon")
    _exact(
        beacon,
        {
            "chain_hash": CHAIN_HASH,
            "group_hash": GROUP_HASH,
            "scheme_id": SCHEME_ID,
            "round": round_number,
            "round_time_unix_seconds": round_time,
            "randomness": sha256(signature),
            "signature_sha256": sha256(signature),
            "derived_seed_sha256": sha256(seed),
            "signature_verified": True,
            "signature_verifier": {
                "implementation": BLS_IMPLEMENTATION,
                "dependency": "py-ecc",
                "version": PY_ECC_VERSION,
                "dst": BLS_DST,
            },
        },
        "trace manifest beacon",
    )
    frozen = _object(manifest["code_freeze"], "trace manifest code freeze")
    _exact(frozen, {"code_files": code_rows, **code_freeze}, "trace manifest code freeze")

    generator = _object(manifest["generator"], "trace manifest generator")
    _exact(generator, {key: code_rows[0][key] for key in ("bytes", "path", "sha256")} | {"revision": TRACE_GENERATOR_REVISION}, "trace manifest generator")
    verifier = _object(manifest["independent_verifier"], "trace manifest independent verifier")
    _exact(verifier, {key: code_rows[1][key] for key in ("bytes", "path", "sha256")}, "trace manifest independent verifier")
    _exact(manifest["parameters"], {
        "action_count": ACTION_COUNT,
        "behavior_policy": "behavior_uniform",
        "binary_expected_bytes": BINARY_BYTES,
        "binary_magic_hex": BINARY_MAGIC.hex(),
        "binary_version": BINARY_VERSION,
        "family": "refreshEnvironment",
        "horizon": HORIZON,
        "initial_action": 0,
        "initial_state": 0,
        "prng_version": PRNG_VERSION,
        "sampling_version": SAMPLING_VERSION,
        "state_count": STATE_COUNT,
        "true_gamma": "149/200",
    }, "trace manifest parameters")
    outputs = _array(manifest["outputs"], "trace manifest outputs")
    _exact(len(outputs), 2, "trace manifest output count")
    for index, (role, path, file_raw) in enumerate((("trace_binary", trace_path, trace_raw), ("trace_counts", counts_path, counts_raw))):
        row = _object(outputs[index], f"trace manifest outputs[{index}]")
        _exact(row, _file_row(role, path, file_raw), f"trace manifest output {role}")

    all_rows = [*inputs, *outputs, *code_rows]
    all_roles = [row["role"] for row in all_rows]
    path_keys = [unicodedata.normalize("NFC", row["path"]).casefold() for row in all_rows]
    if len(all_roles) != len(set(all_roles)):
        _fail("trace manifest provenance roles are not globally unique")
    if len(path_keys) != len(set(path_keys)):
        _fail("trace manifest provenance paths are not globally unique")
    return manifest


def validate_bound_sources(
    protocol: dict[str, Any],
    sources: Sequence[tuple[str, Path, bytes]],
) -> None:
    bindings = _object(protocol.get("bindings"), "protocol bindings")
    for role, path, raw in sources:
        row = _object(bindings.get(role), f"protocol bindings.{role}")
        _exact(row, {"path": _display(path), "sha256": sha256(raw)}, f"protocol bindings.{role}")


def recompute_statistics_and_rows(
    states: list[int],
    actions: list[int],
    histogram: list[list[list[int]]],
    model: dict[str, Any],
    deterministic: dict[str, Any],
) -> dict[str, Any]:
    n = len(states) - 1
    _exact(n, HORIZON, "receipt transition count")
    hits = sum(
        int(states[k + 1] == queue_step(states[k], actions[k + 1]))
        for k in range(n)
    )
    augmented_edges, augmented_visits = augmented_counts(states, actions)
    selected_summary = normalized_score_summary(
        histogram,
        model["target_policies"][1],
        model["losses"][2],
        deterministic["selected"]["potential"],
        PRIMARY_B,
    )
    nominal_persistence = structured_eta(CANDIDATE_HITS[1], hits, n, tilt=Fraction(1, 64), log_upper=7)
    primary_risk = empirical_bernstein_correction(selected_summary, log_upper=9, tilt=Fraction(1, 16))
    primary_residual = PRIMARY_DRIFT + PRIMARY_SENSITIVITY * nominal_persistence["eta"]
    primary_total = selected_summary["empirical_corrected_score"] + primary_risk + primary_residual

    score_catalog = build_score_catalog(histogram, model, deterministic)
    adaptive = select_adaptive_endpoint(score_catalog, hits, n)
    adaptive_selected = adaptive["selected"]

    oracle_table = deterministic["oracle"]
    oracle_summary = normalized_score_summary(
        histogram,
        model["target_policies"][1],
        model["losses"][2],
        oracle_table["potential"],
        oracle_table["actual_span"],
    )
    oracle_risk = empirical_bernstein_correction(oracle_summary, log_upper=8, tilt=Fraction(1, 16))
    oracle_total = oracle_summary["empirical_corrected_score"] + oracle_risk + oracle_table["drift_oscillation"]

    generic: dict[int, dict[str, Any]] = {}
    for depth in (12, 5):
        table = deterministic["candidate_tables"][1][DEPTHS.index(depth)][5]
        summary = normalized_score_summary(
            histogram,
            model["target_policies"][1],
            model["losses"][2],
            table["potential"],
            table["closed_span_bound"],
        )
        risk = empirical_bernstein_correction(summary, log_upper=9, tilt=Fraction(1, 16))
        residual = CANDIDATE_GAMMAS[1] ** depth + 2 * (1 + summary["span_bound"]) * nominal_persistence["eta"]
        generic[depth] = {"summary": summary, "risk": risk, "residual": residual, "total": summary["empirical_corrected_score"] + risk + residual}

    fixed_eta = fixed_range_eta(CANDIDATE_HITS[1], hits, n)
    fixed_risk = fixed_range_risk_correction(selected_summary["scale"], n)
    fixed_residual = PRIMARY_DRIFT + PRIMARY_SENSITIVITY * fixed_eta["eta"]
    fixed_total = selected_summary["empirical_corrected_score"] + fixed_risk + fixed_residual

    unstructured = unstructured_transition_summary(augmented_edges, augmented_visits, model["candidate_kernels"][1], n)
    unstructured_residual = CANDIDATE_GAMMAS[1] ** 12 + 4 * (1 + generic[12]["summary"]["span_bound"]) * unstructured["eta_augmented"]
    unstructured_total = generic[12]["summary"]["empirical_corrected_score"] + generic[12]["risk"] + unstructured_residual

    return {
        "physical_histogram": histogram,
        "augmented_edges": augmented_edges,
        "augmented_visits": augmented_visits,
        "persistence_hit_count": hits,
        "selected_summary": selected_summary,
        "nominal_persistence": nominal_persistence,
        "primary": {"risk": primary_risk, "residual": primary_residual, "total": primary_total},
        "score_catalog": score_catalog,
        "adaptive": adaptive,
        "oracle_summary": oracle_summary,
        "oracle": {"risk": oracle_risk, "residual": oracle_table["drift_oscillation"], "total": oracle_total},
        "generic": generic,
        "fixed_eta": fixed_eta,
        "fixed": {"risk": fixed_risk, "residual": fixed_residual, "total": fixed_total},
        "unstructured": unstructured,
        "unstructured_residual": unstructured_residual,
        "unstructured_total": unstructured_total,
        "causal": causal_beta_summaries(states, actions),
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


def _public_score_summary(summary: dict[str, Any]) -> dict[str, Any]:
    return {
        key: (
            number(value)
            if isinstance(value, Fraction)
            else [[number(entry) for entry in row] for row in value]
        )
        for key, value in summary.items()
    }


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


def _vacuity(
    total: Fraction,
    *,
    primary: bool = False,
    planned: bool = False,
    premise_ok: bool = True,
) -> dict[str, Any]:
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


def build_expected_receipt(
    *,
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
    sharp_receipt_core_source_path: Path,
    sharp_receipt_core_source_raw: bytes,
    deterministic: dict[str, Any],
    states: list[int],
    actions: list[int],
    physical: dict[str, Any],
    model: dict[str, Any],
) -> dict[str, Any]:
    n = len(states) - 1
    stats = recompute_statistics_and_rows(
        states, actions, physical["edge_counts"], model, deterministic
    )
    hits = stats["persistence_hit_count"]
    selected = deterministic["selected"]
    oracle = deterministic["oracle"]
    primary_score = stats["selected_summary"]
    primary_persistence = stats["nominal_persistence"]
    adaptive = stats["adaptive"]
    adaptive_selected = adaptive["selected"]
    oracle_score = stats["oracle_summary"]
    generic12 = stats["generic"][12]
    generic5 = stats["generic"][5]
    fixed_eta = stats["fixed_eta"]
    unstructured = stats["unstructured"]

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
            risk=stats["primary"]["risk"],
            radius=primary_persistence["eta"],
            residual=stats["primary"]["residual"],
            total=stats["primary"]["total"],
            confidence=fixed_confidence,
            settings={"candidate_index": 1, "depth": 12, "policy_index": 1, "predictor_index": 2, "posterior_index": 5, "fixed_before_data": True},
            vacuity=_vacuity(stats["primary"]["total"], primary=True),
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
            confidence={"delta_risk": "1/40", "delta_persistence": "1/40", "delta_total": "1/20", "candidate_depth_weight": "1/21", "risk_tilt_weight": "1/4", "persistence_tilt_weight": "1/4"},
            settings={
                "indices": adaptive_selected["indices"],
                "tie_break_order": ["candidate_index", "depth_index", "risk_tilt_index", "persistence_tilt_index", "posterior_index"],
                "selector_received_true_gamma": False,
            },
            vacuity=_vacuity(adaptive_selected["total_certified_rhs"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[2],
            theorem_or_event=_event(
                "oracle_true_kernel_event",
                "exists_controlledQueueKnownKernelOPE_event",
                "SEPARATE_CHECKED_TRUE_KERNEL_EVENT",
                checked_outer_mass=Fraction(1, 20),
                planned_allocation=None,
            ),
            certification_status=checked_status,
            empirical=oracle_score["empirical_corrected_score"],
            risk=stats["oracle"]["risk"],
            radius=Fraction(0),
            residual=stats["oracle"]["residual"],
            total=stats["oracle"]["total"],
            confidence={"delta_risk": "1/20", "delta_total": "1/20", "risk_tilt": "1/16"},
            settings={"true_gamma": "149/200", "depth": 12, "policy_index": 1, "predictor_index": 2, "precomputed_before_trace_decode": True},
            vacuity=_vacuity(stats["oracle"]["total"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[3],
            theorem_or_event=_event(
                "generic_nominal_depth12_event",
                "exists_structuredControlledQueueFiniteCatalogOPE_event",
                "SEPARATE_CHECKED_FIXED_ATOM_EVENT",
                checked_outer_mass=Fraction(1, 20),
                planned_allocation=None,
            ),
            certification_status=checked_status,
            empirical=generic12["summary"]["empirical_corrected_score"],
            risk=generic12["risk"],
            radius=primary_persistence["eta"],
            residual=generic12["residual"],
            total=generic12["total"],
            confidence=fixed_confidence,
            settings={"candidate_index": 1, "depth": 12, "policy_index": 1, "predictor_index": 2, "fixed_before_data": True},
            vacuity=_vacuity(generic12["total"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[4],
            theorem_or_event=_event(
                "generic_nominal_depth5_event",
                "exists_structuredControlledQueueFiniteCatalogOPE_event",
                "SEPARATE_CHECKED_FIXED_ATOM_EVENT",
                checked_outer_mass=Fraction(1, 20),
                planned_allocation=None,
            ),
            certification_status=checked_status,
            empirical=generic5["summary"]["empirical_corrected_score"],
            risk=generic5["risk"],
            radius=primary_persistence["eta"],
            residual=generic5["residual"],
            total=generic5["total"],
            confidence=fixed_confidence,
            settings={"candidate_index": 1, "depth": 5, "policy_index": 1, "predictor_index": 2, "fixed_before_data": True},
            vacuity=_vacuity(generic5["total"]),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[5],
            theorem_or_event=_event(
                "fixed_range_planned_arithmetic",
                None,
                "PLANNED_ARITHMETIC_ONLY",
                checked_outer_mass=None,
                planned_allocation=Fraction(1, 20),
            ),
            certification_status="PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE",
            empirical=primary_score["empirical_corrected_score"],
            risk=stats["fixed"]["risk"],
            radius=fixed_eta["eta"],
            residual=stats["fixed"]["residual"],
            total=stats["fixed"]["total"],
            confidence={**fixed_confidence, "confidence_claim": "NOT_A_CONFIDENCE_CERTIFICATE"},
            settings={"candidate_index": 1, "depth": 12, "fixed_range_arithmetic_only": True},
            vacuity=_vacuity(stats["fixed"]["total"], planned=True),
        ),
        _report_row(
            endpoint_id=ROW_ORDER[6],
            theorem_or_event=_event(
                "unstructured_4608_coordinate_event",
                "exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event",
                "SEPARATE_CHECKED_EVENT_WITH_VISIT_PREMISE",
                checked_outer_mass=Fraction(1, 20),
                planned_allocation=None,
            ),
            certification_status=(checked_status if unstructured["all_augmented_source_rows_visited"] else "PREMISE_FAILED_ZERO_AUGMENTED_SOURCE_VISIT"),
            empirical=generic12["summary"]["empirical_corrected_score"],
            risk=generic12["risk"],
            radius=unstructured["eta_augmented"],
            residual=stats["unstructured_residual"],
            total=stats["unstructured_total"],
            confidence={"delta_risk": "1/40", "delta_transition": "1/40", "delta_total": "1/20", "coordinate_prior_mass": "1/4608", "risk_tilt": "1/16", "transition_tilt": "1/64"},
            settings={"candidate_index": 1, "depth": 12, "coordinate_count": 2304, "oriented_coordinate_count": 4608, "all_augmented_source_rows_visited": unstructured["all_augmented_source_rows_visited"]},
            vacuity=_vacuity(stats["unstructured_total"], premise_ok=unstructured["all_augmented_source_rows_visited"]),
        ),
    ]
    _exact([row["endpoint_id"] for row in rows], list(ROW_ORDER), "receipt reporting row order")
    if "NOT_A_CONFIDENCE_CERTIFICATE" not in rows[5]["certification_status"]:
        _fail("fixed-range row was mislabeled as a confidence certificate")

    adaptive_stats = [
        {
            **{key: row[key] for key in ("candidate_index", "depth_index", "depth", "posterior_index", "policy_index", "predictor_index")},
            "score_summary": _public_score_summary(row["summary"]),
        }
        for row in stats["score_catalog"]
    ]
    adaptive_minimum = [
        {"indices": row["indices"], "total_certified_rhs": number(row["total_certified_rhs"])}
        for row in adaptive["catalog_minimum_certificate"]
    ]
    persistence_catalog = [
        {"candidate_index": candidate_index, "persistence_tilt_index": tilt_index, "summary": _public_fraction_dict(summary)}
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

    receipt_only_inputs = [
        _file_row("trace_binary", trace_path, trace_raw),
        _file_row("trace_counts", counts_path, counts_raw),
        _file_row("trace_manifest", trace_manifest_path, trace_manifest_raw),
        _file_row("pilot_selected_potential_data", selected_data_path, selected_data_raw),
        _file_row("known_kernel_receipt_source", known_kernel_source_path, known_kernel_source_raw),
        _file_row("persistence_confidence_source", persistence_source_path, persistence_source_raw),
        _file_row("structured_ope_source", structured_source_path, structured_source_raw),
        _file_row("sharp_structured_ope_source", sharp_structured_source_path, sharp_structured_source_raw),
        _file_row("sharp_receipt_core_source", sharp_receipt_core_source_path, sharp_receipt_core_source_raw),
    ]
    receipt = {
        "schema_version": RECEIPT_SCHEMA,
        "receipt_version": RECEIPT_VERSION,
        "artifact_status": ARTIFACT_STATUS,
        "protocol_binding": {"path": _display(protocol_path), "bytes": len(protocol_raw), "sha256": sha256(protocol_raw), "commit": PROTOCOL_COMMIT, "tree": PROTOCOL_TREE},
        "trace_manifest_binding": {"path": _display(trace_manifest_path), "bytes": len(trace_manifest_raw), "sha256": sha256(trace_manifest_raw), "schema_version": TRACE_MANIFEST_SCHEMA, "trace_version": TRACE_VERSION},
        "registration": trace_manifest["registration"],
        "beacon": trace_manifest["beacon"],
        "code_freeze": trace_manifest["code_freeze"],
        "inputs": [dict(row) for row in trace_manifest["inputs"]] + receipt_only_inputs,
        "trace_summary": {
            "horizon": n,
            "initial_state": states[0],
            "dummy_initial_action": actions[0],
            "final_state": states[-1],
            "final_action": actions[-1],
            "first_scored_transition": [states[0], actions[1], states[1]],
            "terminal_scored_transition": [states[n - 1], actions[n], states[n]],
            "action_indexing": "score k uses A_(k+1), never dummy A_0 or A_k",
            "trace_sha256": sha256(trace_raw),
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
            "physical_transition_histogram": physical["edge_counts"],
            "physical_source_visits": physical["source_state_visits"],
            "physical_state_action_counts": physical["state_action_counts"],
            "augmented_transition_histogram": stats["augmented_edges"],
            "augmented_source_visits": stats["augmented_visits"],
            "all_augmented_source_rows_visited": all(visit > 0 for visit in stats["augmented_visits"]),
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
        "dynamic_encountered_risk": stats["causal"],
        "nonclaims": list(NONCLAIMS),
    }
    _keys(receipt, {"schema_version", "receipt_version", "artifact_status", "protocol_binding", "trace_manifest_binding", "registration", "beacon", "code_freeze", "inputs", "trace_summary", "deterministic_tables", "sufficient_statistics", "reporting_rows", "dynamic_encountered_risk", "nonclaims"}, "receipt top-level")
    return receipt


def build_expected_manifest(
    *,
    receipt: dict[str, Any],
    receipt_path: Path,
    receipt_raw: bytes,
    lean_path: Path,
    lean_raw: bytes,
    generator_path: Path = DEFAULT_GENERATOR,
    verifier_path: Path = DEFAULT_VERIFIER,
) -> dict[str, Any]:
    generator_raw = _read(generator_path, "receipt generator")
    verifier_raw = _read(verifier_path, "receipt verifier")
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
            "sha256": sha256(generator_raw),
        },
        "independent_verifier": {
            "bytes": len(verifier_raw),
            "path": _display(verifier_path),
            "sha256": sha256(verifier_raw),
        },
        "inputs": receipt["inputs"],
        "outputs": [
            _file_row("receipt", receipt_path, receipt_raw),
            _file_row("lean_data", lean_path, lean_raw),
        ],
        "manifest_note": "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "nonclaims": list(NONCLAIMS),
    }


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


def render_expected_lean(receipt: dict[str, Any]) -> bytes:
    """Independently render the frozen conditional Lean instantiation."""

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
good-event membership, or a confidence theorem.  The fixed-range row remains
`PLANNED_NOT_CHECKED`.
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
    rendered = content.encode("utf-8")
    _validate_lean_contract(rendered)
    return rendered


def _validate_lean_contract(rendered: bytes) -> None:
    required = (
        b"import FormalSLT.Applications.ControlledQueueSharpStructuredReceiptCore",
        b"HasPhysicalTransitionHistogram",
        b"sharpStructuredReceiptBoundary_evaluation_of_histogram",
        b"prospectiveHistogramUpper_eq",
        b"prospectiveCertificate_23_1",
        b"prospectiveStateCertificate_23",
        b"private noncomputable def prospectiveActualScoreRow",
        b"private structure ProspectiveStateSubtotalCertificate",
        b"#print axioms FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData.prospectiveSharpStructuredEndpoint_le",
    )
    if any(fragment not in rendered for fragment in required):
        _fail("generated Lean lacks a required conditional histogram certificate")
    if b"PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE" not in rendered:
        _fail("generated Lean relabeled the fixed-range arithmetic row")


def _path_identity(path: Path) -> str:
    return unicodedata.normalize("NFC", path.absolute().as_posix()).casefold()


def _has_symlink_component(path: Path) -> bool:
    absolute = path.absolute()
    current = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        current = current / part
        if current.is_symlink():
            return True
    return False


def _validate_supplied_paths(paths: dict[str, Path]) -> None:
    _exact(set(paths), set(EXPECTED_SUPPLIED_PATHS), "supplied path roles")
    seen: dict[str, str] = {}
    for role, path in paths.items():
        if _has_symlink_component(path):
            _fail(f"supplied path for {role} contains a symbolic-link component: {path}")
        identity = _path_identity(path)
        if identity in seen:
            _fail(f"supplied paths alias: {seen[identity]} and {role}")
        seen[identity] = role
        _exact(
            path.resolve(),
            EXPECTED_SUPPLIED_PATHS[role].resolve(),
            f"frozen supplied path for {role}",
        )


def verify_paths(
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
    sharp_receipt_core_source_path: Path,
    receipt_path: Path,
    receipt_manifest_path: Path,
    lean_path: Path,
) -> dict[str, Any]:
    """Recompute and byte-compare all prospective receipt artifacts."""

    supplied = {
        "protocol": protocol_path,
        "trace": trace_path,
        "counts": counts_path,
        "trace_manifest": trace_manifest_path,
        "model_input": model_input_path,
        "model_manifest": model_manifest_path,
        "model_tables": model_tables_path,
        "selected_data": selected_data_path,
        "known_kernel_source": known_kernel_source_path,
        "persistence_source": persistence_source_path,
        "structured_source": structured_source_path,
        "sharp_structured_source": sharp_structured_source_path,
        "sharp_receipt_core_source": sharp_receipt_core_source_path,
        "receipt": receipt_path,
        "receipt_manifest": receipt_manifest_path,
        "lean": lean_path,
    }
    _validate_supplied_paths(supplied)

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
    sharp_receipt_core_source_raw = _read(sharp_receipt_core_source_path, "sharp receipt-core source")
    validate_bound_sources(
        protocol,
        (
            ("model_input", model_input_path, model_input_raw),
            ("model_manifest", model_manifest_path, model_manifest_raw),
            ("model_tables", model_tables_path, model_tables_raw),
            ("pilot_selected_potential_data", selected_data_path, selected_data_raw),
            ("known_kernel_receipt_source", known_kernel_source_path, known_kernel_source_raw),
            ("persistence_confidence_source", persistence_source_path, persistence_source_raw),
            ("structured_ope_source", structured_source_path, structured_source_raw),
        ),
    )
    validate_model_input(model_input_raw)
    validate_model_manifest(
        model_manifest_raw,
        model_input_path,
        model_input_raw,
        model_tables_path,
        model_tables_raw,
    )
    model = parse_model_tables(model_tables_raw)

    # Load-bearing chronology: reconstruct true-kernel oracle and every
    # selector candidate before reading or decoding any trace byte.
    deterministic = compute_deterministic_tables(model)
    trace_raw = _read(trace_path, "prospective trace")
    states, actions = decode_trace(trace_raw)
    counts_raw = _read(counts_path, "prospective trace counts")
    _counts, physical = validate_trace_counts(counts_raw, trace_raw, states, actions)
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
    freeze_commit = _oid(
        _object(trace_manifest["code_freeze"], "trace manifest code freeze").get("commit"),
        "trace manifest code-freeze commit",
    )
    _verify_git_file(
        freeze_commit,
        SHARP_STRUCTURED_SOURCE_PATH,
        sharp_structured_source_raw,
        "sharp structured-OPE source",
    )
    _verify_git_file(
        freeze_commit,
        SHARP_RECEIPT_CORE_SOURCE_PATH,
        sharp_receipt_core_source_raw,
        "sharp receipt-core source",
    )
    expected_receipt = build_expected_receipt(
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
        sharp_receipt_core_source_path=sharp_receipt_core_source_path,
        sharp_receipt_core_source_raw=sharp_receipt_core_source_raw,
        deterministic=deterministic,
        states=states,
        actions=actions,
        physical=physical,
        model=model,
    )
    expected_receipt_raw = canonical_json(expected_receipt)
    expected_lean_raw = render_expected_lean(expected_receipt)
    expected_manifest = build_expected_manifest(
        receipt=expected_receipt,
        receipt_path=receipt_path,
        receipt_raw=expected_receipt_raw,
        lean_path=lean_path,
        lean_raw=expected_lean_raw,
    )
    expected_manifest_raw = canonical_json(expected_manifest)

    receipt_raw = _read(receipt_path, "prospective receipt")
    actual_receipt = parse_canonical_object(receipt_raw, "prospective receipt")
    rows = _array(actual_receipt.get("reporting_rows"), "receipt reporting rows")
    if len(rows) != 7:
        _fail("receipt must contain exactly seven reporting rows")
    fixed = _object(rows[5], "fixed-range reporting row")
    if fixed.get("endpoint_id") != ROW_ORDER[5] or "NOT_A_CONFIDENCE_CERTIFICATE" not in _string(fixed.get("certification_status"), "fixed-range certification status"):
        _fail("fixed-range arithmetic was relabeled as a confidence certificate")
    _exact(receipt_raw, expected_receipt_raw, "independently reconstructed receipt bytes")

    lean_raw = _read(lean_path, "generated Lean data")
    _validate_lean_contract(lean_raw)
    _exact(lean_raw, expected_lean_raw, "independently rendered Lean bytes")

    manifest_raw = _read(receipt_manifest_path, "prospective receipt manifest")
    actual_manifest = parse_canonical_object(manifest_raw, "prospective receipt manifest")
    _exact(actual_manifest, expected_manifest, "independently reconstructed receipt manifest")
    _exact(manifest_raw, expected_manifest_raw, "independently rendered receipt-manifest bytes")
    return {
        "receipt_sha256": sha256(receipt_raw),
        "lean_sha256": sha256(lean_raw),
        "manifest_sha256": sha256(manifest_raw),
        "primary_upper": expected_receipt["reporting_rows"][0]["total_certified_rhs"]["rational"],
        "primary_threshold_met": expected_receipt["reporting_rows"][0]["vacuity_and_threshold_status"]["below_primary_threshold"],
    }


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
    parser.add_argument("--sharp-receipt-core-source", type=Path, default=DEFAULT_SHARP_RECEIPT_CORE_SOURCE)
    parser.add_argument("--receipt", "--receipt-output", dest="receipt", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--manifest", "--manifest-output", dest="manifest", type=Path, default=DEFAULT_RECEIPT_MANIFEST)
    parser.add_argument("--lean", "--lean-output", dest="lean", type=Path, default=DEFAULT_LEAN)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        result = verify_paths(
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
            sharp_receipt_core_source_path=args.sharp_receipt_core_source,
            receipt_path=args.receipt,
            receipt_manifest_path=args.manifest,
            lean_path=args.lean,
        )
    except VerificationError as error:
        print(f"prospective controlled-queue receipt verification failed: {error}", file=sys.stderr)
        return 1
    print(
        "verified prospective controlled-queue receipt, seven exact rows, "
        "conditional Lean instantiation, and manifest; "
        f"primary_upper={result['primary_upper']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
