#!/usr/bin/env python3
"""Generate the single preregistered controlled-queue prospective trace.

This is an offline, fail-closed code-freeze tool.  It never fetches OSF or
drand data and it never chooses a beacon round.  Generation is possible only
after the caller supplies archived public-registration evidence, the OSF-bound
code-freeze record, the exact formula-selected quicknet response, and a valid
quicknet BLS signature.  The output contains only a raw state/action path and
raw count tables; this module deliberately has no endpoint implementation.

The default evidence files do not exist during code freeze, so running this
script now must fail without creating any prospective artifact.
"""

from __future__ import annotations

import argparse
import calendar
import hashlib
import importlib.metadata
import json
import math
import os
import re
import struct
import subprocess
import sys
import tempfile
import unicodedata
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path, PurePosixPath
from typing import Any, Callable, NoReturn, Sequence


ROOT = Path(__file__).resolve().parents[1]

DEFAULT_PROTOCOL = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "structured-ope-protocol-v1.json"
)
DEFAULT_OSF_REGISTRATION = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "evidence"
    / "osf-registration-v1.json"
)
DEFAULT_OSF_BINDING = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "evidence"
    / "code-freeze-binding-v1.json"
)
DEFAULT_OSF_BINDING_FILE = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "evidence"
    / "osf-code-freeze-binding-file-v1.json"
)
DEFAULT_QUICKNET_CHAIN_INFO = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "evidence"
    / "quicknet-chain-info-v1.json"
)
DEFAULT_QUICKNET_ROUND = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "evidence"
    / "quicknet-round-v1.json"
)
DEFAULT_MODEL_INPUT = ROOT / "applications" / "controlled_queue" / "model-v1.json"
DEFAULT_MODEL_MANIFEST = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "generated"
    / "model-v1-manifest.json"
)
DEFAULT_MODEL_TABLES = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "generated"
    / "model-v1-tables.json"
)
DEFAULT_TRACE_OUTPUT = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "generated"
    / "structured-ope-trace-v1.bin"
)
DEFAULT_COUNTS_OUTPUT = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "generated"
    / "structured-ope-trace-v1-counts.json"
)
DEFAULT_MANIFEST_OUTPUT = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "prospective"
    / "generated"
    / "structured-ope-trace-v1-manifest.json"
)
DEFAULT_TRACE_VERIFIER = ROOT / "scripts" / "verify_controlled_queue_prospective_trace.py"

PROTOCOL_PATH = "applications/controlled_queue/structured-ope-protocol-v1.json"
OSF_REGISTRATION_PATH = (
    "applications/controlled_queue/prospective/evidence/osf-registration-v1.json"
)
OSF_BINDING_PATH = (
    "applications/controlled_queue/prospective/evidence/code-freeze-binding-v1.json"
)
OSF_BINDING_FILE_PATH = (
    "applications/controlled_queue/prospective/evidence/"
    "osf-code-freeze-binding-file-v1.json"
)
QUICKNET_CHAIN_INFO_PATH = (
    "applications/controlled_queue/prospective/evidence/quicknet-chain-info-v1.json"
)
QUICKNET_ROUND_PATH = (
    "applications/controlled_queue/prospective/evidence/quicknet-round-v1.json"
)
MODEL_INPUT_PATH = "applications/controlled_queue/model-v1.json"
MODEL_MANIFEST_PATH = "applications/controlled_queue/generated/model-v1-manifest.json"
MODEL_TABLES_PATH = "applications/controlled_queue/generated/model-v1-tables.json"
TRACE_OUTPUT_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1.bin"
)
COUNTS_OUTPUT_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-counts.json"
)
MANIFEST_OUTPUT_PATH = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-manifest.json"
)

PROTOCOL_SCHEMA = "controlled-queue-structured-ope-preregistration-v1"
PROTOCOL_VERSION = "controlled-queue-structured-ope-protocol-v1"
EXPECTED_PROTOCOL_SHA256 = (
    "070519615ba7cdaf0198a72a03ab6f691a7ff9b37c2eaa97a363d7fd4c3bf153"
)
EXPECTED_PROTOCOL_COMMIT = "65d8d56245e3862821fce09bcf30b017f03d2baa"
EXPECTED_PROTOCOL_TREE = "8dbe01780fd2cec94b8b954f6ef1c8c210afee53"

BINDING_SCHEMA = "controlled-queue-prospective-code-freeze-binding-v1"
BINDING_STATUS = "PUBLIC OSF CODE FREEZE BINDING"
COUNTS_SCHEMA = "controlled-queue-prospective-trace-counts-v1"
MANIFEST_SCHEMA = "controlled-queue-prospective-trace-manifest-v1"
TRACE_VERSION = "controlled-queue-prospective-trace-v1"
GENERATOR_REVISION = "controlled-queue-prospective-trace-generator-v1"
ARTIFACT_STATUS = "PROSPECTIVE TRACE/PREPROCESSING ONLY - NO ENDPOINT"

HORIZON = 200_000
STATE_COUNT = 24
ACTION_COUNT = 2
INITIAL_STATE = 0
INITIAL_ACTION = 0
TRUE_GAMMA = Fraction(149, 200)
TRUE_HIT_PROBABILITY = Fraction(1209, 1600)

BINARY_VERSION = "controlled-queue-prospective-trace-binary-v1"
BINARY_MAGIC = b"FSLTCQSP1\n"
BINARY_HEADER = struct.Struct(">10sQQQ")
BINARY_EXPECTED_BYTES = 400_036
UINT64_SPACE = 1 << 64

PRNG_VERSION = "sha256-counter-stream-v1"
SAMPLING_VERSION = "exact-categorical-u64-rejection-v1"
PRNG_DOMAIN = "FormalSLT/controlled-queue/prospective-structured-ope-v1"
TEST_SEED_HEX = "ac40e6b078e9298f9b271e6d7ed690b8911fa1e3f7005deff855ca43d94d5fcf"
TEST_COUNTER_ZERO_DIGEST_HEX = (
    "02be0e953603f95244eea43f8a16795185b337e881a64248d260219cfb7721ca"
)

QUICKNET_CHAIN_HASH = (
    "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971"
)
QUICKNET_GROUP_HASH = (
    "f477d5c89f21a17c863a7f937c6a6d15859414d2be09cd448d4279af331c5d3e"
)
QUICKNET_PUBLIC_KEY = (
    "83cf0f2896adee7eb8b5f01fcad3912212c437e0073e911fb90022d3e760183c8"
    "c4b450b6a0a6c3ac6a5776a2d1064510d1fec758c921cc22b0e17e63aaf4bcb5"
    "ed66304de9cf809bd274ca73bab4af5a6e9c76a4bc09e76eae8991ef5ece45a"
)
QUICKNET_SCHEME = "bls-unchained-g1-rfc9380"
QUICKNET_BEACON_ID = "quicknet"
QUICKNET_GENESIS = 1_692_803_367
QUICKNET_PERIOD = 3
REGISTRATION_DELAY_SECONDS = 3_600

PY_ECC_DISTRIBUTION = "py-ecc"
PY_ECC_VERSION = "8.0.0"
PY_ECC_IMPLEMENTATION = "py_ecc_low_level_rfc9380"
QUICKNET_DST = b"BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_"

SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
GIT_OBJECT_RE = re.compile(r"[0-9a-f]{40}\Z")
HEX_RE = re.compile(r"[0-9a-f]+\Z")
OSF_ID_RE = re.compile(r"[a-z0-9]{5}\Z")
RFC3339_UTC_RE = re.compile(
    r"(?P<year>[0-9]{4})-(?P<month>[0-9]{2})-(?P<day>[0-9]{2})"
    r"T(?P<hour>[0-9]{2}):(?P<minute>[0-9]{2}):(?P<second>[0-9]{2})"
    r"(?:\.(?P<fraction>[0-9]+))?Z\Z"
)

CODE_FILE_PATHS = {
    "trace_generator": "scripts/generate_controlled_queue_prospective_trace.py",
    "trace_verifier": "scripts/verify_controlled_queue_prospective_trace.py",
    "receipt_generator": "scripts/generate_controlled_queue_prospective_receipt.py",
    "receipt_verifier": "scripts/verify_controlled_queue_prospective_receipt.py",
}
CODE_FILE_ROLES = tuple(CODE_FILE_PATHS)

FRESH_OUTPUT_PATHS = (
    TRACE_OUTPUT_PATH,
    COUNTS_OUTPUT_PATH,
    MANIFEST_OUTPUT_PATH,
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1.json",
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1-manifest.json",
    "FormalSLT/Applications/ControlledQueueProspectiveStructuredOPEData.lean",
)

NONCLAIMS = (
    "not a numerical endpoint or confidence certificate",
    "not proof that the named path belongs to a theorem-produced good event",
    "not Lean verification of the beacon signature or raw trace bytes",
)


class ProspectiveTraceError(ValueError):
    """Raised when any prospective generation precondition fails."""


def _fail(message: str) -> NoReturn:
    raise ProspectiveTraceError(message)


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
    """Strictly decode UTF-8 JSON while rejecting duplicate/float constants."""

    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProspectiveTraceError(f"invalid UTF-8 JSON in {where}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rational_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


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


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    if set(value) != expected:
        _fail(
            f"{where} keys mismatch; missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )


def _exact(actual: Any, expected: Any, where: str) -> None:
    scalar = isinstance(expected, (bool, int, str)) or expected is None
    if actual != expected or (scalar and type(actual) is not type(expected)):
        _fail(f"{where} must be {expected!r}, got {actual!r}")


def _fraction(value: Any, where: str) -> Fraction:
    text = _string(value, where)
    try:
        result = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise ProspectiveTraceError(f"invalid rational at {where}: {text!r}") from error
    if rational_text(result) != text:
        _fail(f"{where} must be a canonical rational string, got {text!r}")
    return result


def _lower_hex(value: Any, byte_length: int, where: str) -> str:
    text = _string(value, where)
    if HEX_RE.fullmatch(text) is None or len(text) != 2 * byte_length:
        _fail(f"{where} must be lowercase hex encoding {byte_length} bytes")
    return text


def _sha256(value: Any, where: str) -> str:
    text = _string(value, where)
    if SHA256_RE.fullmatch(text) is None:
        _fail(f"{where} must be a lowercase SHA-256 digest")
    return text


def _git_object(value: Any, where: str) -> str:
    text = _string(value, where)
    if GIT_OBJECT_RE.fullmatch(text) is None:
        _fail(f"{where} must be a lowercase 40-digit Git object id")
    return text


def _reject_booleans(value: Any, where: str) -> None:
    if isinstance(value, bool):
        _fail(f"JSON booleans are forbidden at {where}")
    if isinstance(value, dict):
        for key, item in value.items():
            _reject_booleans(item, f"{where}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _reject_booleans(item, f"{where}[{index}]")


def _display(path: Path, *, root: Path = ROOT) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(root.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def _path_identity(path: Path) -> str:
    return unicodedata.normalize("NFC", path.absolute().as_posix()).casefold()


def _same_file_target(left: Path, right: Path) -> bool:
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


def _require_exact_path(path: Path, expected: Path, where: str) -> None:
    actual_text = unicodedata.normalize("NFC", path.absolute().as_posix())
    expected_text = unicodedata.normalize("NFC", expected.absolute().as_posix())
    if actual_text != expected_text:
        _fail(
            f"{where} must be the frozen repository path {_display(expected)}, "
            f"got {_display(path)}"
        )
    if _has_symlink_component(path):
        _fail(f"{where} path contains a symbolic-link component: {path}")


def _read(path: Path, where: str) -> bytes:
    try:
        return path.read_bytes()
    except OSError as error:
        raise ProspectiveTraceError(f"cannot read {where} at {_display(path)}: {error}") from error


def _canonical_object(raw: bytes, where: str) -> dict[str, Any]:
    value = _object(parse_json_bytes(raw, where), where)
    if raw != canonical_json_bytes(value):
        _fail(f"{where} must use canonical JSON bytes")
    return value


def _validate_artifact_paths(
    inputs: dict[str, Path],
    outputs: dict[str, Path],
    *,
    protected: dict[str, Path] | None = None,
) -> None:
    protected_paths = {**inputs, **(protected or {})}
    for role, path in protected_paths.items():
        if _has_symlink_component(path):
            _fail(f"protected path {role} contains a symbolic-link component: {path}")
    for role, path in outputs.items():
        if _has_symlink_component(path):
            _fail(f"output path {role} contains a symbolic-link component: {path}")

    input_items = list(inputs.items())
    input_aliases = [
        (left_role, right_role)
        for index, (left_role, left_path) in enumerate(input_items)
        for right_role, right_path in input_items[index + 1 :]
        if _same_file_target(left_path, right_path)
    ]
    if input_aliases:
        _fail(f"input paths must be distinct; aliases={input_aliases}")

    output_items = list(outputs.items())
    output_aliases = [
        (left_role, right_role)
        for index, (left_role, left_path) in enumerate(output_items)
        for right_role, right_path in output_items[index + 1 :]
        if _same_file_target(left_path, right_path)
    ]
    if output_aliases:
        _fail(f"output paths must be distinct; aliases={output_aliases}")

    collisions = [
        f"{output_role}={_display(output_path)} aliases {protected_role}"
        for output_role, output_path in outputs.items()
        for protected_role, protected_path in protected_paths.items()
        if _same_file_target(output_path, protected_path)
    ]
    if collisions:
        _fail("output path aliases protected input: " + "; ".join(collisions))


def parse_registration_time(value: Any) -> tuple[str, int]:
    """Return the exact RFC3339-Z text and its ceiling Unix second."""

    text = _string(value, "OSF data.attributes.date_registered")
    match = RFC3339_UTC_RE.fullmatch(text)
    if match is None:
        _fail("OSF date_registered must be RFC3339 UTC ending in Z")
    fields = {key: int(match.group(key)) for key in (
        "year",
        "month",
        "day",
        "hour",
        "minute",
        "second",
    )}
    try:
        instant = datetime(**fields, tzinfo=timezone.utc)
    except ValueError as error:
        raise ProspectiveTraceError(f"invalid OSF date_registered: {error}") from error
    base_second = calendar.timegm(instant.utctimetuple())
    fraction = match.group("fraction")
    ceiling = base_second + int(fraction is not None and any(ch != "0" for ch in fraction))
    return text, ceiling


def formula_selected_round(registration_second: int) -> int:
    registration_second = _integer(
        registration_second, "registration Unix second", minimum=0
    )
    numerator = registration_second + REGISTRATION_DELAY_SECONDS - QUICKNET_GENESIS
    round_number = 1 + (-(-numerator // QUICKNET_PERIOD))
    if round_number < 1:
        _fail("formula-selected quicknet round must be positive")
    round_time = QUICKNET_GENESIS + (round_number - 1) * QUICKNET_PERIOD
    target = registration_second + REGISTRATION_DELAY_SECONDS
    if round_time < target or round_time - QUICKNET_PERIOD >= target:
        raise AssertionError("quicknet round formula failed its first-eligible invariant")
    return round_number


def quicknet_round_time(round_number: int) -> int:
    number = _integer(round_number, "quicknet round", minimum=1)
    return QUICKNET_GENESIS + (number - 1) * QUICKNET_PERIOD


def derive_seed(round_number: int, signature: bytes) -> bytes:
    number = _integer(round_number, "quicknet round", minimum=1)
    if len(signature) != 48:
        _fail("quicknet signature must contain exactly 48 bytes")
    return hashlib.sha256(
        PRNG_DOMAIN.encode("utf-8")
        + b"\0"
        + bytes.fromhex(QUICKNET_CHAIN_HASH)
        + number.to_bytes(8, "big")
        + signature
    ).digest()


def _verify_quicknet_with_py_ecc(
    round_number: int, signature: bytes, public_key: bytes
) -> bool:
    """Verify quicknet's G1-signature/G2-public-key RFC9380 scheme."""

    try:
        installed_version = importlib.metadata.version(PY_ECC_DISTRIBUTION)
    except importlib.metadata.PackageNotFoundError as error:
        raise ProspectiveTraceError(
            f"{PY_ECC_DISTRIBUTION}=={PY_ECC_VERSION} is required for BLS verification"
        ) from error
    if installed_version != PY_ECC_VERSION:
        _fail(
            f"BLS verifier requires {PY_ECC_DISTRIBUTION}=={PY_ECC_VERSION}, "
            f"found {installed_version}"
        )
    try:
        from py_ecc.bls.g2_primitives import subgroup_check
        from py_ecc.bls.hash_to_curve import hash_to_G1
        from py_ecc.bls.point_compression import decompress_G1, decompress_G2
        from py_ecc.optimized_bls12_381 import G2, is_inf, pairing
    except ImportError as error:
        raise ProspectiveTraceError(
            f"failed to import pinned {PY_ECC_DISTRIBUTION} BLS primitives"
        ) from error

    try:
        signature_point = decompress_G1(int.from_bytes(signature, "big"))
        public_key_point = decompress_G2(
            (
                int.from_bytes(public_key[:48], "big"),
                int.from_bytes(public_key[48:], "big"),
            )
        )
        message = hashlib.sha256(round_number.to_bytes(8, "big")).digest()
        message_point = hash_to_G1(message, QUICKNET_DST, hashlib.sha256)
        if any(is_inf(point) for point in (signature_point, public_key_point, message_point)):
            return False
        if not all(
            subgroup_check(point)
            for point in (signature_point, public_key_point, message_point)
        ):
            return False
        return pairing(public_key_point, message_point) == pairing(G2, signature_point)
    except (AssertionError, TypeError, ValueError) as error:
        raise ProspectiveTraceError(f"invalid quicknet BLS encoding: {error}") from error


def verify_quicknet_signature(
    round_number: int,
    signature_hex: Any,
    public_key_hex: Any,
    *,
    backend: Callable[[int, bytes, bytes], bool] | None = None,
) -> dict[str, Any]:
    """Verify a quicknet signature and return the frozen audit descriptor."""

    number = _integer(round_number, "quicknet round", minimum=1)
    signature = bytes.fromhex(_lower_hex(signature_hex, 48, "quicknet signature"))
    public_key = bytes.fromhex(_lower_hex(public_key_hex, 96, "quicknet public key"))
    verifier = backend or _verify_quicknet_with_py_ecc
    try:
        valid = verifier(number, signature, public_key)
    except ProspectiveTraceError:
        raise
    except Exception as error:
        raise ProspectiveTraceError(f"quicknet BLS verification failed: {error}") from error
    if valid is not True:
        _fail("quicknet BLS signature is invalid")
    return {
        "dependency": PY_ECC_DISTRIBUTION,
        "dst": QUICKNET_DST.decode("ascii"),
        "implementation": PY_ECC_IMPLEMENTATION,
        "version": PY_ECC_VERSION,
    }


def parse_osf_registration(raw: bytes) -> dict[str, Any]:
    """Validate the archived public OSF registration API response."""

    response = _object(parse_json_bytes(raw, "OSF registration response"), "OSF response")
    data = _object(response.get("data"), "OSF response.data")
    registration_id = _string(data.get("id"), "OSF response.data.id")
    if OSF_ID_RE.fullmatch(registration_id) is None:
        _fail("OSF registration id must contain five lowercase letters or digits")
    _exact(data.get("type"), "registrations", "OSF response.data.type")
    attributes = _object(data.get("attributes"), "OSF response.data.attributes")
    if attributes.get("public") is not True:
        _fail("OSF registration must be public")
    if attributes.get("registration") is not True:
        _fail("OSF response must describe a completed registration")
    if attributes.get("withdrawn") is not False:
        _fail("OSF registration must not be withdrawn")
    date_registered, unix_second = parse_registration_time(
        attributes.get("date_registered")
    )
    return {
        "date_registered": date_registered,
        "id": registration_id,
        "unix_seconds_ceiling": unix_second,
    }


def parse_osf_binding_file_metadata(
    raw: bytes, registration_id: str, binding_raw: bytes
) -> dict[str, Any]:
    """Prove that the exact binding bytes are a file of the registration."""

    response = _object(
        parse_json_bytes(raw, "OSF binding-file metadata response"),
        "OSF binding-file metadata response",
    )
    data = _object(response.get("data"), "OSF binding-file metadata response.data")
    _exact(data.get("type"), "files", "OSF binding-file metadata data.type")
    file_id = _string(data.get("id"), "OSF binding-file metadata data.id")
    if not file_id:
        _fail("OSF binding-file metadata data.id must be nonempty")
    attributes = _object(
        data.get("attributes"), "OSF binding-file metadata data.attributes"
    )
    _exact(
        attributes.get("kind"),
        "file",
        "OSF binding-file metadata attributes.kind",
    )
    _exact(
        _integer(
            attributes.get("current_version"),
            "OSF binding-file metadata attributes.current_version",
            minimum=1,
        ),
        1,
        "OSF binding-file metadata attributes.current_version",
    )
    _exact(
        attributes.get("name"),
        "code-freeze-binding-v1.json",
        "OSF binding-file metadata attributes.name",
    )
    materialized_path = _string(
        attributes.get("materialized_path"),
        "OSF binding-file metadata attributes.materialized_path",
    )
    raw_segments = materialized_path.split("/")
    if (
        not materialized_path.startswith("/")
        or materialized_path.startswith("//")
        or materialized_path.endswith("/")
        or any(segment in {"", ".", ".."} for segment in raw_segments[1:])
        or PurePosixPath(materialized_path).as_posix() != materialized_path
        or unicodedata.normalize("NFC", materialized_path) != materialized_path
    ):
        _fail(
            "OSF binding-file metadata attributes.materialized_path must be an "
            "absolute canonical POSIX path without dot segments"
        )
    _exact(
        PurePosixPath(materialized_path).name,
        "code-freeze-binding-v1.json",
        "OSF binding-file metadata materialized filename",
    )
    _exact(
        _integer(
            attributes.get("size"),
            "OSF binding-file metadata attributes.size",
            minimum=1,
        ),
        len(binding_raw),
        "OSF binding-file metadata attributes.size",
    )
    extra = _object(
        attributes.get("extra"), "OSF binding-file metadata attributes.extra"
    )
    hashes = _object(
        extra.get("hashes"), "OSF binding-file metadata attributes.extra.hashes"
    )
    _exact(
        _sha256(
            hashes.get("sha256"),
            "OSF binding-file metadata attributes.extra.hashes.sha256",
        ),
        sha256_bytes(binding_raw),
        "OSF binding-file metadata binding SHA-256",
    )
    relationships = _object(
        data.get("relationships"), "OSF binding-file metadata data.relationships"
    )
    if "node" in relationships:
        node = _object(
            relationships["node"],
            "OSF binding-file metadata data.relationships.node",
        )
        node_data = _object(
            node.get("data"),
            "OSF binding-file metadata data.relationships.node.data",
        )
        _exact(
            node_data.get("id"),
            registration_id,
            "OSF binding-file metadata node id",
        )
        _string(
            node_data.get("type"),
            "OSF binding-file metadata node type",
        )
    target = _object(
        relationships.get("target"),
        "OSF binding-file metadata data.relationships.target",
    )
    target_data = _object(
        target.get("data"),
        "OSF binding-file metadata data.relationships.target.data",
    )
    _keys(
        target_data,
        {"id", "type"},
        "OSF binding-file metadata data.relationships.target.data",
    )
    _exact(
        target_data["id"], registration_id, "OSF binding-file metadata target id"
    )
    _exact(
        target_data["type"],
        "registrations",
        "OSF binding-file metadata target type",
    )
    target_links = _object(
        target.get("links"),
        "OSF binding-file metadata data.relationships.target.links",
    )
    related = _object(
        target_links.get("related"),
        "OSF binding-file metadata data.relationships.target.links.related",
    )
    _exact(
        related.get("href"),
        f"https://api.osf.io/v2/registrations/{registration_id}/",
        "OSF binding-file metadata target related href",
    )
    return {
        "current_version": 1,
        "file_id": file_id,
        "kind": "file",
        "materialized_path": materialized_path,
        "name": attributes["name"],
        "sha256": sha256_bytes(binding_raw),
        "size": len(binding_raw),
    }


def parse_quicknet_chain_info(raw: bytes) -> dict[str, Any]:
    value = _object(parse_json_bytes(raw, "quicknet chain info"), "quicknet chain info")
    _keys(
        value,
        {
            "beacon_id",
            "chain_hash",
            "genesis_seed",
            "genesis_time",
            "period",
            "public_key",
            "scheme",
        },
        "quicknet chain info",
    )
    expected = {
        "beacon_id": QUICKNET_BEACON_ID,
        "chain_hash": QUICKNET_CHAIN_HASH,
        "genesis_seed": QUICKNET_GROUP_HASH,
        "genesis_time": QUICKNET_GENESIS,
        "period": QUICKNET_PERIOD,
        "public_key": QUICKNET_PUBLIC_KEY,
        "scheme": QUICKNET_SCHEME,
    }
    for key, expected_value in expected.items():
        _exact(value[key], expected_value, f"quicknet chain info.{key}")
    _lower_hex(value["public_key"], 96, "quicknet chain info.public_key")
    _lower_hex(value["chain_hash"], 32, "quicknet chain info.chain_hash")
    _lower_hex(value["genesis_seed"], 32, "quicknet chain info.genesis_seed")
    _integer(value["period"], "quicknet chain info.period", minimum=1)
    _integer(value["genesis_time"], "quicknet chain info.genesis_time", minimum=0)
    return value


def parse_quicknet_round(
    raw: bytes,
    expected_round: int,
    *,
    signature_backend: Callable[[int, bytes, bytes], bool] | None = None,
) -> tuple[dict[str, Any], dict[str, Any], bytes]:
    value = _object(parse_json_bytes(raw, "quicknet round response"), "quicknet round")
    _keys(value, {"randomness", "round", "signature"}, "quicknet round")
    round_number = _integer(value["round"], "quicknet round.round", minimum=1)
    _exact(round_number, expected_round, "formula-selected quicknet round")
    signature_hex = _lower_hex(value["signature"], 48, "quicknet round.signature")
    randomness = _lower_hex(value["randomness"], 32, "quicknet round.randomness")
    signature = bytes.fromhex(signature_hex)
    _exact(
        randomness,
        hashlib.sha256(signature).hexdigest(),
        "quicknet round.randomness",
    )
    verifier = verify_quicknet_signature(
        round_number,
        signature_hex,
        QUICKNET_PUBLIC_KEY,
        backend=signature_backend,
    )
    return value, verifier, signature


def load_protocol(path: Path) -> tuple[bytes, dict[str, Any]]:
    _require_exact_path(path, DEFAULT_PROTOCOL, "protocol path")
    raw = _read(path, "frozen protocol")
    spec = _canonical_object(raw, "frozen protocol")
    _exact(sha256_bytes(raw), EXPECTED_PROTOCOL_SHA256, "frozen protocol SHA-256")
    _exact(spec.get("schema_version"), PROTOCOL_SCHEMA, "protocol schema_version")
    _exact(spec.get("protocol_version"), PROTOCOL_VERSION, "protocol version")
    artifact = _object(spec.get("artifact_contract"), "protocol artifact_contract")
    _exact(
        artifact.get("trace_generator_path"),
        CODE_FILE_PATHS["trace_generator"],
        "protocol trace_generator_path",
    )
    _exact(
        artifact.get("trace_verifier_path"),
        CODE_FILE_PATHS["trace_verifier"],
        "protocol trace_verifier_path",
    )
    _exact(
        artifact.get("receipt_generator_path"),
        CODE_FILE_PATHS["receipt_generator"],
        "protocol receipt_generator_path",
    )
    _exact(
        artifact.get("receipt_verifier_path"),
        CODE_FILE_PATHS["receipt_verifier"],
        "protocol receipt_verifier_path",
    )
    _exact(tuple(artifact.get("fresh_output_paths", ())), FRESH_OUTPUT_PATHS, "fresh output paths")
    generation = _object(spec.get("data_generation"), "protocol data_generation")
    _exact(generation.get("horizon"), HORIZON, "protocol horizon")
    _exact(_fraction(generation.get("true_gamma"), "protocol true_gamma"), TRUE_GAMMA, "true gamma")
    _exact(
        _fraction(generation.get("true_hit_probability"), "protocol true_hit_probability"),
        TRUE_HIT_PROBABILITY,
        "true hit probability",
    )
    prng = _object(generation.get("prng_contract"), "protocol prng_contract")
    frozen_prng = {
        "beacon_chain_hash": QUICKNET_CHAIN_HASH,
        "beacon_group_hash": QUICKNET_GROUP_HASH,
        "beacon_public_key": QUICKNET_PUBLIC_KEY,
        "beacon_scheme_id": QUICKNET_SCHEME,
        "beacon_genesis_unix_seconds": QUICKNET_GENESIS,
        "beacon_period_seconds": QUICKNET_PERIOD,
        "domain_utf8": PRNG_DOMAIN,
        "version": PRNG_VERSION,
        "test_seed_hex": TEST_SEED_HEX,
        "test_counter_zero_digest_hex": TEST_COUNTER_ZERO_DIGEST_HEX,
    }
    for key, expected in frozen_prng.items():
        _exact(prng.get(key), expected, f"protocol prng_contract.{key}")
    sampling = _object(generation.get("sampling_contract"), "protocol sampling_contract")
    _exact(sampling.get("version"), SAMPLING_VERSION, "protocol sampling version")
    binary = _object(generation.get("binary_contract"), "protocol binary_contract")
    _exact(binary.get("version"), BINARY_VERSION, "protocol binary version")
    _exact(binary.get("magic_hex"), BINARY_MAGIC.hex(), "protocol binary magic")
    _exact(binary.get("expected_byte_length"), BINARY_EXPECTED_BYTES, "protocol binary bytes")
    return raw, spec


def _bound_model_files(
    protocol: dict[str, Any], paths: dict[str, Path]
) -> dict[str, tuple[Path, bytes, dict[str, Any]]]:
    bindings = _object(protocol.get("bindings"), "protocol bindings")
    expected_paths = {
        "model_input": MODEL_INPUT_PATH,
        "model_manifest": MODEL_MANIFEST_PATH,
        "model_tables": MODEL_TABLES_PATH,
    }
    result: dict[str, tuple[Path, bytes, dict[str, Any]]] = {}
    for role, path_text in expected_paths.items():
        row = _object(bindings.get(role), f"protocol bindings.{role}")
        _exact(row.get("path"), path_text, f"protocol bindings.{role}.path")
        digest = _sha256(row.get("sha256"), f"protocol bindings.{role}.sha256")
        path = paths[role]
        _require_exact_path(path, ROOT / path_text, f"{role} path")
        raw = _read(path, role)
        _exact(sha256_bytes(raw), digest, f"{role} SHA-256")
        value = _object(parse_json_bytes(raw, role), role)
        result[role] = (path, raw, value)

    model = result["model_input"][2]
    _exact(model.get("schema_version"), "controlled-queue-input-v1", "model schema")
    _exact(model.get("model_version"), "controlled-queue-v1", "model version")
    state_space = _object(model.get("state_space"), "model state_space")
    _exact(state_space.get("queue_capacity"), 7, "model queue capacity")
    _exact(state_space.get("regime_count"), 3, "model regime count")
    _exact(state_space.get("arrival_by_regime"), [0, 1, 2], "model arrivals")
    actions = _array(model.get("actions"), "model actions")
    _exact(actions, [{"id": "eco", "service_capacity": 1}, {"id": "boost", "service_capacity": 2}], "model actions")
    behavior = _object(model.get("behavior_policy"), "model behavior policy")
    _exact(behavior.get("id"), "behavior_uniform", "model behavior policy id")
    _exact(
        behavior.get("boost_probability_by_state"),
        ["1/2"] * STATE_COUNT,
        "model uniform behavior rows",
    )
    kernel = _object(model.get("kernel"), "model kernel")
    _exact(kernel.get("uniform_state_count"), STATE_COUNT, "model kernel state count")

    manifest = result["model_manifest"][2]
    rows = _array(manifest.get("files"), "model manifest files")
    by_role_path = {
        (row.get("role"), row.get("path")): row
        for row in (_object(item, "model manifest file") for item in rows)
    }
    for role, manifest_role in (("model_input", "input"), ("model_tables", "output")):
        path_text = expected_paths[role]
        row = _object(
            by_role_path.get((manifest_role, path_text)),
            f"model manifest row for {role}",
        )
        _exact(
            row.get("sha256"),
            sha256_bytes(result[role][1]),
            f"model manifest {role} SHA-256",
        )
    return result


def _code_rows_by_role(value: Any) -> dict[str, dict[str, Any]]:
    rows = _array(value, "OSF binding code_files")
    if len(rows) != len(CODE_FILE_ROLES):
        _fail("OSF binding code_files must contain exactly four rows")
    result: dict[str, dict[str, Any]] = {}
    for index, raw_row in enumerate(rows):
        row = _object(raw_row, f"OSF binding code_files[{index}]")
        _keys(row, {"bytes", "path", "role", "sha256"}, f"code_files[{index}]")
        role = _string(row["role"], f"code_files[{index}].role")
        if role in result:
            _fail(f"duplicate OSF binding code role: {role}")
        result[role] = row
    _exact(tuple(result), CODE_FILE_ROLES, "OSF binding code-file role order")
    return result


def _run_git(arguments: Sequence[str], *, root: Path = ROOT) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(root), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        _fail(f"Git verification failed for {' '.join(arguments)}: {detail}")
    return completed.stdout


def validate_osf_binding(
    raw: bytes,
    protocol_raw: bytes,
    *,
    root: Path = ROOT,
    git_runner: Callable[[Sequence[str]], bytes] | None = None,
) -> tuple[dict[str, Any], dict[str, tuple[Path, bytes]]]:
    binding = _canonical_object(raw, "OSF code-freeze binding")
    _reject_booleans(binding, "OSF code-freeze binding")
    _keys(
        binding,
        {
            "artifact_status",
            "code_files",
            "code_freeze",
            "protocol",
            "schema_version",
        },
        "OSF code-freeze binding",
    )
    _exact(binding["artifact_status"], BINDING_STATUS, "OSF binding artifact_status")
    _exact(binding["schema_version"], BINDING_SCHEMA, "OSF binding schema_version")

    protocol = _object(binding["protocol"], "OSF binding protocol")
    _keys(protocol, {"bytes", "commit", "path", "sha256", "tree"}, "OSF binding protocol")
    _exact(protocol["path"], PROTOCOL_PATH, "OSF binding protocol.path")
    _exact(_integer(protocol["bytes"], "OSF binding protocol.bytes", minimum=1), len(protocol_raw), "OSF binding protocol.bytes")
    _exact(_sha256(protocol["sha256"], "OSF binding protocol.sha256"), sha256_bytes(protocol_raw), "OSF binding protocol.sha256")
    protocol_commit = _git_object(protocol["commit"], "OSF binding protocol.commit")
    protocol_tree = _git_object(protocol["tree"], "OSF binding protocol.tree")
    _exact(
        protocol_commit,
        EXPECTED_PROTOCOL_COMMIT,
        "OSF binding protocol.commit",
    )
    _exact(protocol_tree, EXPECTED_PROTOCOL_TREE, "OSF binding protocol.tree")

    freeze = _object(binding["code_freeze"], "OSF binding code_freeze")
    _keys(freeze, {"commit", "tree"}, "OSF binding code_freeze")
    freeze_commit = _git_object(freeze["commit"], "OSF binding code_freeze.commit")
    freeze_tree = _git_object(freeze["tree"], "OSF binding code_freeze.tree")
    if freeze_commit == protocol_commit:
        _fail("code-freeze commit must be later than the protocol commit")

    code_rows = _code_rows_by_role(binding["code_files"])
    code_files: dict[str, tuple[Path, bytes]] = {}
    for role in CODE_FILE_ROLES:
        row = code_rows[role]
        _exact(row["path"], CODE_FILE_PATHS[role], f"code_files.{role}.path")
        path = (root / CODE_FILE_PATHS[role]).resolve()
        try:
            path.relative_to(root.resolve())
        except ValueError as error:
            raise ProspectiveTraceError(f"code_files.{role}.path escapes repository") from error
        file_raw = _read(path, f"code file {role}")
        _exact(_integer(row["bytes"], f"code_files.{role}.bytes", minimum=1), len(file_raw), f"code_files.{role}.bytes")
        _exact(_sha256(row["sha256"], f"code_files.{role}.sha256"), sha256_bytes(file_raw), f"code_files.{role}.sha256")
        code_files[role] = (path, file_raw)

    run = git_runner or (lambda args: _run_git(args, root=root))
    _exact(run(("cat-file", "-t", protocol_commit)).strip(), b"commit", "protocol Git object type")
    _exact(run(("show", "-s", "--format=%T", protocol_commit)).decode().strip(), protocol_tree, "protocol Git tree")
    _exact(run(("show", f"{protocol_commit}:{PROTOCOL_PATH}")), protocol_raw, "protocol bytes in protocol commit")
    _exact(run(("cat-file", "-t", freeze_commit)).strip(), b"commit", "code-freeze Git object type")
    _exact(run(("show", "-s", "--format=%T", freeze_commit)).decode().strip(), freeze_tree, "code-freeze Git tree")
    run(("merge-base", "--is-ancestor", protocol_commit, freeze_commit))
    for role, (_path, file_raw) in code_files.items():
        _exact(
            run(("show", f"{freeze_commit}:{CODE_FILE_PATHS[role]}")),
            file_raw,
            f"{role} bytes in code-freeze commit",
        )
    return binding, code_files


class CounterStream:
    """Versioned SHA-256 counter stream from the frozen protocol."""

    def __init__(self, seed: bytes, counter_start: int = 0) -> None:
        if len(seed) != 32:
            raise ValueError("counter-stream seed must contain 32 bytes")
        if not 0 <= counter_start < UINT64_SPACE:
            raise ValueError("counter_start must fit unsigned 64-bit")
        self._prefix = PRNG_DOMAIN.encode("utf-8") + b"\0" + seed
        self._counter = counter_start
        self._buffer = b""
        self.words_consumed = 0
        self.digest_blocks_generated = 0
        self.rejections_by_modulus: dict[int, int] = {}

    def _refill(self) -> None:
        if self._counter >= UINT64_SPACE:
            raise OverflowError("SHA-256 counter stream exhausted")
        self._buffer += hashlib.sha256(
            self._prefix + self._counter.to_bytes(8, "big")
        ).digest()
        self._counter += 1
        self.digest_blocks_generated += 1

    def next_u64(self) -> int:
        while len(self._buffer) < 8:
            self._refill()
        word = int.from_bytes(self._buffer[:8], "big")
        self._buffer = self._buffer[8:]
        self.words_consumed += 1
        return word

    def uniform_below(self, modulus: int) -> int:
        value, rejections = rejection_sample_u64(modulus, self.next_u64)
        if rejections:
            self.rejections_by_modulus[modulus] = (
                self.rejections_by_modulus.get(modulus, 0) + rejections
            )
        return value


def rejection_sample_u64(
    modulus: int, draw_word: Callable[[], int]
) -> tuple[int, int]:
    if isinstance(modulus, bool) or not isinstance(modulus, int):
        raise ValueError("modulus must be an integer")
    if not 1 <= modulus <= UINT64_SPACE:
        raise ValueError("modulus must lie in [1, 2^64]")
    limit = UINT64_SPACE - (UINT64_SPACE % modulus)
    rejections = 0
    while True:
        word = draw_word()
        if isinstance(word, bool) or not isinstance(word, int) or not 0 <= word < UINT64_SPACE:
            raise ValueError("draw_word returned a value outside unsigned 64-bit range")
        if word < limit:
            return word % modulus, rejections
        rejections += 1


def integer_weights(probabilities: Sequence[Fraction]) -> list[int]:
    if not probabilities or any(value < 0 for value in probabilities):
        raise ValueError("categorical probabilities must be nonempty and nonnegative")
    if sum(probabilities) != 1:
        raise ValueError("categorical probabilities must sum exactly to one")
    denominator = math.lcm(*(value.denominator for value in probabilities))
    weights = [
        value.numerator * (denominator // value.denominator)
        for value in probabilities
    ]
    common = math.gcd(*weights)
    return [weight // common for weight in weights]


def sample_from_weights(weights: Sequence[int], stream: CounterStream) -> int:
    if not weights or any(isinstance(weight, bool) or weight < 0 for weight in weights):
        raise ValueError("categorical weights must be nonempty nonnegative integers")
    total = sum(weights)
    if total <= 0:
        raise ValueError("categorical weights must have positive total")
    draw = stream.uniform_below(total)
    cumulative = 0
    for index, weight in enumerate(weights):
        cumulative += weight
        if draw < cumulative:
            return index
    raise AssertionError("categorical draw escaped cumulative intervals")


def queue_step(model: dict[str, Any], source: int, action: int) -> int:
    state_space = model["state_space"]
    regime_count = state_space["regime_count"]
    queue, regime = divmod(source, regime_count)
    service = model["actions"][action]["service_capacity"]
    arrival = state_space["arrival_by_regime"][regime]
    next_queue = min(
        state_space["queue_capacity"], max(0, queue - service) + arrival
    )
    return regime_count * next_queue + ((regime + 1) % regime_count)


def _true_kernel_weights(model: dict[str, Any]) -> list[list[list[int]]]:
    base = (1 - TRUE_GAMMA) / STATE_COUNT
    rows: list[list[list[int]]] = []
    for state in range(STATE_COUNT):
        action_rows: list[list[int]] = []
        for action in range(ACTION_COUNT):
            step = queue_step(model, state, action)
            probabilities = [
                base + (TRUE_GAMMA if destination == step else 0)
                for destination in range(STATE_COUNT)
            ]
            weights = integer_weights(probabilities)
            if weights[step] != 1209 or any(
                weight != 17 for index, weight in enumerate(weights) if index != step
            ):
                raise AssertionError("true refresh-family integer weights drifted")
            action_rows.append(weights)
        rows.append(action_rows)
    return rows


def generate_trace_bytes_and_counts(
    model: dict[str, Any], seed: bytes, *, horizon: int = HORIZON
) -> tuple[bytes, dict[str, Any]]:
    """Pure deterministic path generation with no score or endpoint logic."""

    if isinstance(horizon, bool) or not isinstance(horizon, int) or horizon < 1:
        raise ValueError("horizon must be a positive integer")
    stream = CounterStream(seed)
    behavior_weights = [
        integer_weights([1 - Fraction(value), Fraction(value)])
        for value in model["behavior_policy"]["boost_probability_by_state"]
    ]
    kernel_weights = _true_kernel_weights(model)

    states = bytearray([INITIAL_STATE])
    actions = bytearray([INITIAL_ACTION])
    source_visits = [0] * STATE_COUNT
    destination_counts = [0] * STATE_COUNT
    transition_action_counts = [0] * ACTION_COUNT
    state_action_counts = [[0] * ACTION_COUNT for _state in range(STATE_COUNT)]
    edge_counts = [
        [[0] * STATE_COUNT for _action in range(ACTION_COUNT)]
        for _state in range(STATE_COUNT)
    ]
    persistence_hit_count = 0
    state = INITIAL_STATE

    for _time in range(horizon):
        action = sample_from_weights(behavior_weights[state], stream)
        deterministic_step = queue_step(model, state, action)
        destination = sample_from_weights(kernel_weights[state][action], stream)
        persistence_hit_count += int(destination == deterministic_step)

        actions.append(action)
        states.append(destination)
        source_visits[state] += 1
        destination_counts[destination] += 1
        transition_action_counts[action] += 1
        state_action_counts[state][action] += 1
        edge_counts[state][action][destination] += 1
        state = destination

    trace_bytes = b"".join(
        (
            BINARY_HEADER.pack(
                BINARY_MAGIC,
                horizon,
                len(states),
                len(actions),
            ),
            bytes(states),
            bytes(actions),
        )
    )
    expected_length = BINARY_HEADER.size + 2 * (horizon + 1)
    if len(trace_bytes) != expected_length:
        raise AssertionError("prospective binary length invariant failed")
    if horizon == HORIZON and len(trace_bytes) != BINARY_EXPECTED_BYTES:
        raise AssertionError("frozen prospective binary byte length drifted")

    counts = {
        "artifact_status": ARTIFACT_STATUS,
        "counts": {
            "destination_state_counts": destination_counts,
            "edge_counts": edge_counts,
            "persistence_hit_count": persistence_hit_count,
            "persistence_miss_count": horizon - persistence_hit_count,
            "source_state_visits": source_visits,
            "state_action_counts": state_action_counts,
            "transition_action_counts": transition_action_counts,
        },
        "final_action": actions[-1],
        "final_state": state,
        "generator_revision": GENERATOR_REVISION,
        "horizon": horizon,
        "initial_action": INITIAL_ACTION,
        "initial_state": INITIAL_STATE,
        "nonclaims": list(NONCLAIMS),
        "prng_audit": {
            "bytes_consumed": stream.words_consumed * 8,
            "digest_blocks_generated": stream.digest_blocks_generated,
            "rejections_by_modulus": {
                str(modulus): count
                for modulus, count in sorted(stream.rejections_by_modulus.items())
            },
            "version": PRNG_VERSION,
            "words_consumed": stream.words_consumed,
        },
        "schema_version": COUNTS_SCHEMA,
        "trace_sha256": sha256_bytes(trace_bytes),
        "trace_version": TRACE_VERSION,
    }
    return trace_bytes, counts


def _manifest_row(role: str, path: Path, raw: bytes) -> dict[str, Any]:
    return {
        "bytes": len(raw),
        "path": _display(path),
        "role": role,
        "sha256": sha256_bytes(raw),
    }


def build_manifest(
    *,
    registration: dict[str, Any],
    registration_raw: bytes,
    binding: dict[str, Any],
    binding_raw: bytes,
    binding_file_metadata_raw: bytes,
    chain_raw: bytes,
    round_value: dict[str, Any],
    round_raw: bytes,
    verification: dict[str, Any],
    seed: bytes,
    input_files: dict[str, tuple[Path, bytes]],
    code_files: dict[str, tuple[Path, bytes]],
    trace_path: Path,
    trace_raw: bytes,
    counts_path: Path,
    counts_raw: bytes,
) -> dict[str, Any]:
    code_rows = [
        _manifest_row(role, *code_files[role]) for role in CODE_FILE_ROLES
    ]
    generator = dict(code_rows[0])
    generator.pop("role")
    generator["revision"] = GENERATOR_REVISION
    independent_verifier = dict(code_rows[1])
    independent_verifier.pop("role")
    signature = bytes.fromhex(round_value["signature"])
    freeze = binding["code_freeze"]
    protocol_binding = binding["protocol"]
    return {
        "artifact_status": ARTIFACT_STATUS,
        "beacon": {
            "chain_hash": QUICKNET_CHAIN_HASH,
            "derived_seed_sha256": sha256_bytes(seed),
            "group_hash": QUICKNET_GROUP_HASH,
            "randomness": round_value["randomness"],
            "round": round_value["round"],
            "round_time_unix_seconds": quicknet_round_time(round_value["round"]),
            "scheme_id": QUICKNET_SCHEME,
            "signature_sha256": sha256_bytes(signature),
            "signature_verified": True,
            "signature_verifier": verification,
        },
        "code_freeze": {
            "code_files": code_rows,
            "commit": freeze["commit"],
            "tree": freeze["tree"],
        },
        "generator": generator,
        "independent_verifier": independent_verifier,
        "inputs": [
            _manifest_row(role, *input_files[role])
            for role in (
                "protocol",
                "osf_registration_response",
                "osf_registration_binding",
                "osf_registration_binding_file",
                "quicknet_chain_info",
                "quicknet_round",
                "model_input",
                "model_manifest",
                "model_tables",
            )
        ],
        "manifest_note": "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "nonclaims": list(NONCLAIMS),
        "outputs": [
            _manifest_row("trace_binary", trace_path, trace_raw),
            _manifest_row("trace_counts", counts_path, counts_raw),
        ],
        "parameters": {
            "action_count": ACTION_COUNT,
            "behavior_policy": "behavior_uniform",
            "binary_expected_bytes": BINARY_EXPECTED_BYTES,
            "binary_magic_hex": BINARY_MAGIC.hex(),
            "binary_version": BINARY_VERSION,
            "family": "refreshEnvironment",
            "horizon": HORIZON,
            "initial_action": INITIAL_ACTION,
            "initial_state": INITIAL_STATE,
            "prng_version": PRNG_VERSION,
            "sampling_version": SAMPLING_VERSION,
            "state_count": STATE_COUNT,
            "true_gamma": rational_text(TRUE_GAMMA),
        },
        "registration": {
            "api_response_sha256": sha256_bytes(registration_raw),
            "binding_file_api_response_sha256": sha256_bytes(
                binding_file_metadata_raw
            ),
            "binding_sha256": sha256_bytes(binding_raw),
            "date_registered": registration["date_registered"],
            "id": registration["id"],
            "protocol_commit": protocol_binding["commit"],
            "protocol_tree": protocol_binding["tree"],
            "unix_seconds_ceiling": registration["unix_seconds_ceiling"],
        },
        "schema_version": MANIFEST_SCHEMA,
        "trace_version": TRACE_VERSION,
    }


def expected_artifacts(
    *,
    protocol_path: Path,
    osf_registration_path: Path,
    osf_binding_path: Path,
    osf_binding_file_path: Path,
    chain_info_path: Path,
    round_path: Path,
    model_input_path: Path,
    model_manifest_path: Path,
    model_tables_path: Path,
    trace_path: Path,
    counts_path: Path,
    signature_backend: Callable[[int, bytes, bytes], bool] | None = None,
) -> tuple[bytes, bytes, bytes]:
    protocol_raw, protocol = load_protocol(protocol_path)
    model_files = _bound_model_files(
        protocol,
        {
            "model_input": model_input_path,
            "model_manifest": model_manifest_path,
            "model_tables": model_tables_path,
        },
    )
    registration_raw = _read(osf_registration_path, "OSF registration response")
    registration = parse_osf_registration(registration_raw)
    binding_raw = _read(osf_binding_path, "OSF code-freeze binding")
    binding, code_files = validate_osf_binding(binding_raw, protocol_raw)
    binding_file_metadata_raw = _read(
        osf_binding_file_path, "OSF binding-file metadata response"
    )
    parse_osf_binding_file_metadata(
        binding_file_metadata_raw, registration["id"], binding_raw
    )
    chain_raw = _read(chain_info_path, "quicknet chain info")
    parse_quicknet_chain_info(chain_raw)
    expected_round = formula_selected_round(registration["unix_seconds_ceiling"])
    round_raw = _read(round_path, "quicknet round response")
    round_value, verification, signature = parse_quicknet_round(
        round_raw,
        expected_round,
        signature_backend=signature_backend,
    )
    seed = derive_seed(expected_round, signature)
    trace_raw, counts = generate_trace_bytes_and_counts(
        model_files["model_input"][2], seed
    )
    counts_raw = canonical_json_bytes(counts)
    inputs = {
        "protocol": (protocol_path, protocol_raw),
        "osf_registration_response": (osf_registration_path, registration_raw),
        "osf_registration_binding": (osf_binding_path, binding_raw),
        "osf_registration_binding_file": (
            osf_binding_file_path,
            binding_file_metadata_raw,
        ),
        "quicknet_chain_info": (chain_info_path, chain_raw),
        "quicknet_round": (round_path, round_raw),
        **{
            role: (path, raw)
            for role, (path, raw, _value) in model_files.items()
        },
    }
    manifest = build_manifest(
        registration=registration,
        registration_raw=registration_raw,
        binding=binding,
        binding_raw=binding_raw,
        binding_file_metadata_raw=binding_file_metadata_raw,
        chain_raw=chain_raw,
        round_value=round_value,
        round_raw=round_raw,
        verification=verification,
        seed=seed,
        input_files=inputs,
        code_files=code_files,
        trace_path=trace_path,
        trace_raw=trace_raw,
        counts_path=counts_path,
        counts_raw=counts_raw,
    )
    return trace_raw, counts_raw, canonical_json_bytes(manifest)


def _write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if _has_symlink_component(path):
        _fail(f"output path contains a symbolic-link component: {path}")
    parent_flags = os.O_RDONLY
    parent_flags |= getattr(os, "O_DIRECTORY", 0)
    parent_flags |= getattr(os, "O_NOFOLLOW", 0)
    parent_descriptor = os.open(path.parent, parent_flags)
    temporary: Path | None = None
    try:
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{path.name}.", dir=path.parent
        )
        temporary = Path(temporary_name)
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        if _has_symlink_component(path):
            _fail(f"output path contains a symbolic-link component: {path}")
        try:
            os.link(
                temporary,
                path.name,
                dst_dir_fd=parent_descriptor,
                follow_symlinks=False,
            )
        except FileExistsError as error:
            raise ProspectiveTraceError(
                f"refusing to overwrite existing artifact: {path}"
            ) from error
        os.fsync(parent_descriptor)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()
        os.close(parent_descriptor)


def write_artifacts_manifest_last(
    trace_path: Path,
    trace_raw: bytes,
    counts_path: Path,
    counts_raw: bytes,
    manifest_path: Path,
    manifest_raw: bytes,
    *,
    writer: Callable[[Path, bytes], None] = _write_atomic,
) -> None:
    writer(trace_path, trace_raw)
    writer(counts_path, counts_raw)
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
    parser.add_argument(
        "--osf-registration", type=Path, default=DEFAULT_OSF_REGISTRATION
    )
    parser.add_argument("--osf-binding", type=Path, default=DEFAULT_OSF_BINDING)
    parser.add_argument(
        "--osf-binding-file", type=Path, default=DEFAULT_OSF_BINDING_FILE
    )
    parser.add_argument(
        "--quicknet-chain-info", type=Path, default=DEFAULT_QUICKNET_CHAIN_INFO
    )
    parser.add_argument("--quicknet-round", type=Path, default=DEFAULT_QUICKNET_ROUND)
    parser.add_argument("--model-input", type=Path, default=DEFAULT_MODEL_INPUT)
    parser.add_argument("--model-manifest", type=Path, default=DEFAULT_MODEL_MANIFEST)
    parser.add_argument("--model-tables", type=Path, default=DEFAULT_MODEL_TABLES)
    parser.add_argument("--trace-output", type=Path, default=DEFAULT_TRACE_OUTPUT)
    parser.add_argument("--counts-output", type=Path, default=DEFAULT_COUNTS_OUTPUT)
    parser.add_argument("--manifest-output", type=Path, default=DEFAULT_MANIFEST_OUTPUT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="read-only check for byte-identical generated artifacts",
    )
    return parser.parse_args(argv)


def _validate_cli_paths(args: argparse.Namespace) -> None:
    expected = {
        "protocol": DEFAULT_PROTOCOL,
        "osf_registration": DEFAULT_OSF_REGISTRATION,
        "osf_binding": DEFAULT_OSF_BINDING,
        "osf_binding_file": DEFAULT_OSF_BINDING_FILE,
        "quicknet_chain_info": DEFAULT_QUICKNET_CHAIN_INFO,
        "quicknet_round": DEFAULT_QUICKNET_ROUND,
        "model_input": DEFAULT_MODEL_INPUT,
        "model_manifest": DEFAULT_MODEL_MANIFEST,
        "model_tables": DEFAULT_MODEL_TABLES,
        "trace_output": DEFAULT_TRACE_OUTPUT,
        "counts_output": DEFAULT_COUNTS_OUTPUT,
        "manifest_output": DEFAULT_MANIFEST_OUTPUT,
    }
    for role, expected_path in expected.items():
        _require_exact_path(getattr(args, role), expected_path, role)
    inputs = {
        "protocol": args.protocol,
        "osf_registration_response": args.osf_registration,
        "osf_registration_binding": args.osf_binding,
        "osf_registration_binding_file": args.osf_binding_file,
        "quicknet_chain_info": args.quicknet_chain_info,
        "quicknet_round": args.quicknet_round,
        "model_input": args.model_input,
        "model_manifest": args.model_manifest,
        "model_tables": args.model_tables,
    }
    outputs = {
        "trace_binary": args.trace_output,
        "trace_counts": args.counts_output,
        "trace_manifest": args.manifest_output,
    }
    protected = {
        role: ROOT / path for role, path in CODE_FILE_PATHS.items()
    }
    _validate_artifact_paths(inputs, outputs, protected=protected)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        _validate_cli_paths(args)
        if not args.check:
            existing = [
                path_text
                for path_text in FRESH_OUTPUT_PATHS
                if (ROOT / path_text).exists() or (ROOT / path_text).is_symlink()
            ]
            if existing:
                _fail(
                    "single-run generation refuses existing prospective outputs: "
                    + ", ".join(existing)
                )
        trace_raw, counts_raw, manifest_raw = expected_artifacts(
            protocol_path=args.protocol,
            osf_registration_path=args.osf_registration,
            osf_binding_path=args.osf_binding,
            osf_binding_file_path=args.osf_binding_file,
            chain_info_path=args.quicknet_chain_info,
            round_path=args.quicknet_round,
            model_input_path=args.model_input,
            model_manifest_path=args.model_manifest,
            model_tables_path=args.model_tables,
            trace_path=args.trace_output,
            counts_path=args.counts_output,
        )
        if args.check:
            ok = all(
                (
                    _check_exact(args.trace_output, trace_raw),
                    _check_exact(args.counts_output, counts_raw),
                    _check_exact(args.manifest_output, manifest_raw),
                )
            )
            if ok:
                print("controlled-queue prospective trace artifacts are current")
                return 0
            return 1
        write_artifacts_manifest_last(
            args.trace_output,
            trace_raw,
            args.counts_output,
            counts_raw,
            args.manifest_output,
            manifest_raw,
        )
        print(
            "generated the single controlled-queue prospective trace, counts, "
            "and manifest"
        )
        return 0
    except (OSError, ProspectiveTraceError, ValueError) as error:
        print(f"controlled-queue prospective trace generation failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
