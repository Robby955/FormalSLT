#!/usr/bin/env python3
"""Independently verify the frozen prospective controlled-queue trace.

The verifier intentionally imports no project generator.  It validates the
frozen protocol and public provenance, verifies the quicknet BLS signature,
derives and replays the SHA-256 counter stream, decodes the complete binary
path, and reconstructs every stored count.  It is read-only: passing this
program establishes artifact integrity, not a statistical certificate or
membership of the observed path in a theorem-produced good event.
"""

from __future__ import annotations

import argparse
import calendar
import hashlib
import importlib.metadata
import json
import math
import re
import struct
import subprocess
import sys
import unicodedata
from datetime import datetime
from fractions import Fraction
from pathlib import Path, PurePosixPath
from typing import Any, NoReturn, Sequence


ROOT = Path(__file__).resolve().parents[1]
PROSPECTIVE = ROOT / "applications" / "controlled_queue" / "prospective"
EVIDENCE = PROSPECTIVE / "evidence"
GENERATED = PROSPECTIVE / "generated"

DEFAULT_PROTOCOL = (
    ROOT / "applications" / "controlled_queue" / "structured-ope-protocol-v1.json"
)
DEFAULT_OSF_RESPONSE = EVIDENCE / "osf-registration-v1.json"
DEFAULT_OSF_BINDING = EVIDENCE / "code-freeze-binding-v1.json"
DEFAULT_OSF_BINDING_FILE = EVIDENCE / "osf-code-freeze-binding-file-v1.json"
DEFAULT_CHAIN_INFO = EVIDENCE / "quicknet-chain-info-v1.json"
DEFAULT_ROUND_RESPONSE = EVIDENCE / "quicknet-round-v1.json"
DEFAULT_MODEL_INPUT = ROOT / "applications" / "controlled_queue" / "model-v1.json"
DEFAULT_MODEL_MANIFEST = (
    ROOT / "applications" / "controlled_queue" / "generated" / "model-v1-manifest.json"
)
DEFAULT_MODEL_TABLES = (
    ROOT / "applications" / "controlled_queue" / "generated" / "model-v1-tables.json"
)
DEFAULT_TRACE = GENERATED / "structured-ope-trace-v1.bin"
DEFAULT_COUNTS = GENERATED / "structured-ope-trace-v1-counts.json"
DEFAULT_MANIFEST = GENERATED / "structured-ope-trace-v1-manifest.json"

PROTOCOL_PATH = "applications/controlled_queue/structured-ope-protocol-v1.json"
PROTOCOL_SHA256 = "070519615ba7cdaf0198a72a03ab6f691a7ff9b37c2eaa97a363d7fd4c3bf153"
PROTOCOL_COMMIT = "65d8d56245e3862821fce09bcf30b017f03d2baa"
PROTOCOL_TREE = "8dbe01780fd2cec94b8b954f6ef1c8c210afee53"

TRACE_GENERATOR_PATH = "scripts/generate_controlled_queue_prospective_trace.py"
TRACE_VERIFIER_PATH = "scripts/verify_controlled_queue_prospective_trace.py"
RECEIPT_GENERATOR_PATH = "scripts/generate_controlled_queue_prospective_receipt.py"
RECEIPT_VERIFIER_PATH = "scripts/verify_controlled_queue_prospective_receipt.py"
TRACE_GENERATOR = ROOT / TRACE_GENERATOR_PATH
TRACE_VERIFIER = ROOT / TRACE_VERIFIER_PATH
RECEIPT_GENERATOR = ROOT / RECEIPT_GENERATOR_PATH
RECEIPT_VERIFIER = ROOT / RECEIPT_VERIFIER_PATH
CODE_FILES: tuple[tuple[str, str, Path], ...] = (
    ("trace_generator", TRACE_GENERATOR_PATH, TRACE_GENERATOR),
    ("trace_verifier", TRACE_VERIFIER_PATH, TRACE_VERIFIER),
    ("receipt_generator", RECEIPT_GENERATOR_PATH, RECEIPT_GENERATOR),
    ("receipt_verifier", RECEIPT_VERIFIER_PATH, RECEIPT_VERIFIER),
)

PROTOCOL_SCHEMA = "controlled-queue-structured-ope-preregistration-v1"
PROTOCOL_VERSION = "controlled-queue-structured-ope-protocol-v1"
BINDING_SCHEMA = "controlled-queue-prospective-code-freeze-binding-v1"
COUNTS_SCHEMA = "controlled-queue-prospective-trace-counts-v1"
MANIFEST_SCHEMA = "controlled-queue-prospective-trace-manifest-v1"
TRACE_VERSION = "controlled-queue-prospective-trace-v1"
GENERATOR_REVISION = "controlled-queue-prospective-trace-generator-v1"
ARTIFACT_STATUS = "PROSPECTIVE TRACE/PREPROCESSING ONLY - NO ENDPOINT"
BINDING_STATUS = "PUBLIC OSF CODE FREEZE BINDING"

HORIZON = 200_000
STATE_COUNT = 24
ACTION_COUNT = 2
INITIAL_STATE = 0
INITIAL_ACTION = 0
TRUE_GAMMA = Fraction(149, 200)
DOMAIN = "FormalSLT/controlled-queue/prospective-structured-ope-v1"
PRNG_VERSION = "sha256-counter-stream-v1"
SAMPLING_VERSION = "exact-categorical-u64-rejection-v1"
BINARY_VERSION = "controlled-queue-prospective-trace-binary-v1"
BINARY_MAGIC = b"FSLTCQSP1\n"
BINARY_EXPECTED_BYTES = 400_036
UINT64_SPACE = 1 << 64

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
BLS_DST = b"BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_"

NONCLAIMS = [
    "not a numerical endpoint or confidence certificate",
    "not proof that the named path belongs to a theorem-produced good event",
    "not Lean verification of the beacon signature or raw trace bytes",
]

SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
GIT_OID_RE = re.compile(r"[0-9a-f]{40}\Z")
RFC3339_UTC_RE = re.compile(
    r"(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(?:\.(\d+))?Z\Z"
)


class VerificationError(ValueError):
    """Raised when prospective evidence or replay violates the frozen contract."""


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


def _canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def _parse_controlled_json(raw: bytes, where: str) -> dict[str, Any]:
    value = _object(parse_json(raw, where), where)
    _exact(raw, _canonical_json(value), f"canonical {where} bytes")
    return value


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
        _fail(f"{where} must be an integer")
    if minimum is not None and value < minimum:
        _fail(f"{where} must be at least {minimum}")
    return value


def _boolean(value: Any, where: str) -> bool:
    if type(value) is not bool:
        _fail(f"{where} must be a boolean")
    return value


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected or type(actual) is not type(expected):
        _fail(f"{where} mismatch: expected {expected!r}, got {actual!r}")


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    _exact(set(value), expected, f"{where} keys")


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _digest(value: Any, where: str) -> str:
    result = _string(value, where)
    if SHA256_RE.fullmatch(result) is None:
        _fail(f"{where} must be a lowercase SHA-256 digest")
    return result


def _oid(value: Any, where: str) -> str:
    result = _string(value, where)
    if GIT_OID_RE.fullmatch(result) is None:
        _fail(f"{where} must be a lowercase 40-digit Git object id")
    return result


def _hex(value: Any, byte_length: int, where: str) -> bytes:
    text = _string(value, where)
    if re.fullmatch(r"[0-9a-f]+", text) is None:
        _fail(f"{where} must be lowercase hexadecimal")
    try:
        result = bytes.fromhex(text)
    except ValueError as error:
        raise VerificationError(f"invalid hexadecimal at {where}") from error
    if len(result) != byte_length:
        _fail(f"{where} must encode exactly {byte_length} bytes")
    return result


def _rational(value: Any, where: str) -> Fraction:
    text = _string(value, where)
    try:
        result = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError(f"invalid rational at {where}: {text!r}") from error
    canonical = str(result.numerator)
    if result.denominator != 1:
        canonical += f"/{result.denominator}"
    _exact(text, canonical, f"canonical {where}")
    return result


def _display(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def _path_identity(path: Path) -> str:
    return unicodedata.normalize("NFC", path.resolve().as_posix()).casefold()


def _verify_distinct_paths(paths: dict[str, Path]) -> None:
    rows = list(paths.items())
    identities: dict[str, str] = {}
    for role, path in rows:
        identity = _path_identity(path)
        if identity in identities:
            _fail(f"path roles {identities[identity]} and {role} alias each other")
        identities[identity] = role
    for index, (left_role, left) in enumerate(rows):
        for right_role, right in rows[index + 1 :]:
            try:
                aliases = left.exists() and right.exists() and left.samefile(right)
            except OSError as error:
                raise VerificationError(
                    f"cannot resolve path aliasing for {left_role}/{right_role}: {error}"
                ) from error
            if aliases:
                _fail(f"path roles {left_role} and {right_role} resolve to one file")


def _read(path: Path, where: str) -> bytes:
    try:
        return path.read_bytes()
    except OSError as error:
        raise VerificationError(f"cannot read {where} at {path}: {error}") from error


def _git(*arguments: str) -> bytes:
    """Run one exact, read-only Git object query without shell interpretation."""

    try:
        completed = subprocess.run(
            [
                "/usr/bin/git",
                "--no-replace-objects",
                "--no-lazy-fetch",
                "-C",
                str(ROOT),
                *arguments,
            ],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            env={
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_TERMINAL_PROMPT": "0",
                "LC_ALL": "C",
                "PATH": "/usr/bin:/bin",
            },
        )
    except OSError as error:
        raise VerificationError(f"cannot execute git object check: {error}") from error
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise VerificationError(f"git object check failed for {arguments!r}: {detail}")
    return completed.stdout


def _verify_git_tree(commit: str, expected_tree: str, where: str) -> None:
    _exact(_git("cat-file", "-t", commit).strip(), b"commit", f"{where} object type")
    try:
        actual = _git("rev-parse", "--verify", f"{commit}^{{tree}}").decode("ascii").strip()
    except UnicodeDecodeError as error:
        raise VerificationError(f"non-ASCII Git tree id for {where}") from error
    _exact(actual, expected_tree, f"{where} commit tree")


def _verify_git_ancestor(ancestor: str, descendant: str) -> None:
    _git("merge-base", "--is-ancestor", ancestor, descendant)


def _verify_git_file(
    commit: str,
    path_text: str,
    expected_raw: bytes,
    expected_hash: str,
    expected_bytes: int,
    where: str,
) -> None:
    committed = _git("show", f"{commit}:{path_text}")
    _exact(len(committed), expected_bytes, f"{where} committed byte length")
    _exact(_sha(committed), expected_hash, f"{where} committed SHA-256")
    _exact(committed, expected_raw, f"{where} current versus committed bytes")


def _file_row(value: Any, role: str, path: str, raw: bytes, where: str) -> dict[str, Any]:
    row = _object(value, where)
    _keys(row, {"role", "path", "bytes", "sha256"}, where)
    _exact(row["role"], role, f"{where}.role")
    _exact(row["path"], path, f"{where}.path")
    _exact(_integer(row["bytes"], f"{where}.bytes", minimum=0), len(raw), f"{where}.bytes")
    _exact(_digest(row["sha256"], f"{where}.sha256"), _sha(raw), f"{where}.sha256")
    return row


def _registration_second(value: Any) -> tuple[str, int]:
    text = _string(value, "OSF date_registered")
    match = RFC3339_UTC_RE.fullmatch(text)
    if match is None:
        _fail("OSF date_registered must be RFC3339 UTC ending in Z")
    year, month, day, hour, minute, second = map(int, match.groups()[:6])
    if second >= 60:
        _fail("OSF date_registered leap seconds are unsupported")
    try:
        parsed = datetime(year, month, day, hour, minute, second)
    except ValueError as error:
        raise VerificationError(f"invalid OSF date_registered: {error}") from error
    base = calendar.timegm(parsed.timetuple())
    fraction = match.group(7)
    return text, base + int(fraction is not None and any(ch != "0" for ch in fraction))


def _formula_round(registration_second: int) -> tuple[int, int]:
    numerator = registration_second + REGISTRATION_DELAY_SECONDS - GENESIS_SECONDS
    if numerator < 0:
        _fail("OSF registration precedes the frozen quicknet genesis window")
    round_number = 1 + (-(-numerator // PERIOD_SECONDS))
    round_time = GENESIS_SECONDS + (round_number - 1) * PERIOD_SECONDS
    target = registration_second + REGISTRATION_DELAY_SECONDS
    if round_time < target or round_time - PERIOD_SECONDS >= target:
        _fail("formula-selected quicknet round is not the first eligible round")
    return round_number, round_time


def _verify_quicknet_signature(round_number: int, signature: bytes, public_key: bytes) -> None:
    """Verify quicknet's G1 signature/G2 public key RFC9380 construction."""

    try:
        version = importlib.metadata.version("py-ecc")
        from py_ecc.bls.g2_primitives import subgroup_check
        from py_ecc.bls.hash_to_curve import hash_to_G1
        from py_ecc.bls.point_compression import decompress_G1, decompress_G2
        from py_ecc.optimized_bls12_381 import G2, is_inf, pairing
    except (ImportError, importlib.metadata.PackageNotFoundError) as error:
        raise VerificationError(
            f"py-ecc=={PY_ECC_VERSION} is required for quicknet signature verification"
        ) from error
    _exact(version, PY_ECC_VERSION, "py-ecc version")
    if len(signature) != 48 or len(public_key) != 96:
        _fail("quicknet signature/public-key byte length mismatch")
    try:
        signature_point = decompress_G1(int.from_bytes(signature, "big"))
        public_key_point = decompress_G2(
            (
                int.from_bytes(public_key[:48], "big"),
                int.from_bytes(public_key[48:], "big"),
            )
        )
        message = hashlib.sha256(round_number.to_bytes(8, "big")).digest()
        message_point = hash_to_G1(message, BLS_DST, hashlib.sha256)
        valid_points = (
            not is_inf(signature_point)
            and not is_inf(public_key_point)
            and not is_inf(message_point)
            and subgroup_check(signature_point)
            and subgroup_check(public_key_point)
            and subgroup_check(message_point)
        )
        valid_pairing = valid_points and (
            pairing(public_key_point, message_point) == pairing(G2, signature_point)
        )
    except (AssertionError, ValueError, TypeError) as error:
        raise VerificationError(f"invalid quicknet BLS encoding: {error}") from error
    if not valid_pairing:
        _fail("quicknet BLS signature verification failed")


class IndependentCounterStream:
    """Frozen SHA-256 counter stream, implemented independently of the generator."""

    def __init__(self, seed: bytes) -> None:
        if len(seed) != 32:
            _fail("derived seed must contain 32 bytes")
        self.prefix = DOMAIN.encode("utf-8") + b"\0" + seed
        self.counter = 0
        self.buffer = b""
        self.words = 0
        self.blocks = 0
        self.rejections: dict[int, int] = {}

    def next_u64(self) -> int:
        if len(self.buffer) < 8:
            if self.counter >= UINT64_SPACE:
                _fail("PRNG counter exhausted")
            self.buffer += hashlib.sha256(
                self.prefix + self.counter.to_bytes(8, "big")
            ).digest()
            self.counter += 1
            self.blocks += 1
        result = int.from_bytes(self.buffer[:8], "big")
        self.buffer = self.buffer[8:]
        self.words += 1
        return result

    def below(self, modulus: int) -> int:
        if not 1 <= modulus <= UINT64_SPACE:
            _fail("invalid rejection-sampling modulus")
        limit = UINT64_SPACE - UINT64_SPACE % modulus
        rejected = 0
        while True:
            word = self.next_u64()
            if word < limit:
                if rejected:
                    self.rejections[modulus] = self.rejections.get(modulus, 0) + rejected
                return word % modulus
            rejected += 1


def _weights(probabilities: Sequence[Fraction]) -> list[int]:
    if not probabilities or any(value < 0 for value in probabilities):
        _fail("invalid categorical distribution")
    if sum(probabilities) != 1:
        _fail("categorical distribution does not sum to one")
    denominator = math.lcm(*(value.denominator for value in probabilities))
    result = [value.numerator * (denominator // value.denominator) for value in probabilities]
    divisor = math.gcd(*result)
    return [value // divisor for value in result]


def _sample(weights: Sequence[int], stream: IndependentCounterStream) -> int:
    draw = stream.below(sum(weights))
    cumulative = 0
    for index, weight in enumerate(weights):
        cumulative += weight
        if draw < cumulative:
            return index
    _fail("categorical replay escaped cumulative intervals")


def _queue_step(model: dict[str, Any], state: int, action: int) -> int:
    queue, regime = divmod(state, 3)
    service = model["actions"][action]["service_capacity"]
    arrival = model["state_space"]["arrival_by_regime"][regime]
    return 3 * min(7, max(0, queue - service) + arrival) + (regime + 1) % 3


def _verify_protocol(protocol: dict[str, Any], raw: bytes) -> None:
    _exact(_sha(raw), PROTOCOL_SHA256, "frozen protocol SHA-256")
    _exact(protocol.get("schema_version"), PROTOCOL_SCHEMA, "protocol schema")
    _exact(protocol.get("protocol_version"), PROTOCOL_VERSION, "protocol version")
    generation = _object(protocol.get("data_generation"), "protocol.data_generation")
    _exact(_integer(generation.get("horizon"), "protocol horizon"), HORIZON, "protocol horizon")
    _exact(_rational(generation.get("true_gamma"), "protocol true gamma"), TRUE_GAMMA, "protocol true gamma")
    _exact(generation.get("family"), "refreshEnvironment", "protocol source family")
    _exact(generation.get("behavior_policy_id"), "behavior_uniform", "protocol behavior policy")
    _exact(generation.get("action_encoding"), ["eco", "boost"], "protocol action encoding")
    _exact(generation.get("state_encoding"), "state_id = 3 * queue + regime", "protocol state encoding")
    initial = _object(generation.get("initial_observation"), "protocol initial observation")
    _exact(_integer(initial.get("physical_state_index"), "initial state"), INITIAL_STATE, "initial state")
    _exact(_integer(initial.get("action_index"), "initial action"), INITIAL_ACTION, "initial action")
    prng = _object(generation.get("prng_contract"), "protocol PRNG")
    frozen_prng = {
        "beacon_chain_hash": CHAIN_HASH,
        "beacon_group_hash": GROUP_HASH,
        "beacon_public_key": PUBLIC_KEY,
        "beacon_scheme_id": SCHEME_ID,
        "beacon_genesis_unix_seconds": GENESIS_SECONDS,
        "beacon_period_seconds": PERIOD_SECONDS,
        "domain_utf8": DOMAIN,
        "version": PRNG_VERSION,
        "counter_start": 0,
        "hash": "SHA-256",
    }
    for key, expected in frozen_prng.items():
        _exact(prng.get(key), expected, f"protocol PRNG {key}")
    sampling = _object(generation.get("sampling_contract"), "protocol sampling")
    _exact(sampling.get("version"), SAMPLING_VERSION, "protocol sampling version")
    binary = _object(generation.get("binary_contract"), "protocol binary")
    _exact(binary.get("version"), BINARY_VERSION, "protocol binary version")
    _exact(binary.get("magic_hex"), BINARY_MAGIC.hex(), "protocol binary magic")
    _exact(_integer(binary.get("expected_byte_length"), "protocol binary length"), BINARY_EXPECTED_BYTES, "protocol binary length")
    path = _object(generation.get("path_contract"), "protocol path contract")
    for key, expected in (
        ("state_array_length", HORIZON + 1),
        ("action_array_length", HORIZON + 1),
        ("score_count", HORIZON),
        ("dummy_previous_action_used_only_at_x0", True),
    ):
        _exact(path.get(key), expected, f"protocol path {key}")


def _verify_model(model: dict[str, Any]) -> None:
    _exact(model.get("schema_version"), "controlled-queue-input-v1", "model schema")
    _exact(model.get("model_version"), "controlled-queue-v1", "model version")
    state_space = _object(model.get("state_space"), "model state_space")
    _exact(_integer(state_space.get("queue_capacity"), "queue capacity"), 7, "queue capacity")
    _exact(_integer(state_space.get("regime_count"), "regime count"), 3, "regime count")
    _exact(state_space.get("arrival_by_regime"), [0, 1, 2], "arrival table")
    actions = _array(model.get("actions"), "model actions")
    _exact(len(actions), ACTION_COUNT, "model action count")
    for index, (action_id, service) in enumerate((('eco', 1), ('boost', 2))):
        row = _object(actions[index], f"model action {index}")
        _exact(row.get("id"), action_id, f"model action {index} id")
        _exact(_integer(row.get("service_capacity"), f"model action {index} service"), service, f"model action {index} service")
    behavior = _object(model.get("behavior_policy"), "model behavior policy")
    _exact(behavior.get("id"), "behavior_uniform", "model behavior policy id")
    probabilities = _array(behavior.get("boost_probability_by_state"), "behavior probabilities")
    _exact(len(probabilities), STATE_COUNT, "behavior probability count")
    for index, value in enumerate(probabilities):
        _exact(_rational(value, f"behavior probability {index}"), Fraction(1, 2), f"behavior probability {index}")


def _verify_osf_response(value: dict[str, Any]) -> tuple[str, str, int]:
    data = _object(value.get("data"), "OSF response.data")
    registration_id = _string(data.get("id"), "OSF registration id")
    if re.fullmatch(r"[a-z0-9]{5}", registration_id) is None:
        _fail("OSF registration id must contain five lowercase letters or digits")
    _exact(data.get("type"), "registrations", "OSF response type")
    attributes = _object(data.get("attributes"), "OSF response attributes")
    _exact(_boolean(attributes.get("public"), "OSF public flag"), True, "OSF public flag")
    _exact(_boolean(attributes.get("registration"), "OSF registration flag"), True, "OSF registration flag")
    _exact(_boolean(attributes.get("withdrawn"), "OSF withdrawn flag"), False, "OSF withdrawn flag")
    date_registered, second = _registration_second(attributes.get("date_registered"))
    return registration_id, date_registered, second


def _verify_osf_binding_file_response(
    value: dict[str, Any], registration_id: str, binding_raw: bytes
) -> None:
    data = _object(value.get("data"), "OSF binding-file response.data")
    file_id = _string(data.get("id"), "OSF binding-file id")
    if not file_id:
        _fail("OSF binding-file id must be nonempty")
    _exact(data.get("type"), "files", "OSF binding-file response type")
    attributes = _object(data.get("attributes"), "OSF binding-file attributes")
    _exact(attributes.get("name"), "code-freeze-binding-v1.json", "OSF binding filename")
    _exact(attributes.get("kind"), "file", "OSF binding-file kind")
    _exact(
        _integer(attributes.get("current_version"), "OSF binding-file current version", minimum=1),
        1,
        "OSF binding-file current version",
    )
    materialized_path = _string(
        attributes.get("materialized_path"), "OSF binding materialized path"
    )
    segments = materialized_path.split("/")
    if (
        not materialized_path.startswith("/")
        or materialized_path.startswith("//")
        or materialized_path.endswith("/")
        or any(segment in {"", ".", ".."} for segment in segments[1:])
        or PurePosixPath(materialized_path).as_posix() != materialized_path
        or unicodedata.normalize("NFC", materialized_path) != materialized_path
    ):
        _fail(
            "OSF binding materialized path must be an absolute canonical POSIX "
            "path without empty or dot segments"
        )
    _exact(
        PurePosixPath(materialized_path).name,
        "code-freeze-binding-v1.json",
        "OSF binding materialized filename",
    )
    _exact(
        _integer(attributes.get("size"), "OSF binding file size", minimum=1),
        len(binding_raw),
        "OSF binding file size",
    )
    extra = _object(attributes.get("extra"), "OSF binding-file attributes.extra")
    hashes = _object(extra.get("hashes"), "OSF binding-file hashes")
    _exact(
        _digest(hashes.get("sha256"), "OSF binding-file SHA-256"),
        _sha(binding_raw),
        "OSF binding-file SHA-256",
    )
    relationships = _object(data.get("relationships"), "OSF binding-file relationships")
    if "node" in relationships:
        node = _object(
            relationships["node"], "OSF binding-file node relationship"
        )
        node_data = _object(
            node.get("data"), "OSF binding-file node relationship data"
        )
        _exact(
            node_data.get("id"),
            registration_id,
            "OSF binding-file node relationship id",
        )
        _string(node_data.get("type"), "OSF binding-file node relationship type")
    target = _object(relationships.get("target"), "OSF binding-file target relationship")
    target_data = _object(target.get("data"), "OSF binding-file target relationship data")
    _exact(
        target_data,
        {"id": registration_id, "type": "registrations"},
        "OSF binding-file registration target",
    )
    target_links = _object(target.get("links"), "OSF binding-file target links")
    related = _object(
        target_links.get("related"), "OSF binding-file target related link"
    )
    href = _string(related.get("href"), "OSF binding-file target related URL")
    _exact(
        href,
        f"https://api.osf.io/v2/registrations/{registration_id}/",
        "OSF binding-file target related URL",
    )


def _verify_chain_info(value: dict[str, Any]) -> None:
    _keys(
        value,
        {"public_key", "period", "genesis_time", "genesis_seed", "chain_hash", "scheme", "beacon_id"},
        "quicknet chain info",
    )
    _exact(value["public_key"], PUBLIC_KEY, "quicknet public key")
    _exact(_integer(value["period"], "quicknet period", minimum=1), PERIOD_SECONDS, "quicknet period")
    _exact(_integer(value["genesis_time"], "quicknet genesis", minimum=0), GENESIS_SECONDS, "quicknet genesis")
    _exact(value["genesis_seed"], GROUP_HASH, "quicknet genesis/group hash")
    _exact(value["chain_hash"], CHAIN_HASH, "quicknet chain hash")
    _exact(value["scheme"], SCHEME_ID, "quicknet scheme")
    _exact(value["beacon_id"], BEACON_ID, "quicknet beacon id")


def _verify_round_response(value: dict[str, Any], expected_round: int) -> tuple[bytes, str]:
    _keys(value, {"round", "signature", "randomness"}, "quicknet round response")
    _exact(_integer(value["round"], "quicknet round", minimum=1), expected_round, "formula-selected quicknet round")
    signature = _hex(value["signature"], 48, "quicknet signature")
    randomness = _digest(value["randomness"], "quicknet randomness")
    _exact(randomness, _sha(signature), "quicknet randomness identity")
    _verify_quicknet_signature(expected_round, signature, bytes.fromhex(PUBLIC_KEY))
    return signature, randomness


def _verify_binding(
    binding: dict[str, Any],
    protocol_raw: bytes,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    _keys(binding, {"artifact_status", "schema_version", "protocol", "code_freeze", "code_files"}, "code-freeze binding")
    _exact(binding["artifact_status"], BINDING_STATUS, "binding status")
    _exact(binding["schema_version"], BINDING_SCHEMA, "binding schema")
    protocol = _object(binding["protocol"], "binding protocol")
    _keys(protocol, {"path", "bytes", "sha256", "commit", "tree"}, "binding protocol")
    _exact(protocol["path"], PROTOCOL_PATH, "binding protocol path")
    _exact(_integer(protocol["bytes"], "binding protocol bytes", minimum=0), len(protocol_raw), "binding protocol bytes")
    _exact(_digest(protocol["sha256"], "binding protocol hash"), PROTOCOL_SHA256, "binding protocol hash")
    _exact(_oid(protocol["commit"], "binding protocol commit"), PROTOCOL_COMMIT, "binding protocol commit")
    _exact(_oid(protocol["tree"], "binding protocol tree"), PROTOCOL_TREE, "binding protocol tree")
    _verify_git_tree(PROTOCOL_COMMIT, PROTOCOL_TREE, "protocol")
    _verify_git_file(
        PROTOCOL_COMMIT,
        PROTOCOL_PATH,
        protocol_raw,
        PROTOCOL_SHA256,
        len(protocol_raw),
        "protocol",
    )

    code_freeze = _object(binding["code_freeze"], "binding code freeze")
    _keys(code_freeze, {"commit", "tree"}, "binding code freeze")
    commit = _oid(code_freeze["commit"], "code-freeze commit")
    tree = _oid(code_freeze["tree"], "code-freeze tree")
    if commit == PROTOCOL_COMMIT or tree == PROTOCOL_TREE:
        _fail("code-freeze Git objects must postdate the protocol-only objects")

    actual_rows = _array(binding["code_files"], "binding code files")
    _exact(len(actual_rows), len(CODE_FILES), "binding code-file count")
    checked_rows: list[dict[str, Any]] = []
    for index, (role, path_text, path) in enumerate(CODE_FILES):
        raw = _read(path, f"code file {role}")
        checked = _file_row(
            actual_rows[index], role, path_text, raw, f"binding code_files[{index}]"
        )
        checked_rows.append(checked)
    _verify_git_tree(commit, tree, "code freeze")
    _verify_git_ancestor(PROTOCOL_COMMIT, commit)
    for row, (_role, path_text, path) in zip(checked_rows, CODE_FILES, strict=True):
        _verify_git_file(
            commit,
            path_text,
            _read(path, f"code file {row['role']}"),
            row["sha256"],
            row["bytes"],
            f"code file {row['role']}",
        )
    return {"commit": commit, "tree": tree}, checked_rows


def _decode_binary(raw: bytes) -> tuple[bytes, bytes]:
    _exact(len(raw), BINARY_EXPECTED_BYTES, "trace binary byte length")
    if not raw.startswith(BINARY_MAGIC):
        _fail("trace binary magic mismatch")
    offset = len(BINARY_MAGIC)
    horizon, state_count, action_count = struct.unpack_from(">QQQ", raw, offset)
    offset += 24
    _exact(horizon, HORIZON, "binary horizon")
    _exact(state_count, HORIZON + 1, "binary state count")
    _exact(action_count, HORIZON + 1, "binary action count")
    states = raw[offset : offset + state_count]
    offset += state_count
    actions = raw[offset : offset + action_count]
    offset += action_count
    _exact(offset, len(raw), "binary payload alignment")
    if any(state >= STATE_COUNT for state in states):
        _fail("trace binary contains an out-of-range state")
    if any(action >= ACTION_COUNT for action in actions):
        _fail("trace binary contains an out-of-range action")
    _exact(states[0], INITIAL_STATE, "binary initial state")
    _exact(actions[0], INITIAL_ACTION, "binary dummy initial action")
    return states, actions


def _replay(
    model: dict[str, Any], trace_raw: bytes, seed: bytes
) -> tuple[dict[str, Any], dict[str, Any], bytes, bytes]:
    states, actions = _decode_binary(trace_raw)
    stream = IndependentCounterStream(seed)
    behavior_weights = [1, 1]
    base = (1 - TRUE_GAMMA) / STATE_COUNT
    source_visits = [0] * STATE_COUNT
    destination_counts = [0] * STATE_COUNT
    transition_action_counts = [0] * ACTION_COUNT
    state_action_counts = [[0] * ACTION_COUNT for _ in range(STATE_COUNT)]
    edge_counts = [
        [[0] * STATE_COUNT for _ in range(ACTION_COUNT)]
        for _ in range(STATE_COUNT)
    ]
    persistence_hits = 0

    for time in range(HORIZON):
        state = states[time]
        action = _sample(behavior_weights, stream)
        _exact(actions[time + 1], action, f"behavior-policy action replay at k={time}")
        step = _queue_step(model, state, action)
        kernel_weights = _weights(
            [
                base + (TRUE_GAMMA if destination == step else 0)
                for destination in range(STATE_COUNT)
            ]
        )
        destination = _sample(kernel_weights, stream)
        _exact(states[time + 1], destination, f"refreshEnvironment replay at k={time}")

        source_visits[state] += 1
        destination_counts[destination] += 1
        transition_action_counts[action] += 1
        state_action_counts[state][action] += 1
        edge_counts[state][action][destination] += 1
        persistence_hits += int(destination == step)

    if sum(source_visits) != HORIZON or sum(destination_counts) != HORIZON:
        _fail("state count conservation failed")
    if sum(transition_action_counts) != HORIZON:
        _fail("transition-action count conservation failed")
    if sum(map(sum, state_action_counts)) != HORIZON:
        _fail("state-action count conservation failed")
    if sum(sum(map(sum, action_rows)) for action_rows in edge_counts) != HORIZON:
        _fail("edge count conservation failed")

    return {
        "source_state_visits": source_visits,
        "destination_state_counts": destination_counts,
        "transition_action_counts": transition_action_counts,
        "state_action_counts": state_action_counts,
        "edge_counts": edge_counts,
        "persistence_hit_count": persistence_hits,
        "persistence_miss_count": HORIZON - persistence_hits,
    }, {
        "version": PRNG_VERSION,
        "words_consumed": stream.words,
        "bytes_consumed": stream.words * 8,
        "digest_blocks_generated": stream.blocks,
        "rejections_by_modulus": {
            str(key): value for key, value in sorted(stream.rejections.items())
        },
    }, states, actions


def _expected_counts(
    counts: dict[str, Any],
    trace_raw: bytes,
    model: dict[str, Any],
    seed: bytes,
) -> None:
    replay_counts, prng_audit, states, actions = _replay(model, trace_raw, seed)
    expected = {
        "artifact_status": ARTIFACT_STATUS,
        "schema_version": COUNTS_SCHEMA,
        "trace_version": TRACE_VERSION,
        "generator_revision": GENERATOR_REVISION,
        "horizon": HORIZON,
        "initial_state": states[0],
        "initial_action": actions[0],
        "final_state": states[-1],
        "final_action": actions[-1],
        "trace_sha256": _sha(trace_raw),
        "counts": replay_counts,
        "prng_audit": prng_audit,
        "nonclaims": NONCLAIMS,
    }
    _exact(counts, expected, "independently replayed prospective counts")


def _verify_manifest(
    manifest: dict[str, Any],
    *,
    paths: dict[str, Path],
    raws: dict[str, bytes],
    code_freeze: dict[str, Any],
    code_rows: list[dict[str, Any]],
    registration_id: str,
    date_registered: str,
    registration_second: int,
    round_number: int,
    round_time: int,
    signature: bytes,
    randomness: str,
    seed: bytes,
) -> None:
    _keys(
        manifest,
        {
            "artifact_status", "schema_version", "trace_version", "generator",
            "independent_verifier", "code_freeze", "registration", "beacon",
            "parameters", "inputs", "outputs", "manifest_note", "nonclaims",
        },
        "trace manifest",
    )
    _exact(manifest["artifact_status"], ARTIFACT_STATUS, "manifest status")
    _exact(manifest["schema_version"], MANIFEST_SCHEMA, "manifest schema")
    _exact(manifest["trace_version"], TRACE_VERSION, "manifest trace version")
    _exact(
        manifest["manifest_note"],
        "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "manifest note",
    )
    _exact(manifest["nonclaims"], NONCLAIMS, "manifest nonclaims")

    code_by_role = {row["role"]: row for row in code_rows}
    generator = _object(manifest["generator"], "manifest generator")
    _keys(generator, {"path", "revision", "bytes", "sha256"}, "manifest generator")
    expected_generator = code_by_role["trace_generator"]
    _exact(generator["path"], expected_generator["path"], "manifest generator path")
    _exact(generator["revision"], GENERATOR_REVISION, "manifest generator revision")
    _exact(generator["bytes"], expected_generator["bytes"], "manifest generator bytes")
    _exact(generator["sha256"], expected_generator["sha256"], "manifest generator hash")
    verifier = _object(manifest["independent_verifier"], "manifest verifier")
    _keys(verifier, {"path", "bytes", "sha256"}, "manifest verifier")
    expected_verifier = code_by_role["trace_verifier"]
    _exact(verifier, {key: expected_verifier[key] for key in ("path", "bytes", "sha256")}, "manifest verifier")

    frozen = _object(manifest["code_freeze"], "manifest code freeze")
    _keys(frozen, {"commit", "tree", "code_files"}, "manifest code freeze")
    _exact(frozen["commit"], code_freeze["commit"], "manifest code-freeze commit")
    _exact(frozen["tree"], code_freeze["tree"], "manifest code-freeze tree")
    _exact(frozen["code_files"], code_rows, "manifest code-file bindings")

    registration = _object(manifest["registration"], "manifest registration")
    _keys(registration, {"id", "date_registered", "unix_seconds_ceiling", "api_response_sha256", "binding_sha256", "binding_file_api_response_sha256", "protocol_commit", "protocol_tree"}, "manifest registration")
    _exact(registration["id"], registration_id, "manifest registration id")
    _exact(registration["date_registered"], date_registered, "manifest registration date")
    _exact(_integer(registration["unix_seconds_ceiling"], "manifest registration second"), registration_second, "manifest registration second")
    _exact(registration["api_response_sha256"], _sha(raws["osf_registration_response"]), "manifest OSF response hash")
    _exact(registration["binding_sha256"], _sha(raws["osf_registration_binding"]), "manifest binding hash")
    _exact(
        registration["binding_file_api_response_sha256"],
        _sha(raws["osf_registration_binding_file"]),
        "manifest OSF binding-file response hash",
    )
    _exact(registration["protocol_commit"], PROTOCOL_COMMIT, "manifest protocol commit")
    _exact(registration["protocol_tree"], PROTOCOL_TREE, "manifest protocol tree")

    beacon = _object(manifest["beacon"], "manifest beacon")
    _keys(beacon, {"chain_hash", "group_hash", "scheme_id", "round", "round_time_unix_seconds", "randomness", "signature_sha256", "derived_seed_sha256", "signature_verified", "signature_verifier"}, "manifest beacon")
    expected_beacon = {
        "chain_hash": CHAIN_HASH,
        "group_hash": GROUP_HASH,
        "scheme_id": SCHEME_ID,
        "round": round_number,
        "round_time_unix_seconds": round_time,
        "randomness": randomness,
        "signature_sha256": _sha(signature),
        "derived_seed_sha256": _sha(seed),
        "signature_verified": True,
        "signature_verifier": {
            "implementation": BLS_IMPLEMENTATION,
            "dependency": "py-ecc",
            "version": PY_ECC_VERSION,
            "dst": BLS_DST.decode("ascii"),
        },
    }
    _exact(beacon, expected_beacon, "manifest beacon")

    parameters = _object(manifest["parameters"], "manifest parameters")
    expected_parameters = {
        "horizon": HORIZON,
        "state_count": STATE_COUNT,
        "action_count": ACTION_COUNT,
        "initial_state": INITIAL_STATE,
        "initial_action": INITIAL_ACTION,
        "true_gamma": "149/200",
        "family": "refreshEnvironment",
        "behavior_policy": "behavior_uniform",
        "prng_version": PRNG_VERSION,
        "sampling_version": SAMPLING_VERSION,
        "binary_version": BINARY_VERSION,
        "binary_magic_hex": BINARY_MAGIC.hex(),
        "binary_expected_bytes": BINARY_EXPECTED_BYTES,
    }
    _exact(parameters, expected_parameters, "manifest parameters")

    expected_inputs = (
        ("protocol", paths["protocol"], raws["protocol"]),
        ("osf_registration_response", paths["osf_registration_response"], raws["osf_registration_response"]),
        ("osf_registration_binding", paths["osf_registration_binding"], raws["osf_registration_binding"]),
        ("osf_registration_binding_file", paths["osf_registration_binding_file"], raws["osf_registration_binding_file"]),
        ("quicknet_chain_info", paths["quicknet_chain_info"], raws["quicknet_chain_info"]),
        ("quicknet_round", paths["quicknet_round"], raws["quicknet_round"]),
        ("model_input", paths["model_input"], raws["model_input"]),
        ("model_manifest", paths["model_manifest"], raws["model_manifest"]),
        ("model_tables", paths["model_tables"], raws["model_tables"]),
    )
    input_rows = _array(manifest["inputs"], "manifest inputs")
    _exact(len(input_rows), len(expected_inputs), "manifest input count")
    for index, (role, path, raw) in enumerate(expected_inputs):
        _file_row(input_rows[index], role, _display(path), raw, f"manifest inputs[{index}]")

    expected_outputs = (
        ("trace_binary", paths["trace"], raws["trace"]),
        ("trace_counts", paths["counts"], raws["counts"]),
    )
    output_rows = _array(manifest["outputs"], "manifest outputs")
    _exact(len(output_rows), len(expected_outputs), "manifest output count")
    for index, (role, path, raw) in enumerate(expected_outputs):
        _file_row(output_rows[index], role, _display(path), raw, f"manifest outputs[{index}]")

    all_rows = [*input_rows, *output_rows, *code_rows]
    roles = [row["role"] for row in all_rows]
    paths_seen = [
        unicodedata.normalize("NFC", row["path"]).casefold() for row in all_rows
    ]
    if len(roles) != len(set(roles)):
        _fail("manifest provenance roles must be globally unique")
    if len(paths_seen) != len(set(paths_seen)):
        _fail("manifest provenance paths must be globally unique")


def verify_paths(
    protocol_path: Path,
    osf_response_path: Path,
    osf_binding_path: Path,
    osf_binding_file_path: Path,
    chain_info_path: Path,
    round_response_path: Path,
    model_input_path: Path,
    model_manifest_path: Path,
    model_tables_path: Path,
    trace_path: Path,
    counts_path: Path,
    manifest_path: Path,
) -> None:
    paths = {
        "protocol": protocol_path,
        "osf_registration_response": osf_response_path,
        "osf_registration_binding": osf_binding_path,
        "osf_registration_binding_file": osf_binding_file_path,
        "quicknet_chain_info": chain_info_path,
        "quicknet_round": round_response_path,
        "model_input": model_input_path,
        "model_manifest": model_manifest_path,
        "model_tables": model_tables_path,
        "trace": trace_path,
        "counts": counts_path,
        "manifest": manifest_path,
    }
    _verify_distinct_paths(paths)
    raws = {role: _read(path, role) for role, path in paths.items()}

    protocol = _parse_controlled_json(raws["protocol"], "protocol")
    binding = _parse_controlled_json(raws["osf_registration_binding"], "OSF binding")
    counts = _parse_controlled_json(raws["counts"], "prospective counts")
    manifest = _parse_controlled_json(raws["manifest"], "prospective manifest")
    model = _object(parse_json(raws["model_input"], "model input"), "model input")
    _object(parse_json(raws["model_manifest"], "model manifest"), "model manifest")
    _object(parse_json(raws["model_tables"], "model tables"), "model tables")
    osf_response = _object(parse_json(raws["osf_registration_response"], "OSF response"), "OSF response")
    osf_binding_file = _object(
        parse_json(raws["osf_registration_binding_file"], "OSF binding-file response"),
        "OSF binding-file response",
    )
    chain_info = _object(parse_json(raws["quicknet_chain_info"], "quicknet chain info"), "quicknet chain info")
    round_response = _object(parse_json(raws["quicknet_round"], "quicknet round response"), "quicknet round response")

    _verify_protocol(protocol, raws["protocol"])
    bindings = _object(protocol.get("bindings"), "protocol bindings")
    frozen_model_paths = {
        "model_input": "applications/controlled_queue/model-v1.json",
        "model_manifest": "applications/controlled_queue/generated/model-v1-manifest.json",
        "model_tables": "applications/controlled_queue/generated/model-v1-tables.json",
    }
    for role, frozen_path in frozen_model_paths.items():
        row = _object(bindings.get(role), f"protocol bindings.{role}")
        _exact(row.get("path"), frozen_path, f"protocol {role} path")
        _exact(row.get("sha256"), _sha(raws[role]), f"protocol {role} hash")
    _verify_model(model)

    registration_id, date_registered, registration_second = _verify_osf_response(osf_response)
    _verify_osf_binding_file_response(
        osf_binding_file, registration_id, raws["osf_registration_binding"]
    )
    code_freeze, code_rows = _verify_binding(binding, raws["protocol"])
    _verify_chain_info(chain_info)
    round_number, round_time = _formula_round(registration_second)
    signature, randomness = _verify_round_response(round_response, round_number)
    seed = hashlib.sha256(
        DOMAIN.encode("utf-8")
        + b"\0"
        + bytes.fromhex(CHAIN_HASH)
        + round_number.to_bytes(8, "big")
        + signature
    ).digest()

    _expected_counts(counts, raws["trace"], model, seed)
    _verify_manifest(
        manifest,
        paths=paths,
        raws=raws,
        code_freeze=code_freeze,
        code_rows=code_rows,
        registration_id=registration_id,
        date_registered=date_registered,
        registration_second=registration_second,
        round_number=round_number,
        round_time=round_time,
        signature=signature,
        randomness=randomness,
        seed=seed,
    )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    parser.add_argument("--osf-registration-response", type=Path, default=DEFAULT_OSF_RESPONSE)
    parser.add_argument("--osf-registration-binding", type=Path, default=DEFAULT_OSF_BINDING)
    parser.add_argument(
        "--osf-registration-binding-file", type=Path, default=DEFAULT_OSF_BINDING_FILE
    )
    parser.add_argument("--quicknet-chain-info", type=Path, default=DEFAULT_CHAIN_INFO)
    parser.add_argument("--quicknet-round", type=Path, default=DEFAULT_ROUND_RESPONSE)
    parser.add_argument("--model-input", type=Path, default=DEFAULT_MODEL_INPUT)
    parser.add_argument("--model-manifest", type=Path, default=DEFAULT_MODEL_MANIFEST)
    parser.add_argument("--model-tables", type=Path, default=DEFAULT_MODEL_TABLES)
    parser.add_argument("--trace", type=Path, default=DEFAULT_TRACE)
    parser.add_argument("--counts", type=Path, default=DEFAULT_COUNTS)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--check", action="store_true", help="explicit read-only verification mode")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        verify_paths(
            args.protocol,
            args.osf_registration_response,
            args.osf_registration_binding,
            args.osf_registration_binding_file,
            args.quicknet_chain_info,
            args.quicknet_round,
            args.model_input,
            args.model_manifest,
            args.model_tables,
            args.trace,
            args.counts,
            args.manifest,
        )
    except (OSError, VerificationError, KeyError, ValueError, struct.error) as error:
        print(f"prospective controlled-queue trace verification failed: {error}", file=sys.stderr)
        return 1
    print("verified prospective controlled-queue trace, public provenance, quicknet signature, replay, and counts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
