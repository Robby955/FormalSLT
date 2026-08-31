#!/usr/bin/env python3
"""Issue, verify, and inspect compact FormalSLT statistical certificates.

Version 1 deliberately supports one profile: the Good Judgment Project Brier
monitor.  The raw replay remains a separate, expensive audit.  This program
binds its canonical artifacts to a small receipt, checks the tracked Lean
source pins, and can run the focused Lean checker without embedding every data
row in a generated proof file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
PROFILE = "gjp-brier-countable-strategy-retrospective-v1"
CERTIFICATE_SCHEMA = "formalslt.certificate.v1"
TRACE_SCHEMA = "formalslt.monitor-trace.v1"
CERTIFICATE_ID = "gjp-brier-monitor-2026-08-30"

STREAM_NAME = "gjp-brier-monitor-v1-stream.json"
RECEIPT_NAME = "gjp-brier-monitor-v1-receipt.json"
MANIFEST_NAME = "gjp-brier-monitor-v1-manifest.json"
STREAM_SCHEMA = "formalslt.brier-monitor.gjp-stream.v1"
RECEIPT_SCHEMA = "formalslt.brier-monitor.gjp-receipt.v1"
MANIFEST_SCHEMA = "formalslt.brier-monitor.gjp-manifest.v1"

LEAN_DATA = ROOT / "FormalSLT/Applications/GJPBrierMonitorReplayData.lean"
LEAN_CERTIFICATE = (
    ROOT / "FormalSLT/Applications/GJPBrierMonitorCountableStrategyCertificate.lean"
)
LEAN_CHECKER = (
    ROOT / "examples/CheckGJPBrierMonitorCountableStrategyCertificate.lean"
)
REPLAY_BUILDER = ROOT / "scripts/build_gjp_brier_replay.py"
REPLAY_VERIFIER = ROOT / "scripts/verify_gjp_brier_replay.py"
PROTOCOL = ROOT / "applications/brier_monitor/realdata/gjp-brier-protocol-v1.json"

DEFAULT_CERTIFICATE = ROOT / "docs/site/monitor/gjp-certificate-v1.json"
DEFAULT_TRACE = ROOT / "docs/site/monitor/gjp-monitor-trace-v1.json"

EXPECTED_HORIZON = 175
EXPECTED_DELTA = Fraction(1, 160)
EXPECTED_EMPIRICAL_RISK = Fraction(
    8392854858107881548807002521,
    175000000000000000000000000000,
)
EXPECTED_QUADRATIC_VARIATION = Fraction(
    120294916573959339034379223444031875456675202377307499560373876000810003865835968114105281625044298440665469050434955903229658713165131927176284821631589697199072750106094269111560144062103,
    31490227338507663225340625775620191856936438614666732905572545768337906435386587182224270548837430336629184362095030510201049599773045834916208000000000000000000000000000000000000000000000,
)
EXPECTED_REPLAY_BOUND_UPPER = Fraction(4313300111337, 31250000000000)
KERNEL_BOUND = Fraction(131, 1000)
EXPECTED_POSTERIOR = {
    "constant-train-baserate": Fraction(124844808069, 1000000000000000),
    "first-week-mean": Fraction(1565799931481, 1000000000000000),
    "final-consensus-median": Fraction(101346719745919, 200000000000000),
    "extremized-final-consensus": Fraction(98315151306171, 200000000000000),
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class CertificateError(ValueError):
    """Raised when a certificate or one of its bindings is invalid."""


def _reject_float(value: str) -> None:
    raise CertificateError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise CertificateError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CertificateError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def load_canonical_json(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise CertificateError(f"cannot read {label}: {path}") from error
    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CertificateError(f"invalid UTF-8 JSON in {label}: {error}") from error
    if not isinstance(value, dict):
        raise CertificateError(f"{label} must be a JSON object")
    if canonical_json_bytes(value) != raw:
        raise CertificateError(f"{label} is not canonical JSON")
    return value, raw


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise CertificateError(f"cannot hash {path}") from error
    return digest.hexdigest()


def rational_text(value: Fraction) -> str:
    reduced = Fraction(value)
    if reduced.denominator == 1:
        return str(reduced.numerator)
    return f"{reduced.numerator}/{reduced.denominator}"


def parse_fraction(value: Any, label: str) -> Fraction:
    if not isinstance(value, str):
        raise CertificateError(f"{label} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise CertificateError(f"invalid rational at {label}: {value!r}") from error
    if rational_text(result) != value:
        raise CertificateError(f"noncanonical rational at {label}: {value!r}")
    return result


def decimal_text(value: Fraction, places: int = 8) -> str:
    with localcontext() as context:
        context.prec = max(40, places + 20)
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
        return format(decimal, f".{places}f")


def _require(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise CertificateError(f"{label} mismatch: expected {expected!r}, got {actual!r}")


def _manifest_role(manifest: dict[str, Any], role: str) -> dict[str, Any]:
    rows = [row for row in manifest.get("files", []) if row.get("role") == role]
    if len(rows) != 1:
        raise CertificateError(f"manifest must contain exactly one {role!r} row")
    return rows[0]


def _artifact_paths(directory: Path) -> tuple[Path, Path, Path]:
    root = directory.resolve()
    paths = root / STREAM_NAME, root / RECEIPT_NAME, root / MANIFEST_NAME
    missing = [path.name for path in paths if not path.is_file()]
    if missing:
        raise CertificateError("artifact directory is missing: " + ", ".join(missing))
    return paths


def validate_artifacts(directory: Path) -> dict[str, Any]:
    stream_path, receipt_path, manifest_path = _artifact_paths(directory)
    stream, stream_raw = load_canonical_json(stream_path, "GJP stream")
    receipt, receipt_raw = load_canonical_json(receipt_path, "GJP receipt")
    manifest, manifest_raw = load_canonical_json(manifest_path, "GJP manifest")

    _require(stream.get("schema_version"), STREAM_SCHEMA, "stream schema")
    _require(receipt.get("receipt_schema"), RECEIPT_SCHEMA, "receipt schema")
    _require(manifest.get("manifest_schema"), MANIFEST_SCHEMA, "manifest schema")
    stream_digest = sha256_bytes(stream_raw)
    receipt_digest = sha256_bytes(receipt_raw)
    manifest_digest = sha256_bytes(manifest_raw)
    _require(receipt.get("stream_sha256"), stream_digest, "receipt stream digest")

    stream_row = _manifest_role(manifest, "stream")
    receipt_row = _manifest_role(manifest, "receipt")
    _require(stream_row.get("name"), STREAM_NAME, "manifest stream name")
    _require(stream_row.get("bytes"), len(stream_raw), "manifest stream bytes")
    _require(stream_row.get("sha256"), stream_digest, "manifest stream digest")
    _require(receipt_row.get("name"), RECEIPT_NAME, "manifest receipt name")
    _require(receipt_row.get("bytes"), len(receipt_raw), "manifest receipt bytes")
    _require(receipt_row.get("sha256"), receipt_digest, "manifest receipt digest")

    builder_row = _manifest_role(manifest, "builder")
    verifier_row = _manifest_role(manifest, "independent_verifier")
    _require(builder_row.get("sha256"), sha256_file(REPLAY_BUILDER), "builder digest")
    _require(verifier_row.get("sha256"), sha256_file(REPLAY_VERIFIER), "verifier digest")
    _require(receipt.get("implementation_commit"), manifest.get("implementation_commit"),
             "implementation commit")
    _require(receipt.get("implementation_tree"), manifest.get("implementation_tree"),
             "implementation tree")

    selected = receipt.get("selected_witness", {})
    _require(receipt.get("confidence_delta"), rational_text(EXPECTED_DELTA), "delta")
    _require(receipt.get("monitor", {}).get("observations"), EXPECTED_HORIZON,
             "monitor horizon")
    _require(
        parse_fraction(selected.get("posterior_empirical_brier_risk"), "empirical risk"),
        EXPECTED_EMPIRICAL_RISK,
        "empirical risk",
    )
    _require(
        parse_fraction(selected.get("suffix_predictor_quadratic_variation"),
                       "quadratic variation"),
        EXPECTED_QUADRATIC_VARIATION,
        "quadratic variation",
    )
    _require(
        parse_fraction(selected.get("boundary_interval", {}).get("upper"),
                       "replay boundary upper"),
        EXPECTED_REPLAY_BOUND_UPPER,
        "replay boundary upper",
    )
    _require(selected.get("wake"), 0, "selected wake")
    _require(selected.get("tilt"), "1/2", "selected tilt")
    _require(receipt.get("overall_preregistered_verdict", {}).get("status"), "FAIL",
             "preregistered status")
    posterior = receipt.get("calibration", {}).get("posterior", {}).get(
        "exact_rational_weights", {}
    )
    for model, expected in EXPECTED_POSTERIOR.items():
        _require(parse_fraction(posterior.get(model), f"posterior {model}"), expected,
                 f"posterior {model}")

    trace_rows = receipt.get("baselines", {}).get("B3_anytime_valid", {}).get(
        "selected_by_time", []
    )
    if not isinstance(trace_rows, list) or len(trace_rows) != EXPECTED_HORIZON - 3:
        raise CertificateError("B3 monitor trace must contain reporting times 4 through 175")
    _require([row.get("horizon") for row in trace_rows], list(range(4, 176)),
             "trace reporting times")

    return {
        "manifest": manifest,
        "manifest_bytes": len(manifest_raw),
        "manifest_sha256": manifest_digest,
        "receipt": receipt,
        "receipt_bytes": len(receipt_raw),
        "receipt_sha256": receipt_digest,
        "stream": stream,
        "stream_bytes": len(stream_raw),
        "stream_sha256": stream_digest,
        "trace_rows": trace_rows,
    }


def _lean_string_constant(name: str) -> str:
    source = LEAN_DATA.read_text(encoding="utf-8")
    pattern = rf'abbrev\s+{re.escape(name)}\s*:\s*String\s*:=\s*"([^"]+)"'
    match = re.search(pattern, source)
    if match is None:
        raise CertificateError(f"Lean data module has no String constant {name}")
    return match.group(1)


def validate_tracked_replay_pins(artifacts: dict[str, Any]) -> None:
    _require(_lean_string_constant("streamSha256"), artifacts["stream_sha256"],
             "Lean stream pin")
    _require(_lean_string_constant("receiptSha256"), artifacts["receipt_sha256"],
             "Lean receipt pin")
    _require(_lean_string_constant("protocolSha256"),
             artifacts["receipt"].get("protocol_sha256"), "Lean protocol pin")
    _require(_lean_string_constant("implementationCommit"),
             artifacts["receipt"].get("implementation_commit"),
             "Lean implementation commit")
    _require(_lean_string_constant("implementationTree"),
             artifacts["receipt"].get("implementation_tree"),
             "Lean implementation tree")


def _source_ref() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD^{commit}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise CertificateError("cannot resolve certificate implementation commit") from error
    if not re.fullmatch(r"[0-9a-f]{40}", result):
        raise CertificateError("certificate implementation commit is not lowercase 40-hex")
    for path in (Path(__file__).resolve(), LEAN_DATA, LEAN_CERTIFICATE, LEAN_CHECKER):
        relative = path.relative_to(ROOT).as_posix()
        try:
            frozen = subprocess.run(
                ["git", "show", f"{result}:{relative}"],
                cwd=ROOT,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            ).stdout
        except (OSError, subprocess.CalledProcessError) as error:
            raise CertificateError(f"certificate source is not committed: {relative}") from error
        if frozen != path.read_bytes():
            raise CertificateError(f"certificate source differs from {result}: {relative}")
    return result


def _source_record(path: Path) -> dict[str, Any]:
    return {
        "bytes": path.stat().st_size,
        "path": path.relative_to(ROOT).as_posix(),
        "sha256": sha256_file(path),
    }


def build_trace(artifacts: dict[str, Any]) -> dict[str, Any]:
    threshold = parse_fraction(
        artifacts["receipt"]["selected_witness"]["train_base_rate_brier_threshold"],
        "train base-rate threshold",
    )
    points: list[dict[str, Any]] = []
    for row in artifacts["trace_rows"]:
        empirical = parse_fraction(row["posterior_empirical_brier_risk"], "trace empirical")
        lower = parse_fraction(row["boundary_interval"]["lower"], "trace lower")
        upper = parse_fraction(row["boundary_interval"]["upper"], "trace upper")
        points.append(
            {
                "boundary_lower": rational_text(lower),
                "boundary_lower_decimal": decimal_text(lower),
                "boundary_upper": rational_text(upper),
                "boundary_upper_decimal": decimal_text(upper),
                "empirical_risk": rational_text(empirical),
                "empirical_risk_decimal": decimal_text(empirical),
                "n": row["horizon"],
            }
        )
    return {
        "certificate_id": CERTIFICATE_ID,
        "display_only": True,
        "points": points,
        "replayed_threshold": rational_text(threshold),
        "replayed_threshold_decimal": decimal_text(threshold),
        "schema_version": TRACE_SCHEMA,
        "source_receipt_sha256": artifacts["receipt_sha256"],
    }


def run_lean_checker() -> dict[str, Any]:
    lake = Path.home() / ".elan/bin/lake"
    if not lake.is_file():
        raise CertificateError(f"Lean launcher is absent: {lake}")
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "2"
    try:
        result = subprocess.run(
            [str(lake), "env", "lean", LEAN_CHECKER.relative_to(ROOT).as_posix()],
            cwd=ROOT,
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=900,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CertificateError("focused Lean checker could not complete") from error
    if result.returncode != 0:
        tail = "\n".join(result.stdout.splitlines()[-40:])
        raise CertificateError(f"focused Lean checker failed:\n{tail}")
    if "sorryAx" in result.stdout or "declaration uses 'sorry'" in result.stdout:
        raise CertificateError("focused Lean checker reported an admitted proof")
    seen: set[str] = set()
    for block in re.findall(r"depends on axioms:\s*\[(.*?)\]", result.stdout, re.DOTALL):
        seen.update(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", block))
    unknown = seen - ALLOWED_AXIOMS
    if unknown:
        raise CertificateError("focused Lean checker used unexpected axioms: " + ", ".join(sorted(unknown)))
    return {
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "command": "~/.elan/bin/lake env lean " + LEAN_CHECKER.relative_to(ROOT).as_posix(),
        "observed_axioms": sorted(seen),
        "status": "PASS",
    }


def build_certificate(
    artifacts: dict[str, Any], trace_raw: bytes, lean_result: dict[str, Any], source_ref: str
) -> dict[str, Any]:
    receipt = artifacts["receipt"]
    selected = receipt["selected_witness"]
    posterior = receipt["calibration"]["posterior"]["exact_rational_weights"]
    verdict = receipt["overall_preregistered_verdict"]
    replay_upper = parse_fraction(selected["boundary_interval"]["upper"], "replay upper")
    empirical = parse_fraction(selected["posterior_empirical_brier_risk"], "empirical")
    threshold = parse_fraction(selected["train_base_rate_brier_threshold"], "threshold")
    confidence = 1 - EXPECTED_DELTA
    return {
        "certificate_id": CERTIFICATE_ID,
        "certificate_verification": "PASS",
        "claim": {
            "coverage_use": "RETROSPECTIVE_FIXED_CATALOG_ONLY",
            "failure_mass": rational_text(EXPECTED_DELTA),
            "kernel_checked_upper_bound": rational_text(KERNEL_BOUND),
            "kernel_checked_upper_bound_decimal": decimal_text(KERNEL_BOUND, 3),
            "quantity": "posterior-averaged encountered conditional prefix Brier risk",
            "relation": "<",
            "theorem_support": (
                "one event for every reporting time and eligible model and active-strategy "
                "posterior in the fixed catalog"
            ),
        },
        "confidence": {
            "level": rational_text(confidence),
            "level_decimal": decimal_text(confidence, 5),
            "monitoring": "continuous reporting is covered by the theorem event",
        },
        "data": {
            "dataset_license": artifacts["manifest"]["dataset"]["license"],
            "dataset_persistent_id": artifacts["manifest"]["dataset"]["persistent_id"],
            "dataset_version": artifacts["manifest"]["dataset"]["version"],
            "manifest_bytes": artifacts["manifest_bytes"],
            "manifest_sha256": artifacts["manifest_sha256"],
            "observations": EXPECTED_HORIZON,
            "protocol_sha256": receipt["protocol_sha256"],
            "receipt_bytes": artifacts["receipt_bytes"],
            "receipt_sha256": artifacts["receipt_sha256"],
            "stream_bytes": artifacts["stream_bytes"],
            "stream_sha256": artifacts["stream_sha256"],
        },
        "observed": {
            "posterior_empirical_brier_risk": rational_text(empirical),
            "posterior_empirical_brier_risk_decimal": decimal_text(empirical),
            "replayed_anytime_boundary_upper": rational_text(replay_upper),
            "replayed_anytime_boundary_upper_decimal": decimal_text(replay_upper),
            "train_base_rate_brier_threshold": rational_text(threshold),
            "train_base_rate_brier_threshold_decimal": decimal_text(threshold),
        },
        "profile": PROFILE,
        "provenance": {
            "certificate_implementation_commit": source_ref,
            "replay_implementation_commit": receipt["implementation_commit"],
            "replay_implementation_tree": receipt["implementation_tree"],
            "tier": "AUDITED_PUBLIC_DATA",
        },
        "schema_version": CERTIFICATE_SCHEMA,
        "selection": {
            "model_posterior": posterior,
            "model_posterior_timing": "calibration split only, frozen before monitoring",
            "strategy": {"tilt": "1/2", "wake": 0},
            "strategy_catalog_timing": (
                "fixed after this replay; this 0.131 endpoint is retrospective and is not "
                "the preregistered GJP endpoint"
            ),
        },
        "study": {
            "failed_win_condition_checks": verdict["failed_win_condition_checks"],
            "incomplete_controls": verdict["incomplete_controls"],
            "preregistered_status": verdict["status"],
            "statement": (
                "The certificate verifies its stated arithmetic and theorem scope; the "
                "separate preregistered scientific comparison failed."
            ),
        },
        "trace": {
            "bytes": len(trace_raw),
            "path": "gjp-monitor-trace-v1.json",
            "sha256": sha256_bytes(trace_raw),
        },
        "verification": {
            "certificate_engine": _source_record(Path(__file__).resolve()),
            "data_replay": {
                "builder": _source_record(REPLAY_BUILDER),
                "command": (
                    "python3 scripts/verify_gjp_brier_replay.py --inputs <pinned-input-dir> "
                    "--artifacts <artifact-dir>"
                ),
                "independent_verifier": _source_record(REPLAY_VERIFIER),
                "scope": "pinned public GJP bytes to the quantized stream and exact summaries",
                "status": "PASS",
            },
            "lean_kernel": {
                **lean_result,
                "checker": _source_record(LEAN_CHECKER),
                "scope": (
                    "statistical theorem specialization and endpoint arithmetic from supplied "
                    "exact summaries"
                ),
                "sources": [_source_record(LEAN_DATA), _source_record(LEAN_CERTIFICATE)],
                "theorem": (
                    "FormalSLT.Applications.GJPBrierMonitorCountableStrategyCertificate."
                    "countableStrategySummaryEndpoint_lt_oneHundredThirtyOne_thousandths"
                ),
            },
            "not_checked_by_lean": [
                "raw CSV and TSV parsing",
                "forecast aggregation and quantization",
                "the execution of the independent Python replay",
                "future, population, stationary, or deployment risk",
            ],
        },
    }


def _validate_source_record(record: dict[str, Any], label: str) -> None:
    path_value = record.get("path")
    if not isinstance(path_value, str) or not path_value:
        raise CertificateError(f"{label} has no path")
    path = (ROOT / path_value).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as error:
        raise CertificateError(f"{label} path escapes the repository") from error
    if not path.is_file():
        raise CertificateError(f"{label} source is absent: {path_value}")
    _require(record.get("bytes"), path.stat().st_size, f"{label} bytes")
    _require(record.get("sha256"), sha256_file(path), f"{label} digest")


def validate_certificate(
    certificate: dict[str, Any], certificate_raw: bytes, trace: dict[str, Any], trace_raw: bytes
) -> None:
    _require(certificate.get("schema_version"), CERTIFICATE_SCHEMA, "certificate schema")
    _require(certificate.get("profile"), PROFILE, "certificate profile")
    _require(certificate.get("certificate_id"), CERTIFICATE_ID, "certificate id")
    _require(certificate.get("certificate_verification"), "PASS", "certificate status")
    claim = certificate.get("claim", {})
    _require(parse_fraction(claim.get("kernel_checked_upper_bound"), "kernel bound"),
             KERNEL_BOUND, "kernel bound")
    _require(parse_fraction(claim.get("failure_mass"), "failure mass"), EXPECTED_DELTA,
             "failure mass")
    _require(claim.get("coverage_use"), "RETROSPECTIVE_FIXED_CATALOG_ONLY",
             "coverage use")
    observed = certificate.get("observed", {})
    _require(parse_fraction(observed.get("posterior_empirical_brier_risk"), "empirical"),
             EXPECTED_EMPIRICAL_RISK, "empirical")
    _require(parse_fraction(observed.get("replayed_anytime_boundary_upper"), "replay bound"),
             EXPECTED_REPLAY_BOUND_UPPER, "replay bound")
    _require(certificate.get("study", {}).get("preregistered_status"), "FAIL",
             "study verdict")
    _require(trace.get("schema_version"), TRACE_SCHEMA, "trace schema")
    _require(trace.get("certificate_id"), CERTIFICATE_ID, "trace certificate id")
    _require(trace.get("source_receipt_sha256"),
             certificate.get("data", {}).get("receipt_sha256"), "trace receipt pin")
    points = trace.get("points", [])
    if not isinstance(points, list) or len(points) != EXPECTED_HORIZON - 3:
        raise CertificateError("monitor trace has the wrong number of points")
    _require([point.get("n") for point in points], list(range(4, 176)),
             "monitor trace times")
    final = points[-1]
    _require(parse_fraction(final.get("empirical_risk"), "final empirical"),
             EXPECTED_EMPIRICAL_RISK, "final empirical")
    _require(parse_fraction(final.get("boundary_upper"), "final replay bound"),
             EXPECTED_REPLAY_BOUND_UPPER, "final replay bound")
    trace_record = certificate.get("trace", {})
    _require(trace_record.get("bytes"), len(trace_raw), "trace bytes")
    _require(trace_record.get("sha256"), sha256_bytes(trace_raw), "trace digest")
    lean = certificate.get("verification", {}).get("lean_kernel", {})
    _validate_source_record(lean.get("checker", {}), "Lean checker")
    for index, record in enumerate(lean.get("sources", [])):
        _validate_source_record(record, f"Lean source {index}")
    replay = certificate.get("verification", {}).get("data_replay", {})
    _validate_source_record(
        certificate.get("verification", {}).get("certificate_engine", {}),
        "certificate engine",
    )
    _validate_source_record(replay.get("builder", {}), "replay builder")
    _validate_source_record(replay.get("independent_verifier", {}), "replay verifier")
    if not certificate_raw.endswith(b"\n"):
        raise CertificateError("certificate must end with a newline")


def verify_artifact_binding(certificate: dict[str, Any], directory: Path) -> None:
    artifacts = validate_artifacts(directory)
    data = certificate["data"]
    for key in (
        "manifest_bytes",
        "manifest_sha256",
        "receipt_bytes",
        "receipt_sha256",
        "stream_bytes",
        "stream_sha256",
    ):
        _require(data.get(key), artifacts[key], f"certificate {key}")
    validate_tracked_replay_pins(artifacts)


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _print_summary(certificate: dict[str, Any]) -> None:
    observed = certificate["observed"]
    claim = certificate["claim"]
    study = certificate["study"]
    print("FormalSLT real-data certificate")
    print(f"Dataset:                     {certificate['data']['dataset_persistent_id']}")
    print(f"Observations:                {certificate['data']['observations']}")
    print(f"Observed Brier loss:         {observed['posterior_empirical_brier_risk_decimal']}")
    print(f"Replayed anytime boundary:  {observed['replayed_anytime_boundary_upper_decimal']}")
    print(f"Compact Lean endpoint:      < {claim['kernel_checked_upper_bound_decimal']}")
    print(f"Confidence level:           {certificate['confidence']['level_decimal']}")
    print(f"Certificate verification:   {certificate['certificate_verification']}")
    print(f"Preregistered study:        {study['preregistered_status']}")
    print(f"Coverage use:               {claim['coverage_use']}")


def issue(args: argparse.Namespace) -> int:
    artifacts = validate_artifacts(args.artifacts)
    if not args.skip_tracked_pin_check:
        validate_tracked_replay_pins(artifacts)
    lean_result = run_lean_checker() if args.run_lean else {
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "command": "not run during issuance",
        "observed_axioms": [],
        "status": "NOT_RUN",
    }
    if lean_result["status"] != "PASS":
        raise CertificateError("issuance requires --run-lean")
    trace = build_trace(artifacts)
    trace_raw = canonical_json_bytes(trace)
    certificate = build_certificate(artifacts, trace_raw, lean_result, _source_ref())
    certificate_raw = canonical_json_bytes(certificate)
    validate_certificate(certificate, certificate_raw, trace, trace_raw)
    _atomic_write(args.out_trace, trace_raw)
    _atomic_write(args.out_certificate, certificate_raw)
    print(f"wrote {args.out_certificate.relative_to(ROOT) if args.out_certificate.is_relative_to(ROOT) else args.out_certificate}")
    print(f"wrote {args.out_trace.relative_to(ROOT) if args.out_trace.is_relative_to(ROOT) else args.out_trace}")
    _print_summary(certificate)
    return 0


def verify(args: argparse.Namespace) -> int:
    certificate, certificate_raw = load_canonical_json(args.certificate, "certificate")
    trace, trace_raw = load_canonical_json(args.trace, "monitor trace")
    validate_certificate(certificate, certificate_raw, trace, trace_raw)
    if args.artifacts is not None:
        verify_artifact_binding(certificate, args.artifacts)
    if not args.skip_lean:
        run_lean_checker()
    print("FormalSLT compact certificate: PASS")
    if args.artifacts is not None:
        print("artifact binding: PASS")
    print("Lean checker: " + ("NOT RUN" if args.skip_lean else "PASS"))
    _print_summary(certificate)
    return 0


def show(args: argparse.Namespace) -> int:
    certificate, _raw = load_canonical_json(args.certificate, "certificate")
    _print_summary(certificate)
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(description=__doc__)
    commands = root.add_subparsers(dest="command", required=True)
    issue_parser = commands.add_parser("issue", help="issue the supported compact certificate")
    issue_parser.add_argument("--artifacts", type=Path, required=True)
    issue_parser.add_argument("--out-certificate", type=Path, default=DEFAULT_CERTIFICATE)
    issue_parser.add_argument("--out-trace", type=Path, default=DEFAULT_TRACE)
    issue_parser.add_argument("--run-lean", action="store_true")
    issue_parser.add_argument("--skip-tracked-pin-check", action="store_true", help=argparse.SUPPRESS)
    issue_parser.set_defaults(handler=issue)

    verify_parser = commands.add_parser("verify", help="verify a compact certificate")
    verify_parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    verify_parser.add_argument("--trace", type=Path, default=DEFAULT_TRACE)
    verify_parser.add_argument("--artifacts", type=Path)
    verify_parser.add_argument("--skip-lean", action="store_true")
    verify_parser.set_defaults(handler=verify)

    show_parser = commands.add_parser("show", help="print the human-readable result")
    show_parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    show_parser.set_defaults(handler=show)
    return root


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(list(argv) if argv is not None else None)
    try:
        return int(args.handler(args))
    except CertificateError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
