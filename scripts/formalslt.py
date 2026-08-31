#!/usr/bin/env python3
"""User-facing dispatcher for supported FormalSLT certificate profiles.

The command is deliberately fail-closed.  A protocol selects a registered
profile and input kind; unregistered analyses are rejected before any output
is written.  Version 1 exposes the checked GJP Brier-monitor vertical slice.
Future CSV or Parquet adapters must register their own theorem-backed profile
rather than inheriting the GJP verification badge.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Iterable

import formalslt_certificate as certificate_engine
import formalslt_brier_certificate as tabular_certificate
import formalslt_brier_tabular as tabular_brier
import verify_formalslt_brier_tabular as tabular_replay


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL_SCHEMA = "formalslt.certify-protocol.v1"
GJP_INPUT_KIND = "gjp-replay-artifact-directory"
GJP_CLAIM_SCOPE = "posterior-averaged encountered conditional prefix Brier risk"
GJP_COVERAGE_USE = "RETROSPECTIVE_FIXED_CATALOG_ONLY"
DEFAULT_PROTOCOL = (
    ROOT / "applications/brier_monitor/gjp-compact-certificate-protocol-v1.json"
)

PROFILE_REGISTRY: dict[str, dict[str, str]] = {
    certificate_engine.PROFILE: {
        "analysis": "brier_monitor",
        "input_kind": GJP_INPUT_KIND,
        "claim_scope": GJP_CLAIM_SCOPE,
        "coverage_use": GJP_COVERAGE_USE,
        "status": "SUPPORTED",
    }
}

AVAILABLE_PROFILES: dict[str, dict[str, str]] = {
    **PROFILE_REGISTRY,
    tabular_certificate.PROFILE: {
        "analysis": "brier_monitor",
        "input_kind": "chronological-scaled-integer-csv-or-parquet",
        "claim_scope": tabular_brier.CLAIM_QUANTITY,
        "coverage_use": "PROTOCOL_BOUND_PRE_OUTCOME_PREDICTIONS",
        "status": "SUPPORTED",
    },
}


class ToolError(ValueError):
    """Raised when a command would exceed a registered certificate profile."""


def _require_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        raise ToolError(
            f"{label} keys mismatch; missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def _require(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise ToolError(f"{label} mismatch: expected {expected!r}, got {actual!r}")


def load_protocol(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        protocol, raw = certificate_engine.load_canonical_json(path, "certificate protocol")
    except certificate_engine.CertificateError as error:
        raise ToolError(str(error)) from error
    _require_keys(
        protocol,
        {
            "analysis",
            "certificate_profile",
            "claim_scope",
            "coverage_use",
            "expected_artifacts",
            "input_kind",
            "protocol_id",
            "schema_version",
        },
        "protocol",
    )
    _require(protocol["schema_version"], PROTOCOL_SCHEMA, "protocol schema")
    profile_name = protocol["certificate_profile"]
    if profile_name not in PROFILE_REGISTRY:
        supported = ", ".join(sorted(PROFILE_REGISTRY))
        raise ToolError(
            f"unsupported certificate profile {profile_name!r}; supported: {supported}"
        )
    profile = PROFILE_REGISTRY[profile_name]
    for key in ("analysis", "input_kind", "claim_scope", "coverage_use"):
        _require(protocol[key], profile[key], f"protocol {key}")
    expected = protocol["expected_artifacts"]
    if not isinstance(expected, dict):
        raise ToolError("protocol expected_artifacts must be an object")
    _require_keys(
        expected,
        {"manifest_sha256", "protocol_sha256", "receipt_sha256", "stream_sha256"},
        "protocol expected_artifacts",
    )
    for key, value in expected.items():
        if not isinstance(value, str) or len(value) != 64 or any(
            character not in "0123456789abcdef" for character in value
        ):
            raise ToolError(f"protocol expected_artifacts.{key} must be lowercase SHA-256")
    if not isinstance(protocol["protocol_id"], str) or not protocol["protocol_id"]:
        raise ToolError("protocol_id must be a nonempty string")
    return protocol, raw


def validate_profile_artifacts(
    protocol: dict[str, Any], artifacts: dict[str, Any]
) -> None:
    expected = protocol["expected_artifacts"]
    actual = {
        "manifest_sha256": artifacts["manifest_sha256"],
        "protocol_sha256": artifacts["receipt"].get("protocol_sha256"),
        "receipt_sha256": artifacts["receipt_sha256"],
        "stream_sha256": artifacts["stream_sha256"],
    }
    for key, expected_value in expected.items():
        _require(actual[key], expected_value, f"profile artifact {key}")


def _output_paths(directory: Path) -> tuple[Path, Path]:
    return directory / "gjp-certificate-v1.json", directory / "gjp-monitor-trace-v1.json"


def _protocol_schema(path: Path) -> str:
    if path.suffix.lower() in {".yaml", ".yml"}:
        try:
            protocol, _raw = tabular_brier.load_protocol(path)
        except tabular_brier.PreparationError as error:
            raise ToolError(str(error)) from error
        return str(protocol["schema_version"])
    try:
        raw = path.read_bytes()
        protocol = json.loads(raw.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ToolError(f"cannot read protocol schema: {path}") from error
    if not isinstance(protocol, dict) or not isinstance(protocol.get("schema_version"), str):
        raise ToolError("protocol must contain a string schema_version")
    return protocol["schema_version"]


def certify(args: argparse.Namespace) -> int:
    schema = _protocol_schema(args.protocol)
    if schema == tabular_brier.PROTOCOL_SCHEMA:
        try:
            certificate_path = tabular_certificate.issue(
                args.protocol, args.data, args.out.resolve()
            )
            certificate = tabular_certificate.verify(certificate_path)
        except tabular_certificate.CertificateError as error:
            raise ToolError(str(error)) from error
        print("FormalSLT compact Brier certificate: PASS")
        print(f"Observed Brier loss:                {certificate['statistics']['posterior_empirical_brier_risk']}")
        print(f"Certified upper bound:              {certificate['claim']['upper_bound']}")
        print("Continuous monitoring:              allowed")
        print("Post-data model selection:           accounted for")
        print(f"Prediction provenance:              {certificate['data']['provenance']['tier']}")
        print("Independent data replay:             PASS")
        print("Lean kernel:                         PASS")
        print(f"Wrote:                               {certificate_path}")
        return 0
    if schema != PROTOCOL_SCHEMA:
        raise ToolError(f"unsupported protocol schema: {schema!r}")
    protocol, _raw = load_protocol(args.protocol)
    if protocol["input_kind"] != GJP_INPUT_KIND:
        raise ToolError(f"unsupported input kind: {protocol['input_kind']}")
    try:
        artifacts = certificate_engine.validate_artifacts(args.data)
        certificate_engine.validate_tracked_replay_pins(artifacts)
    except certificate_engine.CertificateError as error:
        raise ToolError(str(error)) from error
    validate_profile_artifacts(protocol, artifacts)

    output = args.out.resolve()
    certificate_path, trace_path = _output_paths(output)
    existing = [path for path in (certificate_path, trace_path) if path.exists()]
    if existing:
        raise ToolError(
            "refusing to overwrite existing output: " + ", ".join(str(path) for path in existing)
        )
    output.mkdir(parents=True, exist_ok=True)
    issue_args = argparse.Namespace(
        artifacts=args.data,
        out_certificate=certificate_path,
        out_trace=trace_path,
        run_lean=True,
        skip_tracked_pin_check=False,
    )
    try:
        return certificate_engine.issue(issue_args)
    except certificate_engine.CertificateError as error:
        raise ToolError(str(error)) from error


def verify(args: argparse.Namespace) -> int:
    try:
        certificate_value = json.loads(args.certificate.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ToolError(f"cannot read certificate: {args.certificate}") from error
    if isinstance(certificate_value, dict) and certificate_value.get(
        "certificate_profile"
    ) == tabular_certificate.PROFILE:
        if args.skip_lean:
            raise ToolError("--skip-lean is not supported for compact tabular certificates")
        try:
            certificate = tabular_certificate.verify(
                args.certificate, args.protocol, args.data
            )
        except tabular_certificate.CertificateError as error:
            raise ToolError(str(error)) from error
        replay = "PASS" if args.protocol is not None else "NOT RERUN"
        print("FormalSLT compact Brier certificate: PASS")
        print(f"Certified upper bound:              {certificate['claim']['upper_bound']}")
        print(f"Independent data replay:            {replay}")
        print("Lean kernel:                         PASS")
        return 0
    trace = args.trace or args.certificate.with_name("gjp-monitor-trace-v1.json")
    verify_args = argparse.Namespace(
        certificate=args.certificate,
        trace=trace,
        artifacts=args.data,
        skip_lean=args.skip_lean,
    )
    try:
        return certificate_engine.verify(verify_args)
    except certificate_engine.CertificateError as error:
        raise ToolError(str(error)) from error


def show(args: argparse.Namespace) -> int:
    try:
        value = json.loads(args.certificate.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ToolError(f"cannot read certificate: {args.certificate}") from error
    if isinstance(value, dict) and value.get("certificate_profile") == tabular_certificate.PROFILE:
        print(f"Profile:                 {value['certificate_profile']}")
        print(f"Observations:            {value['data']['observations']}")
        print(f"Observed Brier loss:     {value['statistics']['posterior_empirical_brier_risk']}")
        print(f"Certified upper bound:   {value['claim']['upper_bound']}")
        print(f"Provenance:              {value['data']['provenance']['tier']}")
        print(f"Independent replay:      {value['replay']['independent_replay']}")
        print(f"Lean kernel:             {value['kernel']['result']}")
        return 0
    try:
        return certificate_engine.show(argparse.Namespace(certificate=args.certificate))
    except certificate_engine.CertificateError as error:
        raise ToolError(str(error)) from error


def profiles(args: argparse.Namespace) -> int:
    if args.json:
        print(json.dumps(AVAILABLE_PROFILES, indent=2, sort_keys=True))
        return 0
    for name, profile in sorted(AVAILABLE_PROFILES.items()):
        print(f"{name}\t{profile['status']}\t{profile['input_kind']}")
    return 0


def prepare(args: argparse.Namespace) -> int:
    if args.out.exists():
        raise ToolError(f"refusing to overwrite existing output: {args.out}")
    try:
        preparation = tabular_brier.prepare(args.protocol, args.data)
        tabular_brier.atomic_write(args.out, tabular_brier.canonical_json_bytes(preparation))
    except tabular_brier.PreparationError as error:
        raise ToolError(str(error)) from error
    statistics = preparation["statistics"]
    print("FormalSLT tabular preparation")
    print(f"Observations:                {preparation['data']['observations']}")
    print(f"Observed Brier loss:         {statistics['posterior_empirical_brier_risk']}")
    print(f"Candidate boundary upper:   {preparation['candidate']['boundary_upper']}")
    print("Certificate verification:   NOT ISSUED")
    print(f"Wrote:                       {args.out}")
    return 0


def verify_preparation(args: argparse.Namespace) -> int:
    try:
        preparation = tabular_replay.verify(args.preparation, args.protocol, args.data)
    except tabular_replay.ReplayError as error:
        raise ToolError(str(error)) from error
    print("FormalSLT tabular replay:     PASS")
    print(f"Observations:                 {preparation['data']['observations']}")
    print(
        "Observed Brier loss:        "
        + preparation["statistics"]["posterior_empirical_brier_risk"]
    )
    print("Certificate verification:    NOT ISSUED")
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(
        prog="formalslt",
        description="Issue and verify registered FormalSLT statistical certificates.",
    )
    commands = root.add_subparsers(dest="command", required=True)

    profiles_parser = commands.add_parser("profiles", help="list theorem-backed profiles")
    profiles_parser.add_argument("--json", action="store_true")
    profiles_parser.set_defaults(handler=profiles)

    prepare_parser = commands.add_parser(
        "prepare",
        help="prepare exact CSV or Parquet Brier summaries without claiming certification",
    )
    prepare_parser.add_argument("protocol", type=Path)
    prepare_parser.add_argument("data", type=Path)
    prepare_parser.add_argument("--out", type=Path, required=True)
    prepare_parser.set_defaults(handler=prepare)

    replay_parser = commands.add_parser(
        "verify-preparation",
        help="independently replay a tabular preparation",
    )
    replay_parser.add_argument("preparation", type=Path)
    replay_parser.add_argument("protocol", type=Path)
    replay_parser.add_argument("data", type=Path)
    replay_parser.set_defaults(handler=verify_preparation)

    certify_parser = commands.add_parser("certify", help="issue a registered certificate")
    certify_parser.add_argument("protocol", type=Path, nargs="?", default=DEFAULT_PROTOCOL)
    certify_parser.add_argument("data", type=Path, help="profile-specific input")
    certify_parser.add_argument("--out", type=Path, required=True)
    certify_parser.set_defaults(handler=certify)

    verify_parser = commands.add_parser("verify", help="verify an issued certificate")
    verify_parser.add_argument("certificate", type=Path)
    verify_parser.add_argument("--trace", type=Path)
    verify_parser.add_argument("--data", type=Path, help="optional full artifact binding")
    verify_parser.add_argument("--protocol", type=Path, help="protocol for independent tabular replay")
    verify_parser.add_argument("--skip-lean", action="store_true")
    verify_parser.set_defaults(handler=verify)

    show_parser = commands.add_parser("show", help="print a certificate summary")
    show_parser.add_argument("certificate", type=Path)
    show_parser.set_defaults(handler=show)
    return root


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(list(argv) if argv is not None else None)
    try:
        return int(args.handler(args))
    except ToolError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
