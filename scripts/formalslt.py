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
import formalslt_brier_tabular as tabular_brier


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


def certify(args: argparse.Namespace) -> int:
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
        return certificate_engine.show(argparse.Namespace(certificate=args.certificate))
    except certificate_engine.CertificateError as error:
        raise ToolError(str(error)) from error


def profiles(args: argparse.Namespace) -> int:
    if args.json:
        print(json.dumps(PROFILE_REGISTRY, indent=2, sort_keys=True))
        return 0
    for name, profile in sorted(PROFILE_REGISTRY.items()):
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

    certify_parser = commands.add_parser("certify", help="issue a registered certificate")
    certify_parser.add_argument("protocol", type=Path, nargs="?", default=DEFAULT_PROTOCOL)
    certify_parser.add_argument("data", type=Path, help="profile-specific input")
    certify_parser.add_argument("--out", type=Path, required=True)
    certify_parser.set_defaults(handler=certify)

    verify_parser = commands.add_parser("verify", help="verify an issued certificate")
    verify_parser.add_argument("certificate", type=Path)
    verify_parser.add_argument("--trace", type=Path)
    verify_parser.add_argument("--data", type=Path, help="optional full artifact binding")
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
