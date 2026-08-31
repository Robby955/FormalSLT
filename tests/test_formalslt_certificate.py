from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from scripts import formalslt_certificate as certificate


def _receipt() -> dict[str, object]:
    trace_rows = []
    for n in range(4, 176):
        empirical = (
            certificate.EXPECTED_EMPIRICAL_RISK
            if n == 175
            else certificate.Fraction(1, 20)
        )
        upper = (
            certificate.EXPECTED_REPLAY_BOUND_UPPER
            if n == 175
            else certificate.Fraction(1, 2)
        )
        trace_rows.append(
            {
                "boundary_interval": {
                    "lower": certificate.rational_text(upper - certificate.Fraction(1, 10**9)),
                    "upper": certificate.rational_text(upper),
                },
                "horizon": n,
                "posterior_empirical_brier_risk": certificate.rational_text(empirical),
            }
        )
    return {
        "baselines": {"B3_anytime_valid": {"selected_by_time": trace_rows}},
        "calibration": {
            "posterior": {
                "exact_rational_weights": {
                    model: certificate.rational_text(weight)
                    for model, weight in certificate.EXPECTED_POSTERIOR.items()
                }
            }
        },
        "confidence_delta": certificate.rational_text(certificate.EXPECTED_DELTA),
        "implementation_commit": "1" * 40,
        "implementation_tree": "2" * 40,
        "monitor": {"observations": certificate.EXPECTED_HORIZON},
        "overall_preregistered_verdict": {
            "failed_win_condition_checks": ["B2_count_at_least_25"],
            "incomplete_controls": ["shuffled_time_control"],
            "status": "FAIL",
        },
        "protocol_sha256": "3" * 64,
        "selected_witness": {
            "boundary_interval": {
                "upper": certificate.rational_text(certificate.EXPECTED_REPLAY_BOUND_UPPER)
            },
            "posterior_empirical_brier_risk": certificate.rational_text(
                certificate.EXPECTED_EMPIRICAL_RISK
            ),
            "suffix_predictor_quadratic_variation": certificate.rational_text(
                certificate.EXPECTED_QUADRATIC_VARIATION
            ),
            "tilt": "1/2",
            "train_base_rate_brier_threshold": "1/5",
            "wake": 0,
        },
    }


def _artifacts() -> dict[str, object]:
    receipt = _receipt()
    return {
        "manifest": {
            "dataset": {
                "license": "CC0-1.0",
                "persistent_id": "doi:10.7910/DVN/BPCDH5",
                "version": "1.0",
            }
        },
        "manifest_bytes": 400,
        "manifest_sha256": "4" * 64,
        "receipt": receipt,
        "receipt_bytes": 500,
        "receipt_sha256": "5" * 64,
        "stream": {},
        "stream_bytes": 600,
        "stream_sha256": "6" * 64,
        "trace_rows": receipt["baselines"]["B3_anytime_valid"]["selected_by_time"],
    }


def _issued() -> tuple[dict[str, object], bytes, dict[str, object], bytes]:
    artifacts = _artifacts()
    trace = certificate.build_trace(artifacts)
    trace_raw = certificate.canonical_json_bytes(trace)
    lean_result = {
        "allowed_axioms": sorted(certificate.ALLOWED_AXIOMS),
        "command": "focused checker",
        "observed_axioms": sorted(certificate.ALLOWED_AXIOMS),
        "status": "PASS",
    }
    issued = certificate.build_certificate(artifacts, trace_raw, lean_result, "7" * 40)
    issued_raw = certificate.canonical_json_bytes(issued)
    return issued, issued_raw, trace, trace_raw


def test_compact_certificate_validates() -> None:
    issued, issued_raw, trace, trace_raw = _issued()
    certificate.validate_certificate(issued, issued_raw, trace, trace_raw)


def test_changed_kernel_bound_fails_closed() -> None:
    issued, _issued_raw, trace, trace_raw = _issued()
    changed = copy.deepcopy(issued)
    changed["claim"]["kernel_checked_upper_bound"] = "1/2"
    with pytest.raises(certificate.CertificateError, match="kernel bound mismatch"):
        certificate.validate_certificate(
            changed, certificate.canonical_json_bytes(changed), trace, trace_raw
        )


def test_changed_trace_fails_digest_binding() -> None:
    issued, issued_raw, trace, _trace_raw = _issued()
    changed = copy.deepcopy(trace)
    changed["points"][0]["boundary_upper_decimal"] = "0.49999999"
    with pytest.raises(certificate.CertificateError, match="trace digest mismatch"):
        certificate.validate_certificate(
            issued, issued_raw, changed, certificate.canonical_json_bytes(changed)
        )


def test_canonical_loader_rejects_float(tmp_path: Path) -> None:
    path = tmp_path / "bad.json"
    path.write_text('{"value": 0.1}\n', encoding="utf-8")
    with pytest.raises(certificate.CertificateError, match="floating-point"):
        certificate.load_canonical_json(path, "bad fixture")


def test_tracked_lean_replay_pins_are_current() -> None:
    assert certificate._lean_string_constant("streamSha256") == (
        "3e3f1985a5db7fd56faa77d395aa9b72568a19d21d963037816fdc78b503ec07"
    )
    assert certificate._lean_string_constant("receiptSha256") == (
        "9bb608bc559d261d62e05153f58a836121b791d712707b828280b44eaf2a4b11"
    )


def test_monitor_assets_use_no_inline_certificate_data() -> None:
    source = (certificate.ROOT / "docs/site/monitor/monitor.js").read_text(encoding="utf-8")
    assert 'fetch("gjp-certificate-v1.json"' in source
    assert certificate.rational_text(certificate.EXPECTED_EMPIRICAL_RISK) not in source
    json.loads(json.dumps({"source": source}))
