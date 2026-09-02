from __future__ import annotations

import hashlib
import json
import sys
from copy import deepcopy
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
import formalslt_brier_summary as summary_engine  # noqa: E402


CERTIFICATE = (
    ROOT
    / "applications/brier_monitor/generated/uci357-certificate-v1/certificate.json"
)


def test_uci_certificate_summary_has_exact_checked_decomposition() -> None:
    raw = CERTIFICATE.read_bytes()
    certificate = json.loads(raw)
    summary = summary_engine.certificate_summary(
        certificate,
        certificate_sha256=hashlib.sha256(raw).hexdigest(),
        selected_model="logistic_all_sensor",
    )

    assert summary["schema_version"] == summary_engine.SUMMARY_SCHEMA
    assert summary["artifact_status"] == summary_engine.CERTIFICATE_STATUS
    assert summary["certificate"]["sha256"] == hashlib.sha256(raw).hexdigest()
    assert summary["selected_model"] == "logistic_all_sensor"
    assert summary["verification"] == {
        "independent_replay": "PASS",
        "lean_kernel": "PASS",
        "scope": "derived view; exact values are bound to certificate.sha256",
    }
    assert summary["components"]["observed_risk"]["rational"] == (
        "2161547227007/35320733114400"
    )
    assert summary["components"]["selection_cost"]["rational"] == "7/41120"
    assert summary["components"]["confidence_cost"]["rational"] == "61/82240"
    assert summary["components"]["variation_cost"]["rational"] == (
        "252237278248593/22605959067074560"
    )
    assert summary["components"]["arithmetic_upper"]["rational"] == (
        "1422695048907004187305501/19417778380427805012787200"
    )
    assert summary["components"]["rounding_slack"]["rational"] == (
        "4210918862643982119731/12136111487767378132992000000"
    )
    assert summary["claim"]["upper_bound"]["percent_decimal"] == "7.3268000000"


def test_certificate_summary_refuses_inconsistent_arithmetic() -> None:
    raw = CERTIFICATE.read_bytes()
    certificate = json.loads(raw)
    tampered = deepcopy(certificate)
    tampered["statistics"]["rational_arithmetic_upper"] = "1/10"

    with pytest.raises(
        summary_engine.SummaryError,
        match="recorded arithmetic upper bound disagrees",
    ):
        summary_engine.certificate_summary(
            tampered,
            certificate_sha256=hashlib.sha256(raw).hexdigest(),
        )
