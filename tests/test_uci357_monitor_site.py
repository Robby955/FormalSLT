from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
import build_uci357_monitor_site as site_builder  # noqa: E402


def test_display_trace_replays_checked_final_point() -> None:
    trace = site_builder.build_trace()
    certificate = json.loads(site_builder.SOURCE_CERTIFICATE.read_bytes())
    evidence = json.loads(site_builder.SOURCE_EVIDENCE.read_bytes())

    assert trace["schema_version"] == site_builder.TRACE_SCHEMA
    assert trace["artifact_status"] == (
        "DISPLAY REPLAY; FINAL POINT KERNEL CHECKED"
    )
    assert len(trace["points"]) == 514
    assert trace["points"][-1] == trace["final"]
    assert trace["final"] == {
        "boundary_upper_decimal": "0.073268",
        "constant_brier_decimal": "0.16532193",
        "logistic_brier_decimal": "0.06119769",
        "n": 8_224,
        "selected_brier_decimal": "0.06119769",
        "selected_model": "logistic_all_sensor",
    }
    assert Fraction(certificate["claim"]["upper_bound"]) == Fraction(
        trace["final"]["boundary_upper_decimal"]
    )
    assert evidence["selection"]["winner"] == trace["final"]["selected_model"]


def test_site_assets_are_current_and_hash_bound() -> None:
    site_builder.run(check=True)
    manifest_raw = site_builder.MANIFEST.read_bytes()
    manifest = json.loads(manifest_raw)

    assert manifest_raw == site_builder.canonical_json_bytes(manifest)
    assert manifest["schema_version"] == site_builder.MANIFEST_SCHEMA
    assert manifest["source_certificate_commit"] == (
        "6c6101012f38b902d30582a963a911a20518bfc3"
    )
    assert manifest["source_html_template"] == {
        "path": "index.html",
        "sha256": hashlib.sha256(site_builder.SITE.joinpath("index.html").read_bytes()).hexdigest(),
    }
    for entry in manifest["files"]:
        path = site_builder.SITE / entry["path"]
        assert path.is_file()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == entry["sha256"]


def test_monitor_copy_keeps_claim_scope_and_source_binding() -> None:
    html = site_builder.SITE.joinpath("index.html").read_text(encoding="utf-8")
    landing_html = site_builder.ROOT.joinpath("docs/site/index.html").read_text(
        encoding="utf-8"
    )
    javascript = site_builder.SITE.joinpath("monitor.js").read_text(encoding="utf-8")
    stylesheet = site_builder.SITE.joinpath("monitor.css").read_text(encoding="utf-8")

    assert 'name="viewport"' in html
    assert "__FORMALSLT_SOURCE_REF__" in html
    assert "posterior-averaged conditional Brier risk" in html
    assert "does not establish future occupancy" in html
    assert "data-certificate-status" in html
    assert "data-scrubber" in html
    assert "site-manifest digest mismatch" in javascript
    assert "certificate is not bound to this evidence file" in javascript
    assert "overflow: hidden" not in stylesheet
    assert 'href="monitor/occupancy/">Open the checked monitor</a>' in landing_html
