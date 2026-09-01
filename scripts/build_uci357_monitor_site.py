#!/usr/bin/env python3
"""Build the static UCI-357 monitor trace and hash-bound site assets."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

import formalslt_brier_certificate as certificate_engine
import formalslt_brier_summary as summary_engine
import formalslt_brier_tabular as tabular_engine


ROOT = Path(__file__).resolve().parents[1]
APPLICATION = ROOT / "applications/brier_monitor"
SOURCE_DIRECTORY = APPLICATION / "generated/uci357-certificate-v1"
SOURCE_CERTIFICATE = SOURCE_DIRECTORY / "certificate.json"
SOURCE_EVIDENCE = APPLICATION / "generated/uci357-certificate-evidence-v1.json"
SOURCE_PREDICTIONS = APPLICATION / "generated/uci357-monitor-predictions-v1.csv"
SITE = ROOT / "docs/site/monitor/occupancy"
TRACE = SITE / "trace.json"
CERTIFICATE = SITE / "certificate.json"
EVIDENCE = SITE / "evidence.json"
SUMMARY = SITE / "summary.json"
MANIFEST = SITE / "manifest.json"
TRACE_SCHEMA = "formalslt.monitor.uci357-display-trace.v1"
MANIFEST_SCHEMA = "formalslt.monitor.uci357-site-manifest.v1"
SAMPLE_STRIDE = 16
MODEL_IDS = ("constant_train_prevalence", "logistic_all_sensor")
MODEL_COLUMNS = {
    "constant_train_prevalence": "constant_train_prevalence_q",
    "logistic_all_sensor": "logistic_all_sensor_q",
}


class SiteBuildError(ValueError):
    """Raised when the display trace disagrees with the checked artifact."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    try:
        return sha256_bytes(path.read_bytes())
    except OSError as error:
        raise SiteBuildError(f"cannot hash {path}") from error


def fraction(value: str) -> Fraction:
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise SiteBuildError(f"invalid rational {value!r}") from error


def decimal_text(value: Fraction, places: int = 8, *, upward: bool = False) -> str:
    scale = 10**places
    numerator = value.numerator * scale
    if upward:
        scaled = (numerator + value.denominator - 1) // value.denominator
    else:
        scaled = (2 * numerator + value.denominator) // (2 * value.denominator)
    whole, decimal = divmod(scaled, scale)
    return f"{whole}.{decimal:0{places}d}"


def _model_loss(prediction: int, outcome: int, scale: int) -> Fraction:
    return (Fraction(prediction, scale) - outcome) ** 2


def build_trace() -> dict[str, Any]:
    certificate = json.loads(SOURCE_CERTIFICATE.read_bytes())
    evidence = json.loads(SOURCE_EVIDENCE.read_bytes())
    if certificate["kernel"]["result"] != "PASS":
        raise SiteBuildError("source certificate is not kernel-checked")
    if certificate["replay"]["independent_replay"] != "PASS":
        raise SiteBuildError("source certificate lacks independent replay")
    if certificate["data"]["provenance"]["tier"] != "AUDITED":
        raise SiteBuildError("source certificate provenance is not AUDITED")

    prediction_scale = certificate["data"]["prediction_scale"]
    prefix_loss = {model_id: Fraction(0) for model_id in MODEL_IDS}
    prefix_variation = {model_id: Fraction(0) for model_id in MODEL_IDS}
    points: list[dict[str, Any]] = []
    previous_time = 0
    selection_switches = 0
    previous_selection: str | None = None

    with SOURCE_PREDICTIONS.open(newline="", encoding="ascii") as handle:
        reader = csv.DictReader(handle)
        for n, row in enumerate(reader, start=1):
            time = int(row["sequence_index"])
            outcome = int(row["outcome"])
            if time != previous_time + 1 or outcome not in (0, 1):
                raise SiteBuildError("display replay encountered a malformed row")
            previous_time = time
            for model_id in MODEL_IDS:
                prediction = int(row[MODEL_COLUMNS[model_id]])
                loss = _model_loss(prediction, outcome, prediction_scale)
                predictor = Fraction(1, 2) if n == 1 else prefix_loss[model_id] / (n - 1)
                prefix_variation[model_id] += tabular_engine.ceil_to_grid(
                    (loss - predictor) ** 2,
                    tabular_engine.QUADRATIC_VARIATION_GRID,
                )
                prefix_loss[model_id] += loss
            selected = min(MODEL_IDS, key=lambda model_id: prefix_loss[model_id])
            if previous_selection is not None and selected != previous_selection:
                selection_switches += 1
            previous_selection = selected
            if n < 4 or (n % SAMPLE_STRIDE != 0 and n != certificate["data"]["observations"]):
                continue
            empirical = prefix_loss[selected] / n
            arithmetic_upper = empirical + (
                Fraction(7, 10)
                + Fraction(61, 20)
                + Fraction(1, 5) * prefix_variation[selected]
            ) / (Fraction(1, 2) * n)
            boundary = certificate_engine.strict_decimal_ceiling(arithmetic_upper)
            points.append(
                {
                    "boundary_upper_decimal": decimal_text(boundary, 6, upward=True),
                    "constant_brier_decimal": decimal_text(
                        prefix_loss["constant_train_prevalence"] / n
                    ),
                    "logistic_brier_decimal": decimal_text(
                        prefix_loss["logistic_all_sensor"] / n
                    ),
                    "n": n,
                    "selected_brier_decimal": decimal_text(empirical),
                    "selected_model": selected,
                }
            )

    if previous_time != certificate["data"]["observations"]:
        raise SiteBuildError("display replay horizon disagrees with the certificate")
    final = points[-1]
    expected_empirical = fraction(
        certificate["statistics"]["posterior_empirical_brier_risk"]
    )
    expected_bound = fraction(certificate["claim"]["upper_bound"])
    if final["selected_model"] != evidence["selection"]["winner"]:
        raise SiteBuildError("display replay selected a different final model")
    if final["selected_brier_decimal"] != decimal_text(expected_empirical):
        raise SiteBuildError("display replay empirical risk mismatch")
    if final["boundary_upper_decimal"] != decimal_text(expected_bound, 6, upward=True):
        raise SiteBuildError("display replay boundary mismatch")
    return {
        "artifact_status": "DISPLAY REPLAY; FINAL POINT KERNEL CHECKED",
        "certificate_sha256": sha256_file(SOURCE_CERTIFICATE),
        "dataset": {
            "doi": evidence["data"]["dataset_doi"],
            "name": "UCI Occupancy Detection",
        },
        "final": final,
        "points": points,
        "sample_stride": SAMPLE_STRIDE,
        "schema_version": TRACE_SCHEMA,
        "selection_switches": selection_switches,
        "source_prediction_sha256": sha256_file(SOURCE_PREDICTIONS),
    }


def build_assets() -> dict[Path, bytes]:
    certificate_raw = SOURCE_CERTIFICATE.read_bytes()
    certificate = json.loads(certificate_raw)
    evidence = json.loads(SOURCE_EVIDENCE.read_bytes())
    summary = summary_engine.certificate_summary(
        certificate,
        certificate_sha256=sha256_bytes(certificate_raw),
        selected_model=evidence["selection"]["winner"],
    )
    return {
        CERTIFICATE: certificate_raw,
        EVIDENCE: SOURCE_EVIDENCE.read_bytes(),
        SUMMARY: canonical_json_bytes(summary),
        TRACE: canonical_json_bytes(build_trace()),
    }


def build_manifest(assets: dict[Path, bytes]) -> bytes:
    files = []
    for path in (SITE / "monitor.css", SITE / "monitor.js"):
        files.append(
            {
                "path": path.relative_to(SITE).as_posix(),
                "sha256": sha256_file(path),
            }
        )
    files.extend(
        {
            "path": path.relative_to(SITE).as_posix(),
            "sha256": sha256_bytes(raw),
        }
        for path, raw in assets.items()
    )
    return canonical_json_bytes(
        {
            "files": files,
            "schema_version": MANIFEST_SCHEMA,
            "source_html_template": {
                "path": "index.html",
                "sha256": sha256_file(SITE / "index.html"),
            },
            "source_certificate_commit": json.loads(SOURCE_CERTIFICATE.read_bytes())[
                "formal_slt"
            ]["commit"],
        }
    )


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
        Path(temporary).unlink(missing_ok=True)


def run(*, check: bool) -> None:
    assets = build_assets()
    manifest_raw = build_manifest(assets)
    expected = {**assets, MANIFEST: manifest_raw}
    for path, raw in expected.items():
        if check:
            if not path.is_file() or path.read_bytes() != raw:
                raise SiteBuildError(f"stale monitor site asset: {path}")
        else:
            _atomic_write(path, raw)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args(list(argv) if argv is not None else None)
    try:
        run(check=arguments.check)
    except (
        OSError,
        KeyError,
        ValueError,
        json.JSONDecodeError,
    ) as error:
        print(f"ERROR: UCI monitor site refused: {error}")
        return 1
    print("UCI-357 monitor site: PASS" if arguments.check else "UCI-357 monitor site built")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
