#!/usr/bin/env python3
"""Build the audited UCI-357 prediction stream and compact certificate inputs.

The source protocol fixes the archive, chronology, split, feature allowlist,
quantization, and baseline training rule.  This script trains on the frozen
training prefix, emits predictions for the frozen monitor suffix, selects the
lower-Brier model after observing that suffix, and records that post-data
selection explicitly.  FormalSLT charges the resulting point posterior against
the uniform prior; it does not treat the selected model as preselected.

This is a retrospective worked application.  The UCI archive does not prove
real-time label delay, future risk, or deployment performance.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import sys
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Sequence

import formalslt_brier_certificate as certificate_engine
import formalslt_brier_tabular as tabular_engine
import prepare_brier_monitor_uci357 as source_protocol


ROOT = Path(__file__).resolve().parents[1]
APPLICATION = ROOT / "applications/brier_monitor"
PREDICTIONS = APPLICATION / "generated/uci357-monitor-predictions-v1.csv"
EVIDENCE = APPLICATION / "generated/uci357-certificate-evidence-v1.json"
PROTOCOL = APPLICATION / "uci357-certificate-protocol-v1.json"
CERTIFICATE_DIRECTORY = APPLICATION / "generated/uci357-certificate-v1"
CERTIFICATE = CERTIFICATE_DIRECTORY / certificate_engine.CERTIFICATE_NAME
RUNTIME_REQUIREMENTS = ROOT / "requirements-uci357.txt"
EVIDENCE_SCHEMA = "formalslt.brier-monitor.uci357-certificate-evidence.v1"
PROTOCOL_ID = "uci357-occupancy-hard-selection-v1"
MODEL_ORDER = ("constant_train_prevalence", "logistic_all_sensor")
PREDICTION_COLUMNS = {
    "constant_train_prevalence": "constant_train_prevalence_q",
    "logistic_all_sensor": "logistic_all_sensor_q",
}
EXPECTED_NUMPY_VERSION = "2.4.4"
EXPECTED_SKLEARN_VERSION = "1.9.0"


class BuildError(ValueError):
    """Raised when the frozen application cannot be reproduced exactly."""


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True, allow_nan=False)
        + "\n"
    ).encode()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise BuildError(f"cannot hash {path}") from error
    return digest.hexdigest()


def rational_text(value: Fraction) -> str:
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def choose_winner(loss_sums: dict[str, int]) -> str:
    if set(loss_sums) != set(MODEL_ORDER):
        raise BuildError("loss catalog does not match the frozen model order")
    if any(isinstance(value, bool) or not isinstance(value, int) or value < 0 for value in loss_sums.values()):
        raise BuildError("model loss sums must be nonnegative integers")
    return min(MODEL_ORDER, key=lambda model_id: (loss_sums[model_id], MODEL_ORDER.index(model_id)))


def _load_source() -> tuple[
    dict[str, Any],
    bytes,
    source_protocol.PreparedDataset,
    dict[str, Any],
]:
    protocol, protocol_raw = source_protocol._load_protocol(source_protocol.DEFAULT_PROTOCOL)
    try:
        archive_raw = source_protocol.DEFAULT_ARCHIVE.read_bytes()
    except OSError as error:
        raise BuildError(
            "the pinned UCI archive is absent; run "
            "`python3 scripts/prepare_brier_monitor_uci357.py --download`"
        ) from error
    prepared = source_protocol.prepare_archive(archive_raw, protocol)
    manifest = source_protocol.build_manifest(
        prepared,
        protocol,
        protocol_raw,
        Path(source_protocol.__file__).read_bytes(),
    )
    expected_manifest = source_protocol.canonical_json_bytes(manifest)
    if expected_manifest != source_protocol.DEFAULT_MANIFEST.read_bytes():
        raise BuildError("the tracked UCI source manifest is stale")
    return protocol, protocol_raw, prepared, manifest


def _fit_predictions(
    prepared: source_protocol.PreparedDataset,
    protocol: dict[str, Any],
) -> tuple[dict[str, list[int]], list[int], dict[str, Any]]:
    try:
        import numpy as np
        import sklearn  # type: ignore[import-untyped]
        from sklearn.exceptions import ConvergenceWarning  # type: ignore[import-untyped]
        from sklearn.linear_model import LogisticRegression  # type: ignore[import-untyped]
        from sklearn.pipeline import Pipeline  # type: ignore[import-untyped]
        from sklearn.preprocessing import StandardScaler  # type: ignore[import-untyped]
    except ImportError as error:
        raise BuildError("NumPy and scikit-learn are required for the UCI demo") from error
    if np.__version__ != EXPECTED_NUMPY_VERSION or sklearn.__version__ != EXPECTED_SKLEARN_VERSION:
        raise BuildError(
            "UCI model runtime mismatch; install requirements-uci357.txt "
            f"(found NumPy {np.__version__}, scikit-learn {sklearn.__version__})"
        )

    observations = prepared.observations
    slices = source_protocol.split_slices(protocol)
    train_start, train_stop = slices["train"]
    monitor_start, monitor_stop = slices["monitor"]
    train_rows = observations[train_start:train_stop]
    monitor_rows = observations[monitor_start:monitor_stop]

    def matrix(rows: Sequence[source_protocol.Observation]) -> Any:
        return np.asarray(
            [
                [
                    float(row.temperature),
                    float(row.humidity),
                    float(row.light),
                    float(row.co2),
                ]
                for row in rows
            ],
            dtype=np.float64,
        )

    def outcomes(rows: Sequence[source_protocol.Observation]) -> Any:
        return np.asarray([row.occupancy for row in rows], dtype=np.int64)

    train_outcomes = outcomes(train_rows)
    logistic = Pipeline(
        steps=[
            ("scale", StandardScaler()),
            (
                "model",
                LogisticRegression(
                    C=1.0,
                    max_iter=2000,
                    random_state=0,
                    solver="lbfgs",
                    tol=1e-12,
                ),
            ),
        ]
    )
    source_protocol._fit_rejecting_warning(
        logistic,
        matrix(train_rows),
        train_outcomes,
        ConvergenceWarning,
    )
    prevalence = Fraction(int(train_outcomes.sum()), len(train_outcomes))
    constant_prediction = source_protocol.quantize_probability(prevalence)
    logistic_predictions = [
        source_protocol.quantize_probability(float(value))
        for value in logistic.predict_proba(matrix(monitor_rows))[:, 1]
    ]
    predictions = {
        "constant_train_prevalence": [constant_prediction] * len(monitor_rows),
        "logistic_all_sensor": logistic_predictions,
    }
    monitor_outcomes = [row.occupancy for row in monitor_rows]
    model = logistic.named_steps["model"]
    scaler = logistic.named_steps["scale"]
    metadata = {
        "constant_train_prevalence": {
            "prediction_quantized": constant_prediction,
            "training_prevalence": rational_text(prevalence),
        },
        "logistic_all_sensor": {
            "coefficient_repr": [repr(float(value)) for value in model.coef_[0]],
            "feature_allowlist": ["Temperature", "Humidity", "Light", "CO2"],
            "intercept_repr": repr(float(model.intercept_[0])),
            "parameters": {
                "C": "1",
                "max_iter": 2000,
                "random_state": 0,
                "solver": "lbfgs",
                "tol": "1e-12",
            },
            "scaler_mean_repr": [repr(float(value)) for value in scaler.mean_],
            "scaler_scale_repr": [repr(float(value)) for value in scaler.scale_],
        },
        "runtime_requirements": {
            "numpy": np.__version__,
            "scikit_learn": sklearn.__version__,
        },
    }
    return predictions, monitor_outcomes, metadata


def _prediction_stream_bytes(
    predictions: dict[str, list[int]],
    outcomes: list[int],
) -> bytes:
    if any(len(predictions[model_id]) != len(outcomes) for model_id in MODEL_ORDER):
        raise BuildError("prediction vectors do not match the monitor horizon")
    buffer = io.StringIO(newline="")
    writer = csv.writer(buffer, lineterminator="\n")
    writer.writerow(
        [
            "sequence_index",
            "outcome",
            PREDICTION_COLUMNS["constant_train_prevalence"],
            PREDICTION_COLUMNS["logistic_all_sensor"],
        ]
    )
    for index, outcome in enumerate(outcomes, start=1):
        writer.writerow(
            [
                index,
                outcome,
                predictions["constant_train_prevalence"][index - 1],
                predictions["logistic_all_sensor"][index - 1],
            ]
        )
    return buffer.getvalue().encode("ascii")


def _loss_sums(
    predictions: dict[str, list[int]],
    outcomes: list[int],
) -> dict[str, int]:
    return {
        model_id: sum(
            source_protocol.brier_loss_numerator(prediction, outcome)
            for prediction, outcome in zip(
                predictions[model_id],
                outcomes,
                strict=True,
            )
        )
        for model_id in MODEL_ORDER
    }


def build_inputs() -> dict[Path, bytes]:
    source, source_raw, prepared, source_manifest = _load_source()
    predictions, outcomes, model_metadata = _fit_predictions(prepared, source)
    prediction_raw = _prediction_stream_bytes(predictions, outcomes)
    loss_sums = _loss_sums(predictions, outcomes)
    winner = choose_winner(loss_sums)
    monitor_manifest = next(
        split for split in source_manifest["splits"] if split["name"] == "monitor"
    )
    evidence = {
        "artifact_status": "AUDITED RETROSPECTIVE DEMONSTRATION",
        "data": {
            "archive_sha256": prepared.archive_sha256,
            "canonical_stream_sha256": source_manifest["canonical_stream"]["sha256"],
            "dataset_doi": source["dataset"]["doi"],
            "dataset_license": source["dataset"]["license"],
            "monitor_count": len(outcomes),
            "monitor_first_timestamp": monitor_manifest["first_timestamp"],
            "monitor_last_timestamp": monitor_manifest["last_timestamp"],
            "monitor_split_sha256": monitor_manifest["sha256"],
            "prediction_stream_sha256": sha256_bytes(prediction_raw),
        },
        "models": model_metadata,
        "nonclaims": [
            "the analysis was assembled retrospectively and is not a prospective study",
            "the UCI archive does not prove real-time label delay",
            "the certificate concerns encountered conditional prefix risk, not future or deployment risk",
            "Lean checks the compact bound arithmetic, while two Python implementations replay the rows",
        ],
        "schema_version": EVIDENCE_SCHEMA,
        "selection": {
            "loss": "quantized Brier loss",
            "loss_numerator_sums": loss_sums,
            "model_order": list(MODEL_ORDER),
            "posterior": {
                model_id: "1" if model_id == winner else "0"
                for model_id in MODEL_ORDER
            },
            "prior": {model_id: "1/2" for model_id in MODEL_ORDER},
            "rule": "minimum monitor-prefix cumulative Brier loss; model order breaks ties",
            "timing": "POST_DATA",
            "winner": winner,
        },
        "source_bindings": {
            "builder": {
                "path": Path(__file__).resolve().relative_to(ROOT).as_posix(),
                "sha256": sha256_file(Path(__file__).resolve()),
            },
            "source_manifest": {
                "path": source_protocol.DEFAULT_MANIFEST.relative_to(ROOT).as_posix(),
                "sha256": sha256_file(source_protocol.DEFAULT_MANIFEST),
            },
            "source_protocol": {
                "path": source_protocol.DEFAULT_PROTOCOL.relative_to(ROOT).as_posix(),
                "sha256": sha256_bytes(source_raw),
            },
            "runtime_requirements": {
                "path": RUNTIME_REQUIREMENTS.relative_to(ROOT).as_posix(),
                "sha256": sha256_file(RUNTIME_REQUIREMENTS),
            },
        },
    }
    evidence_raw = canonical_json_bytes(evidence)
    certificate_protocol = {
        "analysis": "brier_monitor",
        "claim": {"quantity": tabular_engine.CLAIM_QUANTITY},
        "data": {
            "input_format": "csv",
            "outcome_column": "outcome",
            "prediction_encoding": "scaled_integer",
            "prediction_scale": source_protocol.PROBABILITY_DENOMINATOR,
            "require_strict_time_order": True,
            "time_column": "sequence_index",
        },
        "models": [
            {"column": PREDICTION_COLUMNS[model_id], "id": model_id}
            for model_id in MODEL_ORDER
        ],
        "protocol_id": PROTOCOL_ID,
        "provenance": {
            "evidence_sha256": sha256_bytes(evidence_raw),
            "prediction_timing": "PRE_OUTCOME",
            "tier": "AUDITED",
        },
        "schema_version": tabular_engine.PROTOCOL_SCHEMA,
        "statistics": {
            "delta": "1/20",
            "posterior": evidence["selection"]["posterior"],
            "prior": evidence["selection"]["prior"],
            "tilt": "1/2",
            "wake": 0,
        },
    }
    return {
        PREDICTIONS: prediction_raw,
        EVIDENCE: evidence_raw,
        PROTOCOL: canonical_json_bytes(certificate_protocol),
    }


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with open(descriptor, "wb", closefd=True) as handle:
            handle.write(raw)
            handle.flush()
        Path(temporary).replace(path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def prepare_inputs(*, check: bool) -> None:
    expected = build_inputs()
    for path, raw in expected.items():
        if check:
            try:
                actual = path.read_bytes()
            except OSError as error:
                raise BuildError(f"missing tracked application input: {path}") from error
            if actual != raw:
                raise BuildError(f"tracked application input is stale: {path}")
        else:
            _atomic_write(path, raw)


def issue_certificate() -> Path:
    if CERTIFICATE_DIRECTORY.exists():
        raise BuildError(
            f"refusing to overwrite {CERTIFICATE_DIRECTORY}; verify it or remove it explicitly"
        )
    try:
        return certificate_engine.issue(PROTOCOL, PREDICTIONS, CERTIFICATE_DIRECTORY)
    except certificate_engine.CertificateError as error:
        raise BuildError(str(error)) from error


def verify_bundle() -> dict[str, Any]:
    prepare_inputs(check=True)
    evidence_raw = EVIDENCE.read_bytes()
    protocol, _ = tabular_engine.load_protocol(PROTOCOL)
    if protocol["provenance"]["evidence_sha256"] != sha256_bytes(evidence_raw):
        raise BuildError("certificate protocol does not bind the tracked evidence")
    try:
        return certificate_engine.verify(CERTIFICATE, PROTOCOL, PREDICTIONS)
    except certificate_engine.CertificateError as error:
        raise BuildError(str(error)) from error


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    mode = command.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true", help="write tracked certificate inputs")
    mode.add_argument("--issue", action="store_true", help="prepare inputs and issue the Lean certificate")
    mode.add_argument("--check", action="store_true", help="rebuild inputs and verify the tracked certificate")
    return command


def main(argv: Iterable[str] | None = None) -> int:
    arguments = parser().parse_args(list(argv) if argv is not None else None)
    try:
        if arguments.prepare:
            prepare_inputs(check=False)
            print(f"UCI-357 certificate inputs prepared: {PREDICTIONS.relative_to(ROOT)}")
        elif arguments.issue:
            prepare_inputs(check=False)
            certificate = issue_certificate()
            print(f"UCI-357 compact certificate issued: {certificate.relative_to(ROOT)}")
        else:
            certificate = verify_bundle()
            print("UCI-357 compact certificate: PASS")
            print(f"Observations:              {certificate['data']['observations']}")
            print(
                "Observed Brier loss:       "
                + certificate["statistics"]["posterior_empirical_brier_risk"]
            )
            print("Certified upper bound:     " + certificate["claim"]["upper_bound"])
    except (BuildError, OSError, tabular_engine.PreparationError) as error:
        print(f"ERROR: UCI-357 certificate refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
