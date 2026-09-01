#!/usr/bin/env python3
"""Independently replay a FormalSLT tabular Brier preparation.

This verifier intentionally does not import ``formalslt_brier_tabular``.  It
parses the protocol and prediction file again, recomputes exact losses, the
fixed-grid conservative variation bound, and transcendental enclosures with a
separate implementation, reconstructs the canonical preparation, and rejects
the first mismatch it finds.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Iterator


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "scripts/formalslt_brier_tabular.py"
PROTOCOL_SCHEMA = "formalslt.brier-tabular-protocol.v1"
PREPARATION_SCHEMA = "formalslt.brier-tabular-preparation.v1"
STATUS = "PREPARED_NOT_CERTIFIED"
CLAIM_QUANTITY = "posterior-averaged encountered conditional prefix Brier risk"
SERIES_TERMS = 32
VARIATION_GRID_DENOMINATOR = 1_099_511_627_776
PROVENANCE_TIERS = {"DECLARED", "AUDITED", "SIGNED_LOG"}
NONCLAIMS = [
    "data ingestion and exact arithmetic only; this preparation is not a certificate",
    "no Lean kernel check or statistical coverage theorem is attached",
    "input ordering and provenance are declared by the caller, not externally established",
    "the candidate expression is not future, stationary, population, or deployment risk",
    "the fixed half-tilt preparation is not coin betting or post-hoc strategy selection",
]


class ReplayError(ValueError):
    """Raised when independent replay disagrees with a preparation."""


def encode(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def digest_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def digest_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise ReplayError(f"cannot hash file: {path}") from error
    return digest.hexdigest()


def rat_text(value: Fraction) -> str:
    reduced = Fraction(value)
    return (
        str(reduced.numerator)
        if reduced.denominator == 1
        else f"{reduced.numerator}/{reduced.denominator}"
    )


def upward_grid(value: Fraction) -> Fraction:
    """Independent fixed-grid ceiling used for the observable variation."""

    value = Fraction(value)
    if value < 0:
        raise ReplayError("quadratic variation contribution must be nonnegative")
    quotient, remainder = divmod(
        value.numerator * VARIATION_GRID_DENOMINATOR,
        value.denominator,
    )
    return Fraction(
        quotient + int(remainder != 0),
        VARIATION_GRID_DENOMINATOR,
    )


def rat(value: Any, label: str) -> Fraction:
    if not isinstance(value, str):
        raise ReplayError(f"{label} must be a canonical rational string")
    try:
        answer = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ReplayError(f"invalid rational at {label}: {value!r}") from error
    if rat_text(answer) != value:
        raise ReplayError(f"noncanonical rational at {label}: {value!r}")
    return answer


def strict_json(raw: bytes, label: str) -> dict[str, Any]:
    def fail_float(value: str) -> None:
        raise ReplayError(f"floating-point number in {label}: {value}")

    def fail_constant(value: str) -> None:
        raise ReplayError(f"non-finite number in {label}: {value}")

    def unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise ReplayError(f"duplicate key in {label}: {key}")
            output[key] = value
        return output

    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=fail_float,
            parse_constant=fail_constant,
            object_pairs_hook=unique,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReplayError(f"invalid JSON in {label}: {error}") from error
    if not isinstance(value, dict):
        raise ReplayError(f"{label} must be an object")
    return value


def yaml_document(raw: bytes, label: str) -> dict[str, Any]:
    try:
        import yaml
    except ImportError as error:
        raise ReplayError(
            "YAML replay requires PyYAML; install requirements-cli.txt or use JSON"
        ) from error

    class UniqueLoader(yaml.SafeLoader):
        pass

    def mapping(loader: Any, node: Any, deep: bool = False) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in loader.construct_pairs(node, deep=deep):
            if not isinstance(key, str):
                raise ReplayError(f"non-string key in {label}")
            if key in result:
                raise ReplayError(f"duplicate key in {label}: {key}")
            result[key] = value
        return result

    UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, mapping)
    try:
        value = yaml.load(raw.decode("utf-8"), Loader=UniqueLoader)
    except (UnicodeDecodeError, yaml.YAMLError) as error:
        raise ReplayError(f"invalid YAML in {label}: {error}") from error
    if not isinstance(value, dict):
        raise ReplayError(f"{label} must be an object")
    return value


def read_protocol(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise ReplayError(f"cannot read protocol: {path}") from error
    if path.suffix.lower() == ".json":
        protocol = strict_json(raw, "protocol")
    elif path.suffix.lower() in {".yaml", ".yml"}:
        protocol = yaml_document(raw, "protocol")
    else:
        raise ReplayError("protocol must use .json, .yaml, or .yml")
    if protocol.get("schema_version") != PROTOCOL_SCHEMA:
        raise ReplayError("protocol schema mismatch")
    expected_keys = {
        "analysis",
        "claim",
        "data",
        "models",
        "protocol_id",
        "provenance",
        "schema_version",
        "statistics",
    }
    if set(protocol) != expected_keys:
        raise ReplayError("protocol keys mismatch")
    if protocol.get("analysis") != "brier_monitor":
        raise ReplayError("protocol analysis mismatch")
    data = protocol.get("data")
    models = protocol.get("models")
    statistics = protocol.get("statistics")
    claim = protocol.get("claim")
    provenance = protocol.get("provenance")
    if not isinstance(data, dict) or not isinstance(statistics, dict):
        raise ReplayError("protocol data and statistics must be objects")
    if not isinstance(models, list) or not models:
        raise ReplayError("protocol models must be a nonempty array")
    if not isinstance(claim, dict) or claim.get("quantity") != CLAIM_QUANTITY:
        raise ReplayError("protocol claim quantity mismatch")
    if not isinstance(provenance, dict) or set(provenance) != {
        "evidence_sha256",
        "prediction_timing",
        "tier",
    }:
        raise ReplayError("protocol provenance mismatch")
    if provenance.get("tier") not in PROVENANCE_TIERS:
        raise ReplayError("unsupported provenance tier")
    if provenance.get("prediction_timing") != "PRE_OUTCOME":
        raise ReplayError("prediction timing must be PRE_OUTCOME")
    evidence = provenance.get("evidence_sha256")
    if provenance["tier"] == "DECLARED":
        if evidence is not None:
            raise ReplayError("DECLARED provenance must not name evidence")
    elif not isinstance(evidence, str) or len(evidence) != 64 or any(
        character not in "0123456789abcdef" for character in evidence
    ):
        raise ReplayError("audited provenance evidence digest mismatch")
    if data.get("input_format") not in {"csv", "parquet"}:
        raise ReplayError("unsupported input format")
    if data.get("prediction_encoding") != "scaled_integer":
        raise ReplayError("prediction encoding mismatch")
    if data.get("require_strict_time_order") is not True:
        raise ReplayError("strict time order is required")
    scale = data.get("prediction_scale")
    if isinstance(scale, bool) or not isinstance(scale, int) or scale <= 0:
        raise ReplayError("prediction scale must be a positive integer")
    if statistics.get("wake") != 0 or rat(statistics.get("tilt"), "tilt") != Fraction(1, 2):
        raise ReplayError("replay supports wake 0 and tilt 1/2 only")
    return protocol, raw


def integer(value: Any, label: str) -> int:
    if isinstance(value, bool):
        raise ReplayError(f"{label} must be an integer")
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        stripped = value.strip()
        if stripped and (stripped.isdigit() or (stripped[0] == "-" and stripped[1:].isdigit())):
            return int(stripped)
    raise ReplayError(f"{label} must be an integer")


def csv_rows(path: Path, required: list[str]) -> Iterator[dict[str, Any]]:
    try:
        handle = path.open("r", encoding="utf-8", newline="")
    except OSError as error:
        raise ReplayError(f"cannot open CSV input: {path}") from error
    with handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or len(reader.fieldnames) != len(set(reader.fieldnames)):
            raise ReplayError("CSV header is absent or duplicated")
        missing = sorted(set(required) - set(reader.fieldnames))
        if missing:
            raise ReplayError("CSV is missing columns: " + ", ".join(missing))
        yield from reader


def parquet_rows(path: Path, required: list[str]) -> Iterator[dict[str, Any]]:
    try:
        import pyarrow.parquet as parquet
    except ImportError as error:
        raise ReplayError(
            "Parquet replay requires pyarrow; install requirements-cli.txt or use CSV"
        ) from error
    try:
        source = parquet.ParquetFile(path)
        missing = sorted(set(required) - set(source.schema.names))
        if missing:
            raise ReplayError("Parquet input is missing columns: " + ", ".join(missing))
        for batch in source.iter_batches(batch_size=32768, columns=required):
            yield from batch.to_pylist()
    except ReplayError:
        raise
    except Exception as error:
        raise ReplayError(f"cannot replay Parquet input: {path}") from error


def rows(protocol: dict[str, Any], data_path: Path) -> Iterator[dict[str, Any]]:
    data = protocol["data"]
    required = [data["time_column"], data["outcome_column"]] + [
        model["column"] for model in protocol["models"]
    ]
    expected_suffix = ".csv" if data["input_format"] == "csv" else ".parquet"
    if data_path.suffix.lower() != expected_suffix:
        raise ReplayError(f"input extension must be {expected_suffix}")
    if data["input_format"] == "csv":
        yield from csv_rows(data_path, required)
    else:
        yield from parquet_rows(data_path, required)


def atanh_log_bounds(value: Fraction) -> tuple[Fraction, Fraction]:
    if value <= 0:
        raise ReplayError("log input must be positive")
    if value == 1:
        return Fraction(0), Fraction(0)
    if value < 1:
        lower, upper = atanh_log_bounds(1 / value)
        return -upper, -lower
    exponent = 0
    normalized = value
    while normalized >= 2:
        normalized /= 2
        exponent += 1

    def core(argument: Fraction) -> tuple[Fraction, Fraction]:
        z = (argument - 1) / (argument + 1)
        z_squared = z * z
        power = z
        partial = Fraction(0)
        for index in range(SERIES_TERMS):
            partial += 2 * power / (2 * index + 1)
            power *= z_squared
        remainder = 2 * power / ((2 * SERIES_TERMS + 1) * (1 - z_squared))
        return partial, partial + remainder

    two_lower, two_upper = core(Fraction(2))
    norm_lower, norm_upper = core(normalized)
    return exponent * two_lower + norm_lower, exponent * two_upper + norm_upper


def interval_record(bounds: tuple[Fraction, Fraction]) -> dict[str, str]:
    return {"lower": rat_text(bounds[0]), "upper": rat_text(bounds[1])}


def expected_preparation(
    protocol: dict[str, Any], protocol_raw: bytes, data_path: Path
) -> dict[str, Any]:
    data = protocol["data"]
    model_ids = [model["id"] for model in protocol["models"]]
    model_columns = [model["column"] for model in protocol["models"]]
    if len(model_ids) != len(set(model_ids)) or len(model_columns) != len(set(model_columns)):
        raise ReplayError("model ids and columns must be unique")
    statistics = protocol["statistics"]
    prior_record = statistics.get("prior")
    posterior_record = statistics.get("posterior")
    if not isinstance(prior_record, dict) or not isinstance(posterior_record, dict):
        raise ReplayError("prior and posterior must be objects")
    if set(prior_record) != set(model_ids) or set(posterior_record) != set(model_ids):
        raise ReplayError("prior and posterior keys must equal model ids")
    prior = [rat(prior_record[model], f"prior.{model}") for model in model_ids]
    posterior = [rat(posterior_record[model], f"posterior.{model}") for model in model_ids]
    if any(weight <= 0 for weight in prior) or sum(prior, Fraction(0)) != 1:
        raise ReplayError("prior must be positive and sum to one")
    if any(weight < 0 for weight in posterior) or sum(posterior, Fraction(0)) != 1:
        raise ReplayError("posterior must be nonnegative and sum to one")
    delta = rat(statistics.get("delta"), "delta")
    if not 0 < delta < 1:
        raise ReplayError("delta must lie in (0,1)")
    tilt = rat(statistics.get("tilt"), "tilt")
    scale = data["prediction_scale"]
    prefix_totals = [Fraction(0) for _ in model_ids]
    risk_total = Fraction(0)
    variation_upper = Fraction(0)
    stream_digest = hashlib.sha256()
    last_time: int | None = None
    observation_count = 0

    for observation_count, row in enumerate(rows(protocol, data_path), start=1):
        time = integer(row.get(data["time_column"]), f"row {observation_count} time")
        if last_time is not None and time <= last_time:
            raise ReplayError(f"row {observation_count} time is not strictly increasing")
        last_time = time
        outcome = integer(row.get(data["outcome_column"]), f"row {observation_count} outcome")
        if outcome not in (0, 1):
            raise ReplayError(f"row {observation_count} outcome must be 0 or 1")
        scaled_values: list[int] = []
        row_losses: list[Fraction] = []
        row_variation = Fraction(0)
        for index, column in enumerate(model_columns):
            scaled = integer(row.get(column), f"row {observation_count} prediction {model_ids[index]}")
            if scaled < 0 or scaled > scale:
                raise ReplayError(f"row {observation_count} prediction is outside [0,{scale}]")
            scaled_values.append(scaled)
            loss = (Fraction(scaled, scale) - outcome) ** 2
            history_mean = (
                Fraction(1, 2)
                if observation_count == 1
                else prefix_totals[index] / (observation_count - 1)
            )
            row_variation += posterior[index] * (loss - history_mean) ** 2
            prefix_totals[index] += loss
            row_losses.append(loss)
        variation_upper += upward_grid(row_variation)
        risk_total += sum(
            (posterior[index] * loss for index, loss in enumerate(row_losses)),
            Fraction(0),
        )
        stream_digest.update(
            encode({"outcome": outcome, "predictions": scaled_values, "time": time})
        )

    if observation_count < 4:
        raise ReplayError("at least four observations are required")
    empirical = risk_total / observation_count
    kl_lower = Fraction(0)
    kl_upper = Fraction(0)
    for rho, pi in zip(posterior, prior, strict=True):
        if rho:
            lower, upper = atanh_log_bounds(rho / pi)
            kl_lower += rho * lower
            kl_upper += rho * upper
    confidence_bounds = atanh_log_bounds(1 / delta)
    log_lower, log_upper = atanh_log_bounds(1 - tilt)
    psi_bounds = (-log_upper - tilt, -log_lower - tilt)
    candidate_upper = empirical + (
        kl_upper + confidence_bounds[1] + psi_bounds[1] * variation_upper
    ) / (tilt * observation_count)
    return {
        "artifact_status": STATUS,
        "candidate": {
            "boundary_upper": rat_text(candidate_upper),
            "confidence_log_interval": interval_record(confidence_bounds),
            "kl_interval": interval_record((kl_lower, kl_upper)),
            "psi_interval": interval_record(psi_bounds),
        },
        "claim": {"quantity": CLAIM_QUANTITY, "status": "NOT_CERTIFIED"},
        "data": {
            "input_format": data["input_format"],
            "input_sha256": digest_file(data_path),
            "normalized_stream_sha256": stream_digest.hexdigest(),
            "observations": observation_count,
            "prediction_encoding": "scaled_integer",
            "prediction_scale": scale,
        },
        "nonclaims": NONCLAIMS,
        "protocol": {
            "protocol_id": protocol["protocol_id"],
            "sha256": digest_bytes(protocol_raw),
        },
        "schema_version": PREPARATION_SCHEMA,
        "statistics": {
            "delta": rat_text(delta),
            "posterior_empirical_brier_risk": rat_text(empirical),
            "posterior_suffix_predictor_quadratic_variation_upper": rat_text(
                variation_upper
            ),
            "quadratic_variation_grid_denominator": VARIATION_GRID_DENOMINATOR,
            "quadratic_variation_maximum_rounding_slack": rat_text(
                Fraction(observation_count, VARIATION_GRID_DENOMINATOR)
            ),
            "tilt": rat_text(tilt),
            "wake": 0,
        },
        "verification": {
            "data_parser": "PASS",
            "independent_replay": "NOT_RUN",
            "lean_kernel": "NOT_RUN",
            "source": {
                "path": GENERATOR.relative_to(ROOT).as_posix(),
                "sha256": digest_file(GENERATOR),
            },
        },
    }


def first_difference(actual: Any, expected: Any, path: str = "preparation") -> str | None:
    if type(actual) is not type(expected):
        return f"{path} type mismatch"
    if isinstance(actual, dict):
        if set(actual) != set(expected):
            return f"{path} keys mismatch"
        for key in sorted(actual):
            difference = first_difference(actual[key], expected[key], f"{path}.{key}")
            if difference:
                return difference
        return None
    if isinstance(actual, list):
        if len(actual) != len(expected):
            return f"{path} length mismatch"
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            difference = first_difference(left, right, f"{path}[{index}]")
            if difference:
                return difference
        return None
    if actual != expected:
        return f"{path} mismatch: expected {expected!r}, got {actual!r}"
    return None


def verify(preparation_path: Path, protocol_path: Path, data_path: Path) -> dict[str, Any]:
    try:
        preparation_raw = preparation_path.read_bytes()
    except OSError as error:
        raise ReplayError(f"cannot read preparation: {preparation_path}") from error
    preparation = strict_json(preparation_raw, "preparation")
    if encode(preparation) != preparation_raw:
        raise ReplayError("preparation is not canonical JSON")
    protocol, protocol_raw = read_protocol(protocol_path)
    expected = expected_preparation(protocol, protocol_raw, data_path)
    difference = first_difference(preparation, expected)
    if difference:
        raise ReplayError(difference)
    return preparation


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(description=__doc__)
    root.add_argument("preparation", type=Path)
    root.add_argument("protocol", type=Path)
    root.add_argument("data", type=Path)
    return root


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(list(argv) if argv is not None else None)
    try:
        preparation = verify(args.preparation, args.protocol, args.data)
    except ReplayError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("FormalSLT tabular replay: PASS")
    print(f"Observations:              {preparation['data']['observations']}")
    print(
        "Observed Brier loss:       "
        + preparation["statistics"]["posterior_empirical_brier_risk"]
    )
    print("Certificate verification: NOT ISSUED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
