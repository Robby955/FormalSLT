#!/usr/bin/env python3
"""Independently replay the synthetic Brier-monitor receipt.

This verifier does not import the generator.  It strictly parses the canonical
input, recomputes Brier losses from predictions and outcomes, reconstructs all
suffix statistics and rational log enclosures, checks the unique wake/tilt
witness, renders the expected Lean data independently, and verifies every
manifest digest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "applications/brier_monitor/synthetic-proof-of-life-v1.json"
DEFAULT_RECEIPT = (
    ROOT / "applications/brier_monitor/generated/synthetic-proof-of-life-v1-receipt.json"
)
DEFAULT_MANIFEST = (
    ROOT / "applications/brier_monitor/generated/synthetic-proof-of-life-v1-manifest.json"
)
DEFAULT_LEAN = ROOT / "FormalSLT/Applications/BrierMonitorSyntheticProofOfLifeData.lean"
DEFAULT_LEAN_RECEIPT = (
    ROOT / "FormalSLT/Applications/BrierMonitorSyntheticProofOfLifeReceipt.lean"
)
DEFAULT_LEAN_CHECKER = ROOT / "examples/CheckBrierMonitorSyntheticProofOfLifeReceipt.lean"
GENERATOR = ROOT / "scripts/generate_brier_monitor_synthetic_receipt.py"

INPUT_SCHEMA = "formalslt.brier-monitor.synthetic-input.v1"
RECEIPT_SCHEMA = "formalslt.brier-monitor.synthetic-receipt.v1"
MANIFEST_SCHEMA = "formalslt.brier-monitor.synthetic-manifest.v1"
INPUT_STATUS = "SYNTHETIC PROOF-OF-LIFE INPUT"
RECEIPT_STATUS = "SYNTHETIC PROOF-OF-LIFE ARITHMETIC WITH CONDITIONAL LEAN CLOSURE"
LOG_TERMS = 32
OUTPUT_DENOMINATOR = 10**15
EXPECTED_NONCLAIMS = [
    "synthetic proof-of-life, not real-data evidence",
    "deterministic witness arithmetic, not proof that this path belongs to a theorem-produced good event",
    "the Lean receipt closes exact arithmetic and conditional composition, not realized-path good-event membership",
    "the target semantics are monitored conditional suffix risk, not future, stationary, population, or deployment risk",
    "the supported tilt witness upper-bounds the exact finite-prefix selected boundary; it is not coin betting or a parameter-free master",
    "the input declares predictions as prequential; this local artifact does not establish an external timestamp or production provenance",
]


class VerificationError(ValueError):
    """Raised when independent replay finds any mismatch."""


def _fail_float(value: str) -> None:
    raise VerificationError(f"floating-point JSON numbers are forbidden: {value}")


def _fail_constant(value: str) -> None:
    raise VerificationError(f"non-finite JSON number is forbidden: {value}")


def _unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise VerificationError(f"duplicate JSON key: {key}")
        output[key] = value
    return output


def decode_json(raw: bytes, label: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_fail_float,
            parse_constant=_fail_constant,
            object_pairs_hook=_unique_pairs,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"invalid UTF-8 JSON in {label}: {error}") from error


def encode_json(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode()


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rat_text(value: Fraction) -> str:
    reduced = Fraction(value)
    return (
        str(reduced.numerator)
        if reduced.denominator == 1
        else f"{reduced.numerator}/{reduced.denominator}"
    )


def parse_rat(value: Any, label: str) -> Fraction:
    if not isinstance(value, str):
        raise VerificationError(f"{label} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError(f"invalid rational at {label}: {value!r}") from error
    if rat_text(result) != value:
        raise VerificationError(f"noncanonical rational at {label}: {value!r}")
    return result


def require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise VerificationError(f"{label} must be an object")
    return value


def require_array(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise VerificationError(f"{label} must be an array")
    return value


def require_integer(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise VerificationError(f"{label} must be an integer")
    return value


def require_keys(value: dict[str, Any], keys: set[str], label: str) -> None:
    if set(value) != keys:
        raise VerificationError(
            f"{label} keys mismatch; missing={sorted(keys - set(value))}, "
            f"extra={sorted(set(value) - keys)}"
        )


def require_equal(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise VerificationError(f"{label} mismatch: expected {expected!r}, got {actual!r}")


def repo_path(value: Any, label: str) -> Path:
    if not isinstance(value, str):
        raise VerificationError(f"{label} must be a repository-relative path")
    result = (ROOT / value).resolve()
    try:
        result.relative_to(ROOT.resolve())
    except ValueError as error:
        raise VerificationError(f"{label} escapes the repository root") from error
    return result


def git_blob(commit: str, relative_path: str) -> bytes:
    try:
        process = subprocess.run(
            ["git", "show", f"{commit}:{relative_path}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise VerificationError(
            f"cannot resolve pinned source {commit}:{relative_path}"
        ) from error
    return process.stdout


def unit_log_bounds(value: Fraction) -> tuple[Fraction, Fraction]:
    if not (1 <= value <= 2):
        raise AssertionError("range reduction failed")
    z = (value - 1) / (value + 1)
    powers = z
    partial = Fraction(0)
    z_squared = z * z
    for index in range(LOG_TERMS):
        partial += 2 * powers / (2 * index + 1)
        powers *= z_squared
    remainder = 2 * powers / ((2 * LOG_TERMS + 1) * (1 - z_squared))
    return partial, partial + remainder


def log_bounds(value: Fraction) -> tuple[Fraction, Fraction]:
    if value <= 0:
        raise VerificationError("log input must be positive")
    if value == 1:
        return Fraction(0), Fraction(0)
    if value < 1:
        low, high = log_bounds(1 / value)
        return -high, -low
    exponent = 0
    normalized = value
    while normalized >= 2:
        normalized = normalized / 2
        exponent += 1
    two_low, two_high = unit_log_bounds(Fraction(2))
    norm_low, norm_high = unit_log_bounds(normalized)
    return exponent * two_low + norm_low, exponent * two_high + norm_high


def relative_entropy_bounds(
    posterior: list[Fraction], prior: list[Fraction]
) -> tuple[Fraction, Fraction]:
    low = Fraction(0)
    high = Fraction(0)
    for rho, pi in zip(posterior, prior, strict=True):
        if rho:
            term_low, term_high = log_bounds(rho / pi)
            low += rho * term_low
            high += rho * term_high
    return low, high


def empirical_bernstein_psi_bounds(lam: Fraction) -> tuple[Fraction, Fraction]:
    lower_log, upper_log = log_bounds(1 - lam)
    return -upper_log - lam, -lower_log - lam


def round_lower(value: Fraction) -> Fraction:
    scaled = value * OUTPUT_DENOMINATOR
    return Fraction(scaled.numerator // scaled.denominator, OUTPUT_DENOMINATOR)


def round_upper(value: Fraction) -> Fraction:
    return -round_lower(-value)


def interval_record(bounds: tuple[Fraction, Fraction]) -> dict[str, str]:
    return {
        "lower": rat_text(round_lower(bounds[0])),
        "upper": rat_text(round_upper(bounds[1])),
    }


def floor_log_four(value: int) -> int:
    answer = 0
    threshold = 4
    while threshold <= value:
        answer += 1
        threshold *= 4
    return answer


def largest_atom(suffix_length: int) -> int:
    return max(floor_log_four(suffix_length) - 1, 0) + 2


def display_path(path: Path) -> str:
    absolute = path.resolve()
    try:
        return absolute.relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return absolute.as_posix()


def load_input(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    spec = require_object(decode_json(raw, "input"), "input")
    if encode_json(spec) != raw:
        raise VerificationError("input is not canonical JSON")
    require_keys(
        spec,
        {
            "artifact_status",
            "candidate_wakes",
            "confidence_delta",
            "models",
            "nonclaims",
            "posterior",
            "prior",
            "schema_version",
            "source",
            "stream_segments",
        },
        "input",
    )
    require_equal(spec["schema_version"], INPUT_SCHEMA, "schema_version")
    require_equal(spec["artifact_status"], INPUT_STATUS, "artifact_status")
    require_equal(spec["nonclaims"], EXPECTED_NONCLAIMS, "nonclaims")

    source = require_object(spec["source"], "source")
    require_keys(
        source,
        {
            "formal_slt_commit",
            "oracle_module_path",
            "oracle_module_sha256",
            "oracle_theorem",
            "proof_of_life_checker_path",
            "proof_of_life_checker_sha256",
        },
        "source",
    )
    commit = source["formal_slt_commit"]
    if not isinstance(commit, str) or len(commit) != 40 or any(
        char not in "0123456789abcdef" for char in commit
    ):
        raise VerificationError("formal_slt_commit is not a lowercase 40-hex SHA")
    source_files: dict[str, Path] = {}
    for role in ("oracle_module", "proof_of_life_checker"):
        relative = source[f"{role}_path"]
        current_path = repo_path(relative, f"source.{role}_path")
        pinned = git_blob(commit, relative)
        require_equal(current_path.read_bytes(), pinned, f"current {role} bytes")
        require_equal(digest(pinned), source[f"{role}_sha256"], f"source.{role}_sha256")
        source_files[role] = current_path
    declaration = source["oracle_theorem"]
    if not isinstance(declaration, str) or declaration.rsplit(".", 1)[-1].encode() not in git_blob(
        commit, source["oracle_module_path"]
    ):
        raise VerificationError("oracle theorem is absent from pinned source")

    models = require_array(spec["models"], "models")
    if not models or any(not isinstance(value, str) or not value for value in models):
        raise VerificationError("models must be nonempty strings")
    if len(models) != len(set(models)):
        raise VerificationError("model identifiers are not unique")

    prior = [parse_rat(value, f"prior[{index}]") for index, value in enumerate(
        require_array(spec["prior"], "prior")
    )]
    posterior = [parse_rat(value, f"posterior[{index}]") for index, value in enumerate(
        require_array(spec["posterior"], "posterior")
    )]
    if len(prior) != len(models) or len(posterior) != len(models):
        raise VerificationError("distribution dimensions do not match models")
    if any(weight <= 0 for weight in prior) or sum(prior, Fraction(0)) != 1:
        raise VerificationError("prior is not a full-support PMF")
    if any(weight < 0 for weight in posterior) or sum(posterior, Fraction(0)) != 1:
        raise VerificationError("posterior is not a PMF")
    delta = parse_rat(spec["confidence_delta"], "confidence_delta")
    if not 0 < delta <= 1:
        raise VerificationError("confidence delta is outside (0,1]")

    rows: list[tuple[int, list[Fraction]]] = []
    for segment_number, item in enumerate(require_array(spec["stream_segments"], "stream_segments")):
        segment = require_object(item, f"stream_segments[{segment_number}]")
        require_keys(segment, {"count", "outcome", "predictions"}, "stream segment")
        count = require_integer(segment["count"], "segment count")
        outcome = require_integer(segment["outcome"], "segment outcome")
        if count <= 0 or outcome not in (0, 1):
            raise VerificationError("invalid segment count or binary outcome")
        forecasts = [
            parse_rat(value, f"prediction[{index}]")
            for index, value in enumerate(require_array(segment["predictions"], "predictions"))
        ]
        if len(forecasts) != len(models) or any(not 0 <= value <= 1 for value in forecasts):
            raise VerificationError("prediction row has invalid dimension or range")
        for _unused in range(count):
            rows.append((outcome, forecasts))
    if len(rows) < 4:
        raise VerificationError("fewer than four observations")

    wakes = [
        require_integer(value, f"candidate_wakes[{index}]")
        for index, value in enumerate(require_array(spec["candidate_wakes"], "candidate_wakes"))
    ]
    if not wakes or wakes != sorted(set(wakes)):
        raise VerificationError("candidate wakes are not strictly increasing")
    if any(wake < 0 or len(rows) - wake < 4 for wake in wakes):
        raise VerificationError("candidate wake leaves an inadmissible suffix")

    return {
        "raw": raw,
        "source": source,
        "source_files": source_files,
        "models": models,
        "prior": prior,
        "posterior": posterior,
        "delta": delta,
        "observations": rows,
        "wakes": wakes,
    }


def loss_matrix(parsed: dict[str, Any]) -> list[list[Fraction]]:
    matrix = [[] for _ in parsed["models"]]
    for outcome, forecasts in parsed["observations"]:
        for index, forecast in enumerate(forecasts):
            matrix[index].append((forecast - outcome) * (forecast - outcome))
    return matrix


def suffix_values(
    matrix: list[list[Fraction]], posterior: list[Fraction], wake: int
) -> tuple[Fraction, Fraction]:
    stop = len(matrix[0])
    length = stop - wake
    risk = sum(
        (
            posterior[index] * sum(values[wake:], Fraction(0)) / length
            for index, values in enumerate(matrix)
        ),
        Fraction(0),
    )
    variation = Fraction(0)
    for model_index, values in enumerate(matrix):
        prefix_total = Fraction(0)
        per_model = Fraction(0)
        for time in range(stop):
            estimate = Fraction(1, 2) if time == 0 else prefix_total / time
            if time >= wake:
                per_model += (values[time] - estimate) ** 2
            prefix_total += values[time]
        variation += posterior[model_index] * per_model
    return risk, variation


def replay_receipt(parsed: dict[str, Any]) -> dict[str, Any]:
    matrix = loss_matrix(parsed)
    entropy = relative_entropy_bounds(parsed["posterior"], parsed["prior"])
    horizon = len(parsed["observations"])
    output_rows: list[dict[str, Any]] = []
    candidates: list[tuple[Fraction, Fraction, dict[str, Any]]] = []
    for wake in parsed["wakes"]:
        length = horizon - wake
        empirical, variation = suffix_values(matrix, parsed["posterior"], wake)
        wake_delta = parsed["delta"] / ((wake + 1) * (wake + 2))
        for atom in range(largest_atom(length) + 1):
            tilt = Fraction(1, 2 ** (atom + 1))
            log_charge = log_bounds(Fraction((atom + 1) * (atom + 2), 1) / wake_delta)
            psi = empirical_bernstein_psi_bounds(tilt)
            denominator = length * tilt
            lower = empirical + (entropy[0] + log_charge[0] + psi[0] * variation) / denominator
            upper = empirical + (entropy[1] + log_charge[1] + psi[1] * variation) / denominator
            record = {
                "boundary_interval": interval_record((lower, upper)),
                "confidence_log_interval": interval_record(log_charge),
                "effective_delta": rat_text(wake_delta),
                "kl_interval": interval_record(entropy),
                "posterior_empirical_brier_risk": rat_text(empirical),
                "psi_interval": interval_record(psi),
                "suffix_length": length,
                "suffix_predictor_quadratic_variation": rat_text(variation),
                "tilt": rat_text(tilt),
                "tilt_atom": atom,
                "wake": wake,
            }
            output_rows.append(record)
            candidates.append((lower, upper, record))
    chosen_low, chosen_high, chosen = min(candidates, key=lambda item: item[1])
    other_lowers = [low for low, _high, record in candidates if record is not chosen]
    margin = min(other_lowers) - chosen_high
    if margin <= 0:
        raise VerificationError("candidate interval separation does not prove a unique witness")

    expanded = [
        {"outcome": outcome, "predictions": [rat_text(value) for value in forecasts]}
        for outcome, forecasts in parsed["observations"]
    ]
    losses = {
        model: [rat_text(value) for value in values]
        for model, values in zip(parsed["models"], matrix, strict=True)
    }
    return {
        "artifact_status": RECEIPT_STATUS,
        "boundary_rows": output_rows,
        "input_sha256": digest(parsed["raw"]),
        "log_enclosure": {
            "method": "range-reduced atanh series with exact rational remainder bound",
            "output_denominator": OUTPUT_DENOMINATOR,
            "terms": LOG_TERMS,
        },
        "models": parsed["models"],
        "nonclaims": EXPECTED_NONCLAIMS,
        "posterior": [rat_text(value) for value in parsed["posterior"]],
        "prior": [rat_text(value) for value in parsed["prior"]],
        "receipt_schema": RECEIPT_SCHEMA,
        "selected_witness": {
            **chosen,
            "exact_selection_margin_lower": rat_text(round_lower(margin)),
            "oracle_relation": (
                "for the selected wake, finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le "
                "makes the exact finite-prefix selected boundary no larger than this supported atom"
            ),
        },
        "source": parsed["source"],
        "stream": {
            "expanded_stream_sha256": digest(encode_json(expanded)),
            "horizon": horizon,
            "loss_sequence_sha256": {
                model: digest(encode_json(values)) for model, values in losses.items()
            },
            "losses_recomputed_from_predictions_and_outcomes": "true",
        },
    }


def lean_rat(text: str) -> str:
    value = Fraction(text)
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def expected_lean(receipt: dict[str, Any], receipt_hash: str) -> bytes:
    item = receipt["selected_witness"]
    return f'''/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Mathlib.Data.Rat.Defs

/-!
# Generated synthetic Brier-monitor arithmetic data

This module records deterministic rational outputs from the synthetic
proof-of-life pipeline.  It contains no statistical theorem, no proof that the
path belongs to a theorem-produced good event, and no real-data claim.
-/

namespace FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeData

abbrev inputSha256 : String := "{receipt['input_sha256']}"
abbrev receiptSha256 : String := "{receipt_hash}"
abbrev formalSLTCommit : String := "{receipt['source']['formal_slt_commit']}"
abbrev horizon : Nat := {receipt['stream']['horizon']}
abbrev selectedWake : Nat := {item['wake']}
abbrev selectedTiltAtom : Nat := {item['tilt_atom']}
abbrev selectedTilt : ℚ := {lean_rat(item['tilt'])}
abbrev posteriorEmpiricalBrierRisk : ℚ :=
  {lean_rat(item['posterior_empirical_brier_risk'])}
abbrev suffixPredictorQuadraticVariation : ℚ :=
  {lean_rat(item['suffix_predictor_quadratic_variation'])}
abbrev selectedBoundaryLower : ℚ :=
  {lean_rat(item['boundary_interval']['lower'])}
abbrev selectedBoundaryUpper : ℚ :=
  {lean_rat(item['boundary_interval']['upper'])}
abbrev exactSelectionMarginLower : ℚ :=
  {lean_rat(item['exact_selection_margin_lower'])}

end FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeData
'''.encode("utf-8")


def verify_manifest(
    manifest_path: Path,
    parsed: dict[str, Any],
    receipt_path: Path,
    receipt_raw: bytes,
    lean_path: Path,
    lean_raw: bytes,
) -> None:
    raw = manifest_path.read_bytes()
    manifest = require_object(decode_json(raw, "manifest"), "manifest")
    if raw != encode_json(manifest):
        raise VerificationError("manifest is not canonical JSON")
    require_keys(
        manifest,
        {"artifact_status", "files", "formal_slt_commit", "manifest_schema", "nonclaims"},
        "manifest",
    )
    require_equal(manifest["manifest_schema"], MANIFEST_SCHEMA, "manifest schema")
    require_equal(manifest["artifact_status"], RECEIPT_STATUS, "manifest status")
    require_equal(manifest["nonclaims"], EXPECTED_NONCLAIMS, "manifest nonclaims")
    require_equal(
        manifest["formal_slt_commit"], parsed["source"]["formal_slt_commit"], "manifest commit"
    )

    expected = {
        "input": (Path(parsed["input_path"]), parsed["raw"]),
        "generator": (GENERATOR, GENERATOR.read_bytes()),
        "independent_verifier": (Path(__file__).resolve(), Path(__file__).read_bytes()),
        "oracle_source": (
            parsed["source_files"]["oracle_module"],
            parsed["source_files"]["oracle_module"].read_bytes(),
        ),
        "proof_of_life_checker": (
            parsed["source_files"]["proof_of_life_checker"],
            parsed["source_files"]["proof_of_life_checker"].read_bytes(),
        ),
        "receipt": (receipt_path, receipt_raw),
        "lean_data": (lean_path, lean_raw),
        "lean_receipt_source": (
            DEFAULT_LEAN_RECEIPT,
            DEFAULT_LEAN_RECEIPT.read_bytes(),
        ),
        "lean_receipt_checker": (
            DEFAULT_LEAN_CHECKER,
            DEFAULT_LEAN_CHECKER.read_bytes(),
        ),
    }
    rows = require_array(manifest["files"], "manifest.files")
    if len(rows) != len(expected):
        raise VerificationError("manifest file count mismatch")
    seen: set[str] = set()
    for row_value in rows:
        row = require_object(row_value, "manifest file row")
        require_keys(row, {"bytes", "path", "role", "sha256"}, "manifest file row")
        role = row["role"]
        if role not in expected or role in seen:
            raise VerificationError(f"unexpected or duplicate manifest role: {role!r}")
        seen.add(role)
        path, file_raw = expected[role]
        require_equal(row["path"], display_path(path), f"{role} path")
        require_equal(row["bytes"], len(file_raw), f"{role} bytes")
        require_equal(row["sha256"], digest(file_raw), f"{role} sha256")
    require_equal(seen, set(expected), "manifest roles")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--check", action="store_true", help="accepted for symmetry; verification is always read-only")
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        parsed = load_input(args.input)
        parsed["input_path"] = args.input
        expected_receipt = replay_receipt(parsed)
        expected_receipt_raw = encode_json(expected_receipt)
        actual_receipt_raw = args.receipt.read_bytes()
        if actual_receipt_raw != expected_receipt_raw:
            raise VerificationError("receipt bytes differ from independent replay")
        actual_receipt = require_object(decode_json(actual_receipt_raw, "receipt"), "receipt")
        require_equal(actual_receipt, expected_receipt, "receipt object")
        lean_raw = expected_lean(expected_receipt, digest(expected_receipt_raw))
        require_equal(args.lean.read_bytes(), lean_raw, "Lean data bytes")
        verify_manifest(
            args.manifest,
            parsed,
            args.receipt,
            expected_receipt_raw,
            args.lean,
            lean_raw,
        )
    except (OSError, VerificationError) as error:
        print(f"ERROR: synthetic Brier receipt verification failed: {error}", file=sys.stderr)
        return 1
    print(
        "independent synthetic Brier replay passed: "
        f"{display_path(args.receipt)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
