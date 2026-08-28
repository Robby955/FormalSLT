#!/usr/bin/env python3
"""Generate an exact synthetic Brier-monitor witness package.

The input contains outcomes and prequential probability forecasts, never a
trusted loss column.  This script recomputes Brier losses, posterior empirical
suffix risk, the observable forward-predictor quadratic variation, and
conservative rational enclosures for every admitted wake/tilt boundary.  It
then emits a deterministic receipt, manifest, and Lean data module.

The emitted Lean module contains arithmetic data only.  This generator does
not prove that the synthetic path belongs to a theorem-produced good event and
does not close a statistical certificate in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
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
DEFAULT_VERIFIER = ROOT / "scripts/verify_brier_monitor_synthetic_receipt.py"

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


class ReceiptError(ValueError):
    """Raised when an input or generated artifact violates the contract."""


def _reject_float(value: str) -> None:
    raise ReceiptError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise ReceiptError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ReceiptError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json_bytes(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReceiptError(f"invalid UTF-8 JSON in {where}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rational_text(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fraction(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise ReceiptError(f"{where} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ReceiptError(f"invalid rational at {where}: {value!r}") from error
    if rational_text(result) != value:
        raise ReceiptError(f"noncanonical rational at {where}: {value!r}")
    return result


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ReceiptError(f"{where} must be an object")
    return value


def _array(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReceiptError(f"{where} must be an array")
    return value


def _integer(value: Any, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ReceiptError(f"{where} must be an integer")
    return value


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    if set(value) != expected:
        raise ReceiptError(
            f"{where} keys mismatch; missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise ReceiptError(f"{where} must be {expected!r}, got {actual!r}")


def _inside_root(path_text: str, where: str) -> Path:
    if not isinstance(path_text, str):
        raise ReceiptError(f"{where} must be a repository-relative path string")
    path = (ROOT / path_text).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as error:
        raise ReceiptError(f"{where} escapes the repository root") from error
    return path


def _git_blob(commit: str, path_text: str) -> bytes:
    try:
        result = subprocess.run(
            ["git", "show", f"{commit}:{path_text}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReceiptError(f"cannot resolve pinned source {commit}:{path_text}") from error
    return result.stdout


def _log_unit_interval(value: Fraction, terms: int) -> tuple[Fraction, Fraction]:
    """Enclose log(value) for 1 <= value < 2 by an exact atanh series."""

    if not (1 <= value <= 2):
        raise AssertionError("unit log reduction requires 1 <= value <= 2")
    z = (value - 1) / (value + 1)
    partial = Fraction(0)
    for k in range(terms):
        partial += 2 * z ** (2 * k + 1) / (2 * k + 1)
    remainder = (
        2 * z ** (2 * terms + 1) /
        ((2 * terms + 1) * (1 - z * z))
    )
    return partial, partial + remainder


def log_interval(value: Fraction, terms: int = LOG_TERMS) -> tuple[Fraction, Fraction]:
    """Return a rigorous rational enclosure of log(value)."""

    value = Fraction(value)
    if value <= 0:
        raise ReceiptError("log input must be positive")
    if value == 1:
        return Fraction(0), Fraction(0)
    if value < 1:
        low, high = log_interval(1 / value, terms)
        return -high, -low
    exponent = 0
    reduced = value
    while reduced >= 2:
        reduced /= 2
        exponent += 1
    log2_low, log2_high = _log_unit_interval(Fraction(2), terms)
    reduced_low, reduced_high = _log_unit_interval(reduced, terms)
    return (
        exponent * log2_low + reduced_low,
        exponent * log2_high + reduced_high,
    )


def _weighted_interval(
    weight: Fraction, interval: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    if weight < 0:
        raise AssertionError("interval weight must be nonnegative")
    return weight * interval[0], weight * interval[1]


def kl_interval(
    posterior: list[Fraction], prior: list[Fraction]
) -> tuple[Fraction, Fraction]:
    low = Fraction(0)
    high = Fraction(0)
    for rho, pi in zip(posterior, prior, strict=True):
        if rho == 0:
            continue
        term_low, term_high = _weighted_interval(rho, log_interval(rho / pi))
        low += term_low
        high += term_high
    return low, high


def psi_interval(lam: Fraction) -> tuple[Fraction, Fraction]:
    log_low, log_high = log_interval(1 - lam)
    return -log_high - lam, -log_low - lam


def _round_down(value: Fraction) -> Fraction:
    return Fraction((value * OUTPUT_DENOMINATOR).numerator //
                    (value * OUTPUT_DENOMINATOR).denominator, OUTPUT_DENOMINATOR)


def _round_up(value: Fraction) -> Fraction:
    return -_round_down(-value)


def _interval_json(interval: tuple[Fraction, Fraction]) -> dict[str, str]:
    return {
        "lower": rational_text(_round_down(interval[0])),
        "upper": rational_text(_round_up(interval[1])),
    }


def _nat_log_four(value: int) -> int:
    if value < 1:
        return 0
    result = 0
    power = 1
    while power * 4 <= value:
        power *= 4
        result += 1
    return result


def max_geometric_atom(suffix_length: int) -> int:
    return max(_nat_log_four(suffix_length) - 1, 0) + 2


def _display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def parse_spec(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    spec = _object(parse_json_bytes(raw, "Brier monitor input"), "Brier monitor input")
    if raw != canonical_json_bytes(spec):
        raise ReceiptError("Brier monitor input must use canonical JSON bytes")
    _keys(
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
        "Brier monitor input",
    )
    _exact(spec["schema_version"], INPUT_SCHEMA, "schema_version")
    _exact(spec["artifact_status"], INPUT_STATUS, "artifact_status")
    _exact(spec["nonclaims"], EXPECTED_NONCLAIMS, "nonclaims")

    source = _object(spec["source"], "source")
    _keys(
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
        character not in "0123456789abcdef" for character in commit
    ):
        raise ReceiptError("source.formal_slt_commit must be a lowercase 40-hex SHA")
    for role in ("oracle_module", "proof_of_life_checker"):
        path_text = source[f"{role}_path"]
        digest = source[f"{role}_sha256"]
        file_path = _inside_root(path_text, f"source.{role}_path")
        current_raw = file_path.read_bytes()
        pinned_raw = _git_blob(commit, path_text)
        if current_raw != pinned_raw:
            raise ReceiptError(f"current {path_text} differs from pinned commit {commit}")
        _exact(sha256_bytes(pinned_raw), digest, f"source.{role}_sha256")
    theorem = source["oracle_theorem"]
    if not isinstance(theorem, str) or theorem.rsplit(".", 1)[-1].encode() not in _git_blob(
        commit, source["oracle_module_path"]
    ):
        raise ReceiptError("source.oracle_theorem is absent from the pinned oracle module")

    models = _array(spec["models"], "models")
    if not models or any(not isinstance(model, str) or not model for model in models):
        raise ReceiptError("models must contain nonempty strings")
    if len(set(models)) != len(models):
        raise ReceiptError("model identifiers must be unique")
    model_count = len(models)

    prior = [_fraction(value, f"prior[{index}]") for index, value in enumerate(
        _array(spec["prior"], "prior")
    )]
    posterior = [_fraction(value, f"posterior[{index}]") for index, value in enumerate(
        _array(spec["posterior"], "posterior")
    )]
    if len(prior) != model_count or len(posterior) != model_count:
        raise ReceiptError("prior and posterior lengths must match models")
    if any(value <= 0 for value in prior) or sum(prior, Fraction(0)) != 1:
        raise ReceiptError("prior must be a full-support probability mass function")
    if any(value < 0 for value in posterior) or sum(posterior, Fraction(0)) != 1:
        raise ReceiptError("posterior must be a probability mass function")

    delta = _fraction(spec["confidence_delta"], "confidence_delta")
    if not (0 < delta <= 1):
        raise ReceiptError("confidence_delta must lie in (0,1]")

    observations: list[tuple[int, list[Fraction]]] = []
    for segment_index, raw_segment in enumerate(
        _array(spec["stream_segments"], "stream_segments")
    ):
        segment = _object(raw_segment, f"stream_segments[{segment_index}]")
        _keys(segment, {"count", "outcome", "predictions"}, f"stream_segments[{segment_index}]")
        count = _integer(segment["count"], f"stream_segments[{segment_index}].count")
        outcome = _integer(segment["outcome"], f"stream_segments[{segment_index}].outcome")
        if count <= 0:
            raise ReceiptError("stream segment count must be positive")
        if outcome not in (0, 1):
            raise ReceiptError("Brier outcomes must be 0 or 1")
        predictions = [
            _fraction(value, f"stream_segments[{segment_index}].predictions[{index}]")
            for index, value in enumerate(_array(segment["predictions"], "predictions"))
        ]
        if len(predictions) != model_count:
            raise ReceiptError("each prediction row must match the model count")
        if any(not (0 <= prediction <= 1) for prediction in predictions):
            raise ReceiptError("Brier predictions must lie in [0,1]")
        observations.extend((outcome, predictions) for _ in range(count))
    if len(observations) < 4:
        raise ReceiptError("at least four observations are required")

    wakes = [
        _integer(value, f"candidate_wakes[{index}]")
        for index, value in enumerate(_array(spec["candidate_wakes"], "candidate_wakes"))
    ]
    if not wakes or wakes != sorted(set(wakes)):
        raise ReceiptError("candidate_wakes must be a nonempty strictly increasing array")
    if any(wake < 0 or len(observations) - wake < 4 for wake in wakes):
        raise ReceiptError("each candidate wake must leave a suffix of length at least four")

    return {
        "raw": raw,
        "spec": spec,
        "source": source,
        "models": models,
        "prior": prior,
        "posterior": posterior,
        "delta": delta,
        "observations": observations,
        "wakes": wakes,
    }


def _losses(parsed: dict[str, Any]) -> list[list[Fraction]]:
    model_count = len(parsed["models"])
    result = [[] for _ in range(model_count)]
    for outcome, predictions in parsed["observations"]:
        target = Fraction(outcome)
        for model_index, prediction in enumerate(predictions):
            result[model_index].append((prediction - target) ** 2)
    return result


def _posterior_suffix_statistics(
    losses: list[list[Fraction]], posterior: list[Fraction], wake: int
) -> tuple[Fraction, Fraction]:
    horizon = len(losses[0])
    suffix_length = horizon - wake
    empirical = Fraction(0)
    quadratic = Fraction(0)
    for weight, model_losses in zip(posterior, losses, strict=True):
        empirical += weight * sum(model_losses[wake:], Fraction(0)) / suffix_length
        running_sum = Fraction(0)
        model_quadratic = Fraction(0)
        for time, loss in enumerate(model_losses):
            predictor = Fraction(1, 2) if time == 0 else running_sum / time
            if time >= wake:
                model_quadratic += (loss - predictor) ** 2
            running_sum += loss
        quadratic += weight * model_quadratic
    return empirical, quadratic


def compute_receipt(parsed: dict[str, Any]) -> dict[str, Any]:
    losses = _losses(parsed)
    posterior = parsed["posterior"]
    prior = parsed["prior"]
    delta = parsed["delta"]
    horizon = len(parsed["observations"])
    kl_bounds = kl_interval(posterior, prior)
    rows: list[dict[str, Any]] = []
    numeric_rows: list[tuple[Fraction, Fraction, dict[str, Any]]] = []

    for wake in parsed["wakes"]:
        suffix_length = horizon - wake
        empirical, quadratic = _posterior_suffix_statistics(losses, posterior, wake)
        effective_delta = delta / ((wake + 1) * (wake + 2))
        for atom in range(max_geometric_atom(suffix_length) + 1):
            lam = Fraction(1, 2 ** (atom + 1))
            confidence_ratio = Fraction((atom + 1) * (atom + 2), 1) / effective_delta
            confidence_log = log_interval(confidence_ratio)
            psi_bounds = psi_interval(lam)
            numerator_low = kl_bounds[0] + confidence_log[0] + psi_bounds[0] * quadratic
            numerator_high = kl_bounds[1] + confidence_log[1] + psi_bounds[1] * quadratic
            denominator = suffix_length * lam
            boundary = (
                empirical + numerator_low / denominator,
                empirical + numerator_high / denominator,
            )
            row = {
                "boundary_interval": _interval_json(boundary),
                "confidence_log_interval": _interval_json(confidence_log),
                "effective_delta": rational_text(effective_delta),
                "kl_interval": _interval_json(kl_bounds),
                "posterior_empirical_brier_risk": rational_text(empirical),
                "psi_interval": _interval_json(psi_bounds),
                "suffix_length": suffix_length,
                "suffix_predictor_quadratic_variation": rational_text(quadratic),
                "tilt": rational_text(lam),
                "tilt_atom": atom,
                "wake": wake,
            }
            rows.append(row)
            numeric_rows.append((boundary[0], boundary[1], row))

    selected_low, selected_high, selected_row = min(numeric_rows, key=lambda item: item[1])
    competitor_lowers = [low for low, _high, row in numeric_rows if row is not selected_row]
    selection_margin = min(competitor_lowers) - selected_high
    if selection_margin <= 0:
        raise ReceiptError("rational log enclosures do not certify a unique boundary witness")

    stream_rows = [
        {
            "outcome": outcome,
            "predictions": [rational_text(value) for value in predictions],
        }
        for outcome, predictions in parsed["observations"]
    ]
    loss_rows = {
        model: [rational_text(value) for value in model_losses]
        for model, model_losses in zip(parsed["models"], losses, strict=True)
    }
    return {
        "artifact_status": RECEIPT_STATUS,
        "boundary_rows": rows,
        "input_sha256": sha256_bytes(parsed["raw"]),
        "log_enclosure": {
            "method": "range-reduced atanh series with exact rational remainder bound",
            "output_denominator": OUTPUT_DENOMINATOR,
            "terms": LOG_TERMS,
        },
        "models": parsed["models"],
        "nonclaims": EXPECTED_NONCLAIMS,
        "posterior": [rational_text(value) for value in posterior],
        "prior": [rational_text(value) for value in prior],
        "receipt_schema": RECEIPT_SCHEMA,
        "selected_witness": {
            **selected_row,
            "exact_selection_margin_lower": rational_text(_round_down(selection_margin)),
            "oracle_relation": (
                "for the selected wake, finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le "
                "makes the exact finite-prefix selected boundary no larger than this supported atom"
            ),
        },
        "source": parsed["source"],
        "stream": {
            "expanded_stream_sha256": sha256_bytes(canonical_json_bytes(stream_rows)),
            "horizon": horizon,
            "loss_sequence_sha256": {
                model: sha256_bytes(canonical_json_bytes(values))
                for model, values in loss_rows.items()
            },
            "losses_recomputed_from_predictions_and_outcomes": "true",
        },
    }


def _lean_fraction(value: str) -> str:
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return f"({fraction.numerator} : ℚ)"
    return f"(({fraction.numerator} : ℚ) / {fraction.denominator})"


def render_lean(receipt: dict[str, Any], receipt_sha256: str) -> bytes:
    selected = receipt["selected_witness"]
    content = f'''/-
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
abbrev receiptSha256 : String := "{receipt_sha256}"
abbrev formalSLTCommit : String := "{receipt['source']['formal_slt_commit']}"
abbrev horizon : Nat := {receipt['stream']['horizon']}
abbrev selectedWake : Nat := {selected['wake']}
abbrev selectedTiltAtom : Nat := {selected['tilt_atom']}
abbrev selectedTilt : ℚ := {_lean_fraction(selected['tilt'])}
abbrev posteriorEmpiricalBrierRisk : ℚ :=
  {_lean_fraction(selected['posterior_empirical_brier_risk'])}
abbrev suffixPredictorQuadraticVariation : ℚ :=
  {_lean_fraction(selected['suffix_predictor_quadratic_variation'])}
abbrev selectedBoundaryLower : ℚ :=
  {_lean_fraction(selected['boundary_interval']['lower'])}
abbrev selectedBoundaryUpper : ℚ :=
  {_lean_fraction(selected['boundary_interval']['upper'])}
abbrev exactSelectionMarginLower : ℚ :=
  {_lean_fraction(selected['exact_selection_margin_lower'])}

end FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeData
'''
    return content.encode("utf-8")


def _file_row(role: str, path: Path, raw: bytes) -> dict[str, Any]:
    return {
        "bytes": len(raw),
        "path": _display_path(path),
        "role": role,
        "sha256": sha256_bytes(raw),
    }


def expected_artifacts(
    input_path: Path = DEFAULT_INPUT,
    receipt_path: Path = DEFAULT_RECEIPT,
    manifest_path: Path = DEFAULT_MANIFEST,
    lean_path: Path = DEFAULT_LEAN,
) -> tuple[bytes, bytes, bytes]:
    parsed = parse_spec(input_path)
    receipt = compute_receipt(parsed)
    receipt_raw = canonical_json_bytes(receipt)
    lean_raw = render_lean(receipt, sha256_bytes(receipt_raw))
    generator_path = Path(__file__).resolve()
    verifier_path = DEFAULT_VERIFIER.resolve()
    source = parsed["source"]
    oracle_path = _inside_root(source["oracle_module_path"], "source.oracle_module_path")
    checker_path = _inside_root(
        source["proof_of_life_checker_path"], "source.proof_of_life_checker_path"
    )
    manifest = {
        "artifact_status": RECEIPT_STATUS,
        "files": [
            _file_row("input", input_path, parsed["raw"]),
            _file_row("generator", generator_path, generator_path.read_bytes()),
            _file_row("independent_verifier", verifier_path, verifier_path.read_bytes()),
            _file_row("oracle_source", oracle_path, oracle_path.read_bytes()),
            _file_row("proof_of_life_checker", checker_path, checker_path.read_bytes()),
            _file_row("receipt", receipt_path, receipt_raw),
            _file_row("lean_data", lean_path, lean_raw),
            _file_row(
                "lean_receipt_source",
                DEFAULT_LEAN_RECEIPT,
                DEFAULT_LEAN_RECEIPT.read_bytes(),
            ),
            _file_row(
                "lean_receipt_checker",
                DEFAULT_LEAN_CHECKER,
                DEFAULT_LEAN_CHECKER.read_bytes(),
            ),
        ],
        "formal_slt_commit": source["formal_slt_commit"],
        "manifest_schema": MANIFEST_SCHEMA,
        "nonclaims": EXPECTED_NONCLAIMS,
    }
    manifest_raw = canonical_json_bytes(manifest)
    return receipt_raw, manifest_raw, lean_raw


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_name, path)
    finally:
        if os.path.exists(temporary_name):
            os.unlink(temporary_name)


def _check(path: Path, expected: bytes, label: str) -> None:
    try:
        actual = path.read_bytes()
    except OSError as error:
        raise ReceiptError(f"cannot read tracked {label} at {path}: {error}") from error
    if actual != expected:
        raise ReceiptError(f"tracked {label} is stale: {path}")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        receipt_raw, manifest_raw, lean_raw = expected_artifacts(
            args.input, args.receipt, args.manifest, args.lean
        )
        if args.check:
            _check(args.receipt, receipt_raw, "receipt")
            _check(args.manifest, manifest_raw, "manifest")
            _check(args.lean, lean_raw, "Lean data")
        else:
            _atomic_write(args.receipt, receipt_raw)
            _atomic_write(args.manifest, manifest_raw)
            _atomic_write(args.lean, lean_raw)
    except (OSError, ReceiptError) as error:
        print(f"ERROR: synthetic Brier receipt refused: {error}", file=sys.stderr)
        return 1
    action = "checked" if args.check else "generated"
    print(
        f"synthetic Brier proof-of-life {action}: "
        f"{_display_path(args.receipt)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
