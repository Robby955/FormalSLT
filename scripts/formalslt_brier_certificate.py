#!/usr/bin/env python3
"""Issue and verify compact theorem-backed tabular Brier certificates.

The Lean checker is O(models), not O(observations).  Python streams and hashes
the input rows twice through independent implementations.  Lean checks the
finite posterior, dyadic logarithm bounds, half-tilt penalty, and final
statistical endpoint from the resulting exact rational summaries.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any

import formalslt_brier_tabular as preparation_engine
import verify_formalslt_brier_tabular as replay_engine

ROOT = Path(__file__).resolve().parents[1]
PROFILE = "finite-tabular-brier-half-tilt-v1"
CERTIFICATE_SCHEMA = "formalslt.certificate.v1"
CHECKER_NAME = "CheckCompactBrierCertificate.lean"
PREPARATION_NAME = "preparation.json"
CERTIFICATE_NAME = "certificate.json"
THEOREM_MODULE = ROOT / "FormalSLT/Applications/CompactHalfTiltBrierCertificate.lean"
TRAJECTORY_MODULE = (
    ROOT / "FormalSLT/StochasticDynamics/TrajectoryHalfTiltOrdinaryRiskPACBayes.lean"
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PASS_MARKER = "FORMALSLT_COMPACT_BRIER_CERTIFICATE_PASS"
BOUND_SCALE = 1_000_000
CERTIFICATE_NONCLAIMS = [
    "Lean checks exact summary arithmetic, not raw CSV or Parquet parsing",
    "prediction timing and provenance are accepted at the receipt's stated tier",
    "the bound is not future, stationary, population, or deployment risk",
    "the fixed half tilt is not coin betting or post-hoc strategy selection",
]


class CertificateError(ValueError):
    """Raised when a compact certificate cannot be issued or verified."""


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
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
        raise CertificateError(f"cannot hash {path}") from error
    return digest.hexdigest()


def rational_text(value: Fraction) -> str:
    value = Fraction(value)
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def parse_fraction(value: Any, label: str) -> Fraction:
    try:
        return preparation_engine.parse_fraction(value, label)
    except preparation_engine.PreparationError as error:
        raise CertificateError(str(error)) from error


def lean_rational(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return f"({value.numerator} : Real)"
    return f"(({value.numerator} : Real) / {value.denominator})"


def dyadic_factor(value: Fraction) -> tuple[int, Fraction]:
    if value <= 0:
        raise CertificateError("dyadic logarithm inputs must be positive")
    exponent = 0
    remainder = Fraction(value)
    while remainder >= 2:
        remainder /= 2
        exponent += 1
    return exponent, remainder


def dyadic_log_upper(exponent: int, remainder: Fraction) -> Fraction:
    return Fraction(exponent * 7, 10) + remainder - 1


def strict_decimal_ceiling(value: Fraction, scale: int = BOUND_SCALE) -> Fraction:
    scaled = value * scale
    quotient = scaled.numerator // scaled.denominator
    return Fraction(quotient + 1, scale)


def _git_revision() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else "UNAVAILABLE"


def _model_declarations(count: int) -> str:
    constructors = " | ".join(f"m{index}" for index in range(count))
    return f"inductive Model | {constructors}\n  deriving DecidableEq, Fintype"


def _model_univ(count: int) -> str:
    members = ", ".join(f"Model.m{index}" for index in range(count))
    return (
        "theorem model_univ : (Finset.univ : Finset Model) = "
        f"{{{members}}} := by decide"
    )


def _piecewise_definition(name: str, result_type: str, values: list[str]) -> str:
    rows = [f"def {name} : Model → {result_type}"]
    rows.extend(f"  | .m{index} => {value}" for index, value in enumerate(values))
    return "\n".join(rows)


def _pmf_sum_tactic(name: str, model_count: int) -> str:
    del model_count
    lines = ["rw [model_univ]", f"simp [{name}] <;> norm_num"]
    return "\n    ".join(lines)


def checker_source(
    protocol: dict[str, Any], preparation: dict[str, Any]
) -> tuple[str, dict[str, Fraction]]:
    model_ids = [model["id"] for model in protocol["models"]]
    statistics = protocol["statistics"]
    prior = [
        parse_fraction(statistics["prior"][model], f"prior.{model}")
        for model in model_ids
    ]
    posterior = [
        parse_fraction(statistics["posterior"][model], f"posterior.{model}")
        for model in model_ids
    ]
    delta = parse_fraction(preparation["statistics"]["delta"], "preparation delta")
    empirical = parse_fraction(
        preparation["statistics"]["posterior_empirical_brier_risk"],
        "preparation empirical risk",
    )
    quadratic = parse_fraction(
        preparation["statistics"]["posterior_suffix_predictor_quadratic_variation"],
        "preparation quadratic variation",
    )
    horizon = preparation["data"]["observations"]
    if isinstance(horizon, bool) or not isinstance(horizon, int) or horizon <= 0:
        raise CertificateError("preparation horizon must be a positive integer")

    exponents: list[int] = []
    remainders: list[Fraction] = []
    for rho, pi in zip(posterior, prior, strict=True):
        if rho == 0:
            exponents.append(0)
            remainders.append(Fraction(1))
        else:
            exponent, remainder = dyadic_factor(rho / pi)
            exponents.append(exponent)
            remainders.append(remainder)
    kl_upper = sum(
        (
            rho * dyadic_log_upper(exponent, remainder)
            for rho, exponent, remainder in zip(
                posterior, exponents, remainders, strict=True
            )
        ),
        Fraction(0),
    )
    confidence_exponent, confidence_remainder = dyadic_factor(1 / delta)
    confidence_log_upper = dyadic_log_upper(confidence_exponent, confidence_remainder)
    arithmetic_upper = empirical + (
        kl_upper + confidence_log_upper + Fraction(1, 5) * quadratic
    ) / (Fraction(1, 2) * horizon)
    certified_bound = strict_decimal_ceiling(arithmetic_upper)

    prior_rows = [lean_rational(value) for value in prior]
    posterior_rows = [lean_rational(value) for value in posterior]
    exponent_rows = [str(value) for value in exponents]
    remainder_rows = [lean_rational(value) for value in remainders]
    protocol_digest = preparation["protocol"]["sha256"]
    stream_digest = preparation["data"]["normalized_stream_sha256"]
    source = f"""import FormalSLT.Applications.CompactHalfTiltBrierCertificate

open FormalSLT.Applications.CompactHalfTiltBrierCertificate
open FormalSLT.PACBayesKL

namespace FormalSLT.Generated.CompactBrierCertificate

noncomputable section

{_model_declarations(len(model_ids))}

{_model_univ(len(model_ids))}

{_piecewise_definition("prior", "Real", prior_rows)}

{_piecewise_definition("posterior", "Real", posterior_rows)}

{_piecewise_definition("logExponent", "Nat", exponent_rows)}

{_piecewise_definition("logRemainder", "Real", remainder_rows)}

def empiricalRisk : Real := {lean_rational(empirical)}
def quadraticVariation : Real := {lean_rational(quadratic)}
def confidenceDelta : Real := {lean_rational(delta)}
def horizon : Nat := {horizon}
def klUpper : Real := {lean_rational(kl_upper)}
def confidenceLogUpper : Real := {lean_rational(confidence_log_upper)}
def certifiedUpperRisk : Real := {lean_rational(certified_bound)}

def protocolSha256 : String := \"{protocol_digest}\"
def normalizedStreamSha256 : String := \"{stream_digest}\"

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro model
    cases model <;> norm_num [prior]
  · {_pmf_sum_tactic("prior", len(model_ids))}
  · intro model
    cases model <;> norm_num [prior]

theorem posterior_isPMF : IsPMF posterior := by
  refine ⟨?_, ?_⟩
  · intro model
    cases model <;> norm_num [posterior]
  · {_pmf_sum_tactic("posterior", len(model_ids))}

theorem certificateInputsValid :
    IsFullSupportPMF prior ∧ IsPMF posterior ∧
      0 < confidenceDelta ∧ 0 < horizon := by
  exact ⟨prior_isFullSupportPMF, posterior_isPMF, by
    norm_num [confidenceDelta], by norm_num [horizon]⟩

theorem posterior_ratio_factorization :
    ∀ model, posterior model = 0 ∨
      (0 < logRemainder model ∧
        posterior model / prior model =
          (2 : Real) ^ logExponent model * logRemainder model) := by
  intro model
  cases model <;>
    norm_num [posterior, prior, logExponent, logRemainder]

theorem posterior_kl_le : klDiv posterior prior ≤ klUpper := by
  calc
    klDiv posterior prior ≤
        posteriorAverage posterior
          (fun model => dyadicLogUpper
            (logExponent model) (logRemainder model)) :=
      klDiv_le_dyadicLogUpper posterior_isPMF logExponent logRemainder
        posterior_ratio_factorization
    _ = klUpper := by
      unfold posteriorAverage
      rw [model_univ]
      simp [posterior, logExponent, logRemainder,
        dyadicLogUpper, klUpper]

theorem confidence_log_le :
    Real.log (1 / confidenceDelta) ≤ confidenceLogUpper := by
  calc
    Real.log (1 / confidenceDelta) =
        Real.log ((2 : Real) ^ {confidence_exponent} *
          {lean_rational(confidence_remainder)}) := by
      congr 1
      norm_num [confidenceDelta]
    _ ≤ dyadicLogUpper {confidence_exponent}
        {lean_rational(confidence_remainder)} :=
      log_two_pow_mul_le_dyadicLogUpper {confidence_exponent} (by norm_num)
    _ = confidenceLogUpper := by
      norm_num [dyadicLogUpper, confidenceLogUpper]

theorem certificateBoundary_lt :
    summaryEndpoint empiricalRisk quadraticVariation posterior prior
        confidenceDelta horizon < certifiedUpperRisk := by
  apply summaryEndpoint_lt_of_bounds (klUpper := klUpper)
    (logUpper := confidenceLogUpper)
  · norm_num [horizon]
  · norm_num [quadraticVariation]
  · exact posterior_kl_le
  · exact confidence_log_le
  · norm_num [empiricalRisk, quadraticVariation, klUpper,
      confidenceLogUpper, certifiedUpperRisk, horizon]

#print axioms certificateBoundary_lt
#print axioms certificateInputsValid
#eval IO.println \"{PASS_MARKER}\"

end

end FormalSLT.Generated.CompactBrierCertificate
"""
    return source, {
        "arithmetic_upper": arithmetic_upper,
        "certified_bound": certified_bound,
        "confidence_log_upper": confidence_log_upper,
        "kl_upper": kl_upper,
    }


def _lean_command(checker: Path) -> list[str]:
    return [str(Path.home() / ".elan/bin/lake"), "env", "lean", str(checker)]


def run_checker(checker: Path) -> str:
    command = _lean_command(checker)
    environment = os.environ.copy()
    result = subprocess.run(
        command,
        cwd=ROOT,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        tail = "\n".join(result.stdout.splitlines()[-30:])
        raise CertificateError(f"Lean checker failed:\n{tail}")
    if PASS_MARKER not in result.stdout:
        raise CertificateError("Lean checker did not emit its PASS marker")
    match = re.search(
        r"certificateBoundary_lt' depends on axioms: \[([^\]]*)\]", result.stdout
    )
    if match is None:
        raise CertificateError("Lean checker did not print the certificate axiom set")
    axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
    if axioms != ALLOWED_AXIOMS:
        raise CertificateError(f"unexpected certificate axioms: {sorted(axioms)}")
    return result.stdout


def _canonical_object(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    def reject_float(value: str) -> None:
        raise CertificateError(f"floating-point number in {label}: {value}")

    def reject_constant(value: str) -> None:
        raise CertificateError(f"non-finite number in {label}: {value}")

    def unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise CertificateError(f"duplicate key in {label}: {key}")
            result[key] = value
        return result

    try:
        raw = path.read_bytes()
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=reject_float,
            parse_constant=reject_constant,
            object_pairs_hook=unique_pairs,
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CertificateError(f"cannot read {label}: {path}") from error
    if not isinstance(value, dict) or canonical_json_bytes(value) != raw:
        raise CertificateError(f"{label} must be a canonical JSON object")
    return value, raw


def issue(protocol_path: Path, data_path: Path, output: Path) -> Path:
    output = output.resolve()
    if output.exists():
        raise CertificateError(f"refusing to overwrite existing output: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{output.name}.", dir=output.parent))
    try:
        try:
            preparation = preparation_engine.prepare(protocol_path, data_path)
        except preparation_engine.PreparationError as error:
            raise CertificateError(str(error)) from error
        preparation_path = staging / PREPARATION_NAME
        preparation_raw = preparation_engine.canonical_json_bytes(preparation)
        preparation_engine.atomic_write(preparation_path, preparation_raw)
        try:
            replay_engine.verify(preparation_path, protocol_path, data_path)
        except replay_engine.ReplayError as error:
            raise CertificateError(f"independent replay failed: {error}") from error
        try:
            protocol, protocol_raw = preparation_engine.load_protocol(protocol_path)
        except preparation_engine.PreparationError as error:
            raise CertificateError(str(error)) from error
        protocol_name = f"protocol{protocol_path.suffix.lower()}"
        (staging / protocol_name).write_bytes(protocol_raw)
        source, bounds = checker_source(protocol, preparation)
        checker_path = staging / CHECKER_NAME
        checker_path.write_text(source, encoding="utf-8")
        run_checker(checker_path)

        provenance = protocol["provenance"]
        certificate = {
            "artifact_status": "CERTIFIED",
            "certificate_profile": PROFILE,
            "claim": {
                "confidence": rational_text(
                    1 - parse_fraction(preparation["statistics"]["delta"], "delta")
                ),
                "quantity": preparation["claim"]["quantity"],
                "upper_bound": rational_text(bounds["certified_bound"]),
            },
            "data": {
                **preparation["data"],
                "provenance": provenance,
            },
            "formal_slt": {
                "commit": _git_revision(),
                "lake_manifest_sha256": sha256_file(ROOT / "lake-manifest.json"),
                "lean_toolchain_sha256": sha256_file(ROOT / "lean-toolchain"),
                "theorem": (
                    "FormalSLT.StochasticDynamics."
                    "exists_trajectoryHalfTiltPACBayes_ordinaryRisk_selected_event"
                ),
                "theorem_module_sha256": sha256_file(TRAJECTORY_MODULE),
            },
            "kernel": {
                "allowed_axioms": sorted(ALLOWED_AXIOMS),
                "checker": CHECKER_NAME,
                "checker_sha256": sha256_file(checker_path),
                "result": "PASS",
                "summary_module_sha256": sha256_file(THEOREM_MODULE),
            },
            "nonclaims": CERTIFICATE_NONCLAIMS,
            "protocol": {
                **preparation["protocol"],
                "file": protocol_name,
            },
            "replay": {
                "independent_replay": "PASS",
                "preparation": PREPARATION_NAME,
                "preparation_sha256": sha256_bytes(preparation_raw),
                "verifier_sha256": sha256_file(
                    ROOT / "scripts/verify_formalslt_brier_tabular.py"
                ),
            },
            "schema_version": CERTIFICATE_SCHEMA,
            "statistics": {
                **preparation["statistics"],
                "confidence_log_upper": rational_text(bounds["confidence_log_upper"]),
                "kl_upper": rational_text(bounds["kl_upper"]),
                "rational_arithmetic_upper": rational_text(bounds["arithmetic_upper"]),
            },
        }
        certificate_path = staging / CERTIFICATE_NAME
        preparation_engine.atomic_write(
            certificate_path, canonical_json_bytes(certificate)
        )
        os.replace(staging, output)
        return output / CERTIFICATE_NAME
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def verify(
    certificate_path: Path,
    protocol_path: Path | None = None,
    data_path: Path | None = None,
) -> dict[str, Any]:
    certificate, _raw = _canonical_object(certificate_path, "certificate")
    if certificate.get("schema_version") != CERTIFICATE_SCHEMA:
        raise CertificateError("unsupported certificate schema")
    if certificate.get("certificate_profile") != PROFILE:
        raise CertificateError("unsupported compact certificate profile")
    directory = certificate_path.resolve().parent
    if certificate.get("artifact_status") != "CERTIFIED":
        raise CertificateError("certificate status is not CERTIFIED")
    if certificate.get("kernel", {}).get("result") != "PASS":
        raise CertificateError("kernel result is not PASS")
    if set(certificate.get("kernel", {}).get("allowed_axioms", [])) != ALLOWED_AXIOMS:
        raise CertificateError("recorded axiom set mismatch")
    if certificate.get("replay", {}).get("independent_replay") != "PASS":
        raise CertificateError("recorded independent replay is not PASS")
    if certificate.get("kernel", {}).get("checker") != CHECKER_NAME:
        raise CertificateError("checker filename mismatch")
    if certificate.get("replay", {}).get("preparation") != PREPARATION_NAME:
        raise CertificateError("preparation filename mismatch")
    protocol_name = certificate.get("protocol", {}).get("file")
    if protocol_name not in {"protocol.json", "protocol.yaml", "protocol.yml"}:
        raise CertificateError("stored protocol filename mismatch")
    checker_path = directory / CHECKER_NAME
    if sha256_file(checker_path) != certificate["kernel"]["checker_sha256"]:
        raise CertificateError("checker digest mismatch")
    preparation_path = directory / PREPARATION_NAME
    if sha256_file(preparation_path) != certificate["replay"]["preparation_sha256"]:
        raise CertificateError("preparation digest mismatch")
    if (
        sha256_file(TRAJECTORY_MODULE)
        != certificate["formal_slt"]["theorem_module_sha256"]
    ):
        raise CertificateError("trajectory theorem module digest mismatch")
    if (
        sha256_file(ROOT / "lake-manifest.json")
        != certificate["formal_slt"]["lake_manifest_sha256"]
    ):
        raise CertificateError("lake manifest digest mismatch")
    if (
        sha256_file(ROOT / "lean-toolchain")
        != certificate["formal_slt"]["lean_toolchain_sha256"]
    ):
        raise CertificateError("Lean toolchain digest mismatch")
    if sha256_file(THEOREM_MODULE) != certificate["kernel"]["summary_module_sha256"]:
        raise CertificateError("summary theorem module digest mismatch")
    if (
        sha256_file(ROOT / "scripts/verify_formalslt_brier_tabular.py")
        != certificate["replay"]["verifier_sha256"]
    ):
        raise CertificateError("independent verifier digest mismatch")
    preparation, preparation_raw = _canonical_object(preparation_path, "preparation")
    stored_protocol_path = directory / protocol_name
    try:
        stored_protocol, stored_protocol_raw = preparation_engine.load_protocol(
            stored_protocol_path
        )
    except preparation_engine.PreparationError as error:
        raise CertificateError(str(error)) from error
    if sha256_bytes(stored_protocol_raw) != certificate["protocol"]["sha256"]:
        raise CertificateError("stored protocol digest mismatch")
    if certificate["protocol"]["sha256"] != preparation["protocol"]["sha256"]:
        raise CertificateError("certificate/preparation protocol mismatch")
    expected_source, expected_bounds = checker_source(stored_protocol, preparation)
    try:
        actual_source = checker_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise CertificateError("cannot read generated Lean checker") from error
    if actual_source != expected_source:
        raise CertificateError("generated Lean checker does not match bound inputs")
    expected_statistics = {
        **preparation["statistics"],
        "confidence_log_upper": rational_text(expected_bounds["confidence_log_upper"]),
        "kl_upper": rational_text(expected_bounds["kl_upper"]),
        "rational_arithmetic_upper": rational_text(expected_bounds["arithmetic_upper"]),
    }
    if certificate.get("statistics") != expected_statistics:
        raise CertificateError("certificate statistics mismatch")
    expected_data = {
        **preparation["data"],
        "provenance": stored_protocol["provenance"],
    }
    if certificate.get("data") != expected_data:
        raise CertificateError("certificate data binding mismatch")
    delta = parse_fraction(preparation["statistics"]["delta"], "delta")
    expected_claim = {
        "confidence": rational_text(1 - delta),
        "quantity": preparation["claim"]["quantity"],
        "upper_bound": rational_text(expected_bounds["certified_bound"]),
    }
    if certificate.get("claim") != expected_claim:
        raise CertificateError("certificate claim mismatch")
    if certificate.get("nonclaims") != CERTIFICATE_NONCLAIMS:
        raise CertificateError("certificate nonclaims mismatch")
    run_checker(checker_path)
    if (protocol_path is None) != (data_path is None):
        raise CertificateError("protocol and data must be supplied together for replay")
    if protocol_path is not None and data_path is not None:
        try:
            _external_protocol, external_raw = preparation_engine.load_protocol(
                protocol_path
            )
        except preparation_engine.PreparationError as error:
            raise CertificateError(str(error)) from error
        if sha256_bytes(external_raw) != certificate["protocol"]["sha256"]:
            raise CertificateError("external protocol digest mismatch")
        try:
            replay_engine.verify(preparation_path, protocol_path, data_path)
        except replay_engine.ReplayError as error:
            raise CertificateError(f"independent replay failed: {error}") from error
    return certificate
