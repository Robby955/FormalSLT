#!/usr/bin/env python3
"""Exact, presentation-safe summaries for compact Brier certificates.

The summary is a derived view of an already verified certificate or of a live
preview.  It keeps exact rational values alongside fixed decimal renderings so
frontends never need to reconstruct the statistical formula with floating
point arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, Mapping

import formalslt_brier_certificate as certificate_engine


SUMMARY_SCHEMA = "formalslt.brier-certificate-summary.v1"
PREVIEW_STATUS = "PREVIEW_NOT_CERTIFIED"
CERTIFICATE_STATUS = "DERIVED_FROM_CERTIFICATE"
DECIMAL_PLACES = 12


class SummaryError(ValueError):
    """Raised when a source artifact cannot support an exact summary."""


def _fraction(value: Any, label: str) -> Fraction:
    try:
        parsed = certificate_engine.parse_fraction(value, label)
    except certificate_engine.CertificateError as error:
        raise SummaryError(str(error)) from error
    if parsed < 0:
        raise SummaryError(f"{label} must be nonnegative")
    return parsed


def _rational(value: Fraction) -> str:
    value = Fraction(value)
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def _decimal(value: Fraction, places: int = DECIMAL_PLACES) -> str:
    """Render a nonnegative rational with deterministic half-up rounding."""

    scale = 10**places
    scaled_numerator = value.numerator * scale
    rounded = (2 * scaled_numerator + value.denominator) // (2 * value.denominator)
    whole, decimal = divmod(rounded, scale)
    return f"{whole}.{decimal:0{places}d}"


def _value(value: Fraction) -> dict[str, str]:
    return {
        "decimal": _decimal(value),
        "percent_decimal": _decimal(100 * value, 10),
        "rational": _rational(value),
    }


def _component_summary(
    *,
    empirical: Fraction,
    kl_upper: Fraction,
    confidence_log_upper: Fraction,
    quadratic_variation_upper: Fraction,
    tilt: Fraction,
    observations: int,
    claimed_upper: Fraction | None,
    recorded_arithmetic_upper: Fraction | None,
) -> dict[str, dict[str, str] | None]:
    if observations <= 0:
        raise SummaryError("observations must be a positive integer")
    if tilt != Fraction(1, 2):
        raise SummaryError("the compact summary supports the half-tilt profile only")
    denominator = tilt * observations
    selection = kl_upper / denominator
    confidence = confidence_log_upper / denominator
    variation = Fraction(1, 5) * quadratic_variation_upper / denominator
    arithmetic = empirical + selection + confidence + variation
    if recorded_arithmetic_upper is not None and arithmetic != recorded_arithmetic_upper:
        raise SummaryError("recorded arithmetic upper bound disagrees with its terms")

    rounding: Fraction | None = None
    margin: Fraction | None = None
    if claimed_upper is not None:
        if claimed_upper <= arithmetic:
            raise SummaryError("certificate upper bound must strictly exceed arithmetic")
        if claimed_upper != certificate_engine.strict_decimal_ceiling(arithmetic):
            raise SummaryError("certificate upper bound is not the strict decimal ceiling")
        rounding = claimed_upper - arithmetic
        margin = claimed_upper - empirical

    return {
        "arithmetic_upper": _value(arithmetic),
        "confidence_cost": _value(confidence),
        "observed_risk": _value(empirical),
        "rounding_slack": None if rounding is None else _value(rounding),
        "selection_cost": _value(selection),
        "total_margin": None if margin is None else _value(margin),
        "variation_cost": _value(variation),
    }


def certificate_summary(
    certificate: Mapping[str, Any],
    *,
    certificate_sha256: str,
    selected_model: str | None = None,
) -> dict[str, Any]:
    """Build an exact decomposition bound to one checked certificate digest."""

    if certificate.get("schema_version") != certificate_engine.CERTIFICATE_SCHEMA:
        raise SummaryError("unsupported certificate schema")
    if certificate.get("certificate_profile") != certificate_engine.PROFILE:
        raise SummaryError("unsupported certificate profile")
    if certificate.get("artifact_status") != "CERTIFIED":
        raise SummaryError("source artifact is not certified")
    if certificate.get("kernel", {}).get("result") != "PASS":
        raise SummaryError("source certificate kernel result is not PASS")
    if certificate.get("replay", {}).get("independent_replay") != "PASS":
        raise SummaryError("source certificate replay result is not PASS")
    if len(certificate_sha256) != 64 or any(
        character not in "0123456789abcdef" for character in certificate_sha256
    ):
        raise SummaryError("certificate_sha256 must be a lowercase SHA-256 digest")

    statistics = certificate.get("statistics")
    claim = certificate.get("claim")
    data = certificate.get("data")
    if not isinstance(statistics, Mapping) or not isinstance(claim, Mapping):
        raise SummaryError("certificate statistics and claim must be objects")
    if not isinstance(data, Mapping):
        raise SummaryError("certificate data must be an object")
    observations = data.get("observations")
    if isinstance(observations, bool) or not isinstance(observations, int):
        raise SummaryError("certificate observations must be an integer")

    empirical = _fraction(
        statistics.get("posterior_empirical_brier_risk"), "empirical risk"
    )
    kl_upper = _fraction(statistics.get("kl_upper"), "KL upper bound")
    confidence_log_upper = _fraction(
        statistics.get("confidence_log_upper"), "confidence log upper bound"
    )
    variation_upper = _fraction(
        statistics.get("posterior_suffix_predictor_quadratic_variation_upper"),
        "quadratic variation upper bound",
    )
    tilt = _fraction(statistics.get("tilt"), "tilt")
    arithmetic = _fraction(
        statistics.get("rational_arithmetic_upper"), "arithmetic upper bound"
    )
    claimed_upper = _fraction(claim.get("upper_bound"), "claim upper bound")
    delta = _fraction(statistics.get("delta"), "delta")
    confidence = _fraction(claim.get("confidence"), "claim confidence")
    if confidence != 1 - delta:
        raise SummaryError("claim confidence disagrees with delta")

    provenance = data.get("provenance")
    if not isinstance(provenance, Mapping):
        raise SummaryError("certificate provenance must be an object")
    components = _component_summary(
        empirical=empirical,
        kl_upper=kl_upper,
        confidence_log_upper=confidence_log_upper,
        quadratic_variation_upper=variation_upper,
        tilt=tilt,
        observations=observations,
        claimed_upper=claimed_upper,
        recorded_arithmetic_upper=arithmetic,
    )
    return {
        "artifact_status": CERTIFICATE_STATUS,
        "certificate": {
            "artifact_status": certificate["artifact_status"],
            "sha256": certificate_sha256,
            "schema_version": certificate["schema_version"],
        },
        "claim": {
            "confidence": _value(confidence),
            "quantity": claim.get("quantity"),
            "upper_bound": _value(claimed_upper),
        },
        "components": components,
        "observations": observations,
        "provenance": dict(provenance),
        "schema_version": SUMMARY_SCHEMA,
        "selected_model": selected_model,
        "verification": {
            "independent_replay": certificate["replay"]["independent_replay"],
            "lean_kernel": certificate["kernel"]["result"],
            "scope": "derived view; exact values are bound to certificate.sha256",
        },
    }


def preview_summary(
    snapshot: Mapping[str, Any],
    *,
    confidence: Fraction,
    tilt: Fraction,
    provenance: Mapping[str, Any],
) -> dict[str, Any]:
    """Build a non-certified decomposition for one incremental snapshot."""

    if snapshot.get("artifact_status") != PREVIEW_STATUS:
        raise SummaryError("source snapshot is not a live preview")
    selected = snapshot.get("selected")
    if not isinstance(selected, Mapping):
        raise SummaryError("snapshot selected record must be an object")
    observations = snapshot.get("observations")
    if isinstance(observations, bool) or not isinstance(observations, int):
        raise SummaryError("snapshot observations must be an integer")
    boundary_raw = selected.get("boundary_upper")
    boundary = (
        None if boundary_raw is None else _fraction(boundary_raw, "preview boundary")
    )
    components = _component_summary(
        empirical=_fraction(selected.get("empirical_brier_risk"), "empirical risk"),
        kl_upper=_fraction(selected.get("kl_upper"), "KL upper bound"),
        confidence_log_upper=_fraction(
            selected.get("confidence_log_upper"), "confidence log upper bound"
        ),
        quadratic_variation_upper=_fraction(
            selected.get("quadratic_variation_upper"),
            "quadratic variation upper bound",
        ),
        tilt=tilt,
        observations=observations,
        claimed_upper=boundary,
        recorded_arithmetic_upper=None,
    )
    return {
        "artifact_status": PREVIEW_STATUS,
        "claim": {
            "confidence": _value(confidence),
            "quantity": snapshot.get("claim", {}).get("quantity"),
            "upper_bound": None if boundary is None else _value(boundary),
        },
        "components": components,
        "observations": observations,
        "provenance": dict(provenance),
        "schema_version": SUMMARY_SCHEMA,
        "selected_model": selected.get("model_id"),
        "verification": {
            "independent_replay": "NOT_RUN",
            "lean_kernel": "NOT_RUN",
            "scope": "live arithmetic preview; not a statistical certificate",
        },
    }
