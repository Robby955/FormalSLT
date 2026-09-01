#!/usr/bin/env python3
"""Incremental exact previews for registered tabular Brier protocols.

This module is the online computation layer, not a certificate checker.  It
maintains exact per-model loss and predictable quadratic-variation summaries,
supports point-posterior model selection after each observed prefix, and emits
the same conservative half-tilt expression used by the compact certificate.
Independent replay and Lean verification remain separate operations.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

import formalslt_brier_tabular as tabular


TRACE_SCHEMA = "formalslt.brier-monitor-trace.v1"
SNAPSHOT_SCHEMA = "formalslt.brier-monitor-snapshot.v1"
STATUS = "PREVIEW_NOT_CERTIFIED"
BOUND_SCALE = 1_000_000
MINIMUM_CERTIFICATE_HORIZON = 4
NONCLAIMS = [
    "online arithmetic only; preview boundaries are not Lean certificates",
    "prediction timing and provenance retain the protocol's stated evidence tier",
    "the preview is not future, stationary, population, or deployment risk",
    "the fixed half tilt is not coin betting or post-hoc strategy selection",
]


class StreamingMonitorError(ValueError):
    """Raised when a streaming update or replay is invalid."""


@dataclass
class _ModelState:
    loss_sum: Fraction = Fraction(0)
    quadratic_variation_upper: Fraction = Fraction(0)


def _integer(value: Any, label: str) -> int:
    if isinstance(value, bool):
        raise StreamingMonitorError(f"{label} must be an integer")
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        stripped = value.strip()
        if stripped and (
            stripped.isdigit()
            or (stripped.startswith("-") and stripped[1:].isdigit())
        ):
            return int(stripped)
    raise StreamingMonitorError(f"{label} must be an integer")


def _dyadic_factor(value: Fraction) -> tuple[int, Fraction]:
    if value <= 0:
        raise StreamingMonitorError("dyadic logarithm inputs must be positive")
    exponent = 0
    remainder = Fraction(value)
    while remainder >= 2:
        remainder /= 2
        exponent += 1
    return exponent, remainder


def _dyadic_log_upper(value: Fraction) -> Fraction:
    exponent, remainder = _dyadic_factor(value)
    return Fraction(exponent * 7, 10) + remainder - 1


def _kl_upper(
    weights: Mapping[str, Fraction], prior: Mapping[str, Fraction]
) -> Fraction:
    return sum(
        (
            weight * _dyadic_log_upper(weight / prior[model_id])
            for model_id, weight in weights.items()
            if weight > 0
        ),
        Fraction(0),
    )


def _strict_decimal_ceiling(
    value: Fraction, scale: int = BOUND_SCALE
) -> Fraction:
    scaled = value * scale
    return Fraction(scaled.numerator // scaled.denominator + 1, scale)


def _rational(value: Fraction) -> str:
    return tabular.rational_text(Fraction(value))


class StreamingBrierMonitor:
    """Exact incremental state for one validated Brier-monitor protocol."""

    def __init__(
        self,
        protocol: dict[str, Any],
        *,
        protocol_sha256: str,
    ) -> None:
        self.protocol = protocol
        self.protocol_sha256 = protocol_sha256
        self.model_ids = tuple(model["id"] for model in protocol["models"])
        self.columns = {
            model["id"]: model["column"] for model in protocol["models"]
        }
        self.scale = protocol["data"]["prediction_scale"]
        statistics = protocol["statistics"]
        self.prior = {
            model_id: tabular.parse_fraction(
                statistics["prior"][model_id], f"prior.{model_id}"
            )
            for model_id in self.model_ids
        }
        self.protocol_posterior = {
            model_id: tabular.parse_fraction(
                statistics["posterior"][model_id], f"posterior.{model_id}"
            )
            for model_id in self.model_ids
        }
        self.delta = tabular.parse_fraction(statistics["delta"], "delta")
        self.tilt = tabular.parse_fraction(statistics["tilt"], "tilt")
        self._states = {model_id: _ModelState() for model_id in self.model_ids}
        self._protocol_loss_sum = Fraction(0)
        self._protocol_quadratic_variation_upper = Fraction(0)
        self._normalized_stream = hashlib.sha256()
        self.observations = 0
        self.last_time: int | None = None
        self.selected_model: str | None = None
        self.selection_switches = 0

    @classmethod
    def from_protocol_path(cls, path: Path) -> "StreamingBrierMonitor":
        try:
            protocol, raw = tabular.load_protocol(path)
        except tabular.PreparationError as error:
            raise StreamingMonitorError(str(error)) from error
        return cls(
            protocol,
            protocol_sha256=tabular.sha256_bytes(raw),
        )

    def update(
        self,
        *,
        time: Any,
        outcome: Any,
        predictions: Mapping[str, Any],
    ) -> None:
        """Consume one prediction-before-outcome row."""

        row_number = self.observations + 1
        time_value = _integer(time, f"row {row_number} time")
        if self.last_time is not None and time_value <= self.last_time:
            raise StreamingMonitorError(
                f"row {row_number} time is not strictly increasing"
            )
        outcome_value = _integer(outcome, f"row {row_number} outcome")
        if outcome_value not in (0, 1):
            raise StreamingMonitorError(
                f"row {row_number} outcome must be 0 or 1"
            )
        if set(predictions) != set(self.model_ids):
            missing = sorted(set(self.model_ids) - set(predictions))
            extra = sorted(set(predictions) - set(self.model_ids))
            raise StreamingMonitorError(
                "prediction keys mismatch; "
                f"missing={missing}, extra={extra}"
            )

        scaled_by_model: dict[str, int] = {}
        for model_id in self.model_ids:
            scaled = _integer(
                predictions[model_id],
                f"row {row_number} prediction {model_id}",
            )
            if not 0 <= scaled <= self.scale:
                raise StreamingMonitorError(
                    f"row {row_number} prediction {model_id} must lie "
                    f"in [0,{self.scale}]"
                )
            scaled_by_model[model_id] = scaled

        scaled_predictions: list[int] = []
        row_losses: dict[str, Fraction] = {}
        row_protocol_variation = Fraction(0)
        for model_id in self.model_ids:
            scaled = scaled_by_model[model_id]
            state = self._states[model_id]
            loss = (Fraction(scaled, self.scale) - outcome_value) ** 2
            predictor = (
                Fraction(1, 2)
                if self.observations == 0
                else state.loss_sum / self.observations
            )
            squared_discrepancy = (loss - predictor) ** 2
            state.quadratic_variation_upper += tabular.ceil_to_grid(
                squared_discrepancy,
                tabular.QUADRATIC_VARIATION_GRID,
            )
            row_protocol_variation += (
                self.protocol_posterior[model_id] * squared_discrepancy
            )
            state.loss_sum += loss
            row_losses[model_id] = loss
            scaled_predictions.append(scaled)

        self._protocol_quadratic_variation_upper += tabular.ceil_to_grid(
            row_protocol_variation,
            tabular.QUADRATIC_VARIATION_GRID,
        )
        self._protocol_loss_sum += sum(
            (
                self.protocol_posterior[model_id] * row_losses[model_id]
                for model_id in self.model_ids
            ),
            Fraction(0),
        )
        self._normalized_stream.update(
            tabular.canonical_json_bytes(
                {
                    "outcome": outcome_value,
                    "predictions": scaled_predictions,
                    "time": time_value,
                }
            )
        )
        self.observations = row_number
        self.last_time = time_value
        selected = min(
            self.model_ids,
            key=lambda model_id: self._states[model_id].loss_sum,
        )
        if self.selected_model is not None and selected != self.selected_model:
            self.selection_switches += 1
        self.selected_model = selected

    def update_row(self, row: Mapping[str, Any]) -> None:
        data = self.protocol["data"]
        self.update(
            time=row.get(data["time_column"]),
            outcome=row.get(data["outcome_column"]),
            predictions={
                model_id: row.get(self.columns[model_id])
                for model_id in self.model_ids
            },
        )

    def _preview(
        self,
        empirical: Fraction,
        quadratic_variation_upper: Fraction,
        weights: Mapping[str, Fraction],
    ) -> dict[str, str | None]:
        kl_upper = _kl_upper(weights, self.prior)
        confidence_log_upper = _dyadic_log_upper(1 / self.delta)
        if self.observations < MINIMUM_CERTIFICATE_HORIZON:
            boundary: Fraction | None = None
        else:
            arithmetic = empirical + (
                kl_upper
                + confidence_log_upper
                + Fraction(1, 5) * quadratic_variation_upper
            ) / (self.tilt * self.observations)
            boundary = _strict_decimal_ceiling(arithmetic)
        return {
            "boundary_upper": None if boundary is None else _rational(boundary),
            "confidence_log_upper": _rational(confidence_log_upper),
            "empirical_brier_risk": _rational(empirical),
            "kl_upper": _rational(kl_upper),
            "quadratic_variation_upper": _rational(
                quadratic_variation_upper
            ),
        }

    def snapshot(self, *, include_models: bool = True) -> dict[str, Any]:
        if self.observations == 0 or self.selected_model is None:
            raise StreamingMonitorError("cannot snapshot an empty monitor")
        model_records: dict[str, dict[str, str | None]] = {}
        if include_models:
            for model_id in self.model_ids:
                state = self._states[model_id]
                point = {
                    candidate: Fraction(int(candidate == model_id))
                    for candidate in self.model_ids
                }
                model_records[model_id] = self._preview(
                    state.loss_sum / self.observations,
                    state.quadratic_variation_upper,
                    point,
                )
        selected_state = self._states[self.selected_model]
        selected_weights = {
            model_id: Fraction(int(model_id == self.selected_model))
            for model_id in self.model_ids
        }
        selected = {
            "model_id": self.selected_model,
            "rule": "minimum prefix cumulative Brier loss; protocol order breaks ties",
            **self._preview(
                selected_state.loss_sum / self.observations,
                selected_state.quadratic_variation_upper,
                selected_weights,
            ),
        }
        protocol_preview = self._preview(
            self._protocol_loss_sum / self.observations,
            self._protocol_quadratic_variation_upper,
            self.protocol_posterior,
        )
        return {
            "artifact_status": STATUS,
            "claim": {
                "quantity": tabular.CLAIM_QUANTITY,
                "status": "NOT_CERTIFIED",
            },
            "last_time": self.last_time,
            "models": model_records,
            "normalized_stream_sha256": self._normalized_stream.hexdigest(),
            "observations": self.observations,
            "protocol_id": self.protocol["protocol_id"],
            "protocol_posterior": protocol_preview,
            "schema_version": SNAPSHOT_SCHEMA,
            "selected": selected,
            "selection_switches": self.selection_switches,
        }


def replay(
    protocol_path: Path,
    data_path: Path,
    *,
    every: int,
) -> dict[str, Any]:
    """Replay a file through the incremental engine and return a compact trace."""

    if every <= 0:
        raise StreamingMonitorError("snapshot interval must be positive")
    monitor = StreamingBrierMonitor.from_protocol_path(protocol_path)
    points: list[dict[str, Any]] = []
    try:
        rows = tabular.iter_rows(monitor.protocol, data_path)
        for row in rows:
            monitor.update_row(row)
            if (
                monitor.observations >= MINIMUM_CERTIFICATE_HORIZON
                and monitor.observations % every == 0
            ):
                points.append(monitor.snapshot(include_models=False))
    except tabular.PreparationError as error:
        raise StreamingMonitorError(str(error)) from error
    if monitor.observations < MINIMUM_CERTIFICATE_HORIZON:
        raise StreamingMonitorError(
            f"at least {MINIMUM_CERTIFICATE_HORIZON} observations are required"
        )
    final = monitor.snapshot()
    if not points or points[-1]["observations"] != monitor.observations:
        points.append(monitor.snapshot(include_models=False))
    return {
        "artifact_status": STATUS,
        "data": {
            "input_sha256": tabular.sha256_file(data_path),
            "observations": monitor.observations,
        },
        "final": final,
        "nonclaims": NONCLAIMS,
        "points": points,
        "protocol_sha256": monitor.protocol_sha256,
        "schema_version": TRACE_SCHEMA,
        "snapshot_interval": every,
    }
