#!/usr/bin/env python3
"""Thin local FastAPI surface for the exact Brier monitor and certifier.

The service keeps live monitor state and source rows in memory.  Certification
freezes the current point-posterior selection, writes a canonical CSV replay,
and calls the same independent replay plus Lean checker used by the CLI.  It is
an unauthenticated local research service, not an Internet-facing deployment.
"""

from __future__ import annotations

import asyncio
import csv
import hashlib
import json
import os
import tempfile
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from threading import RLock

from fastapi import FastAPI, HTTPException, Query, Request
from fastapi.responses import StreamingResponse
from pydantic import BaseModel, ConfigDict, JsonValue, StrictInt

import formalslt_brier_certificate as certificate_engine
import formalslt_brier_summary as summary_engine
import formalslt_brier_streaming as streaming
import formalslt_brier_tabular as tabular


MAX_MODELS = 1_000
MAX_OBSERVATIONS = 1_000_000
SERVICE_STATUS = "LIVE_NOT_CERTIFIED"
PREFIX_CHAIN_SCHEMA = "formalslt.monitor-prefix-chain.v1"
PREFIX_CHAIN_STATUS = "COMMITTED_PREFIX_UNSIGNED"
EVENT_POLL_SECONDS = 0.25
EVENT_KEEPALIVE_SECONDS = 15.0


class StrictModel(BaseModel):
    model_config = ConfigDict(extra="forbid")


class CreateMonitorRequest(StrictModel):
    protocol: dict[str, JsonValue]


class ObservationRequest(StrictModel):
    time: StrictInt
    outcome: StrictInt
    predictions: dict[str, StrictInt]


class MonitorResponse(StrictModel):
    commitment: dict[str, JsonValue]
    monitor_id: str
    model_count: int
    observations: int
    protocol_sha256: str
    snapshot: dict[str, JsonValue] | None
    status: str
    summary: dict[str, JsonValue] | None


class FreezeResponse(StrictModel):
    frozen_protocol: dict[str, JsonValue]
    monitor_id: str
    selection: dict[str, JsonValue]


class CertificateResponse(StrictModel):
    certificate: dict[str, JsonValue]
    certificate_id: str
    monitor_id: str
    selection: dict[str, JsonValue]
    summary: dict[str, JsonValue]


@dataclass
class MonitorSession:
    monitor: streaming.StreamingBrierMonitor
    chain_genesis: str
    chain_head: str
    rows: list[dict[str, int | dict[str, int]]] = field(default_factory=list)
    certificates: dict[
        int,
        tuple[Path, dict[str, JsonValue], dict[str, JsonValue]],
    ] = field(default_factory=dict)
    lock: RLock = field(default_factory=RLock, repr=False)


class ServiceState:
    """In-memory session registry with a local certificate artifact root."""

    def __init__(self, output_root: Path) -> None:
        self.output_root = output_root.resolve()
        self.output_root.mkdir(parents=True, exist_ok=True)
        self._sessions: dict[str, MonitorSession] = {}
        self._lock = RLock()

    def create(self, protocol: dict[str, JsonValue]) -> tuple[str, MonitorSession]:
        monitor = _validated_monitor(protocol)
        if len(monitor.model_ids) > MAX_MODELS:
            raise streaming.StreamingMonitorError(
                f"at most {MAX_MODELS} models are supported by this service"
            )
        data = monitor.protocol["data"]
        columns = [
            data["time_column"],
            data["outcome_column"],
            *monitor.columns.values(),
        ]
        if len(set(columns)) != len(columns):
            raise streaming.StreamingMonitorError(
                "time, outcome, and prediction columns must be distinct"
            )
        monitor_id = uuid.uuid4().hex
        chain_genesis = _prefix_chain_genesis(monitor)
        session = MonitorSession(
            monitor=monitor,
            chain_genesis=chain_genesis,
            chain_head=chain_genesis,
        )
        with self._lock:
            self._sessions[monitor_id] = session
        return monitor_id, session

    def get(self, monitor_id: str) -> MonitorSession:
        with self._lock:
            session = self._sessions.get(monitor_id)
        if session is None:
            raise KeyError(monitor_id)
        return session


def _validated_monitor(
    protocol: dict[str, JsonValue],
) -> streaming.StreamingBrierMonitor:
    """Validate an uploaded JSON value through the canonical protocol loader."""

    raw = tabular.canonical_json_bytes(protocol)
    with tempfile.TemporaryDirectory(prefix="formalslt-monitor-protocol-") as temporary:
        path = Path(temporary) / "protocol.json"
        tabular.atomic_write(path, raw)
        return streaming.StreamingBrierMonitor.from_protocol_path(path)


def _prefix_chain_genesis(monitor: streaming.StreamingBrierMonitor) -> str:
    identity = {
        "model_ids": list(monitor.model_ids),
        "protocol_sha256": monitor.protocol_sha256,
        "schema_version": PREFIX_CHAIN_SCHEMA,
    }
    return hashlib.sha256(tabular.canonical_json_bytes(identity)).hexdigest()


def _prefix_chain_step(
    session: MonitorSession,
    row: dict[str, int | dict[str, int]],
) -> str:
    predictions = row["predictions"]
    if not isinstance(predictions, dict):
        raise RuntimeError("stored prediction row is malformed")
    entry = {
        "outcome": row["outcome"],
        "predictions": [
            predictions[model_id] for model_id in session.monitor.model_ids
        ],
        "previous_sha256": session.chain_head,
        "sequence": session.monitor.observations,
        "time": row["time"],
    }
    return hashlib.sha256(tabular.canonical_json_bytes(entry)).hexdigest()


def _commitment(session: MonitorSession) -> dict[str, JsonValue]:
    return {
        "algorithm": "SHA-256",
        "artifact_status": PREFIX_CHAIN_STATUS,
        "genesis_sha256": session.chain_genesis,
        "head_sha256": session.chain_head,
        "observations": session.monitor.observations,
        "protocol_sha256": session.monitor.protocol_sha256,
        "schema_version": PREFIX_CHAIN_SCHEMA,
        "signed": False,
    }


def _monitor_response(
    monitor_id: str,
    session: MonitorSession,
    *,
    include_models: bool,
) -> MonitorResponse:
    monitor = session.monitor
    snapshot = (
        monitor.snapshot(include_models=include_models)
        if monitor.observations > 0
        else None
    )
    summary = (
        summary_engine.preview_summary(
            snapshot,
            confidence=1 - monitor.delta,
            tilt=monitor.tilt,
            provenance=monitor.protocol["provenance"],
        )
        if snapshot is not None
        else None
    )
    return MonitorResponse(
        commitment=_commitment(session),
        monitor_id=monitor_id,
        model_count=len(monitor.model_ids),
        observations=monitor.observations,
        protocol_sha256=monitor.protocol_sha256,
        snapshot=snapshot,
        status=SERVICE_STATUS,
        summary=summary,
    )


def _write_rows(path: Path, session: MonitorSession) -> None:
    monitor = session.monitor
    data = monitor.protocol["data"]
    fieldnames = [
        data["time_column"],
        data["outcome_column"],
        *(monitor.columns[model_id] for model_id in monitor.model_ids),
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
            writer.writeheader()
            for row in session.rows:
                predictions = row["predictions"]
                if not isinstance(predictions, dict):
                    raise RuntimeError("stored prediction row is malformed")
                writer.writerow(
                    {
                        data["time_column"]: row["time"],
                        data["outcome_column"]: row["outcome"],
                        **{
                            monitor.columns[model_id]: predictions[model_id]
                            for model_id in monitor.model_ids
                        },
                    }
                )
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _issue_session_certificate(
    state: ServiceState,
    monitor_id: str,
    session: MonitorSession,
) -> tuple[
    str,
    dict[str, JsonValue],
    dict[str, JsonValue],
    dict[str, JsonValue],
]:
    monitor = session.monitor
    observations = monitor.observations
    cached = session.certificates.get(observations)
    if cached is not None:
        path, certificate, selection = cached
        summary = summary_engine.certificate_summary(
            certificate,
            certificate_sha256=certificate_engine.sha256_file(path),
            selected_model=str(selection["selected_model"]),
        )
        return f"{monitor_id}:{observations}", certificate, selection, summary

    frozen = monitor.freeze_selected_protocol(input_format="csv")
    prefix_root = state.output_root / monitor_id / f"prefix-{observations}"
    protocol_path = prefix_root / "selected-protocol.json"
    data_path = prefix_root / "predictions.csv"
    certificate_root = prefix_root / "certificate"
    certificate_path = certificate_root / certificate_engine.CERTIFICATE_NAME

    if certificate_path.exists():
        certificate = certificate_engine.verify(
            certificate_path,
            protocol_path,
            data_path,
        )
    else:
        prefix_root.mkdir(parents=True, exist_ok=True)
        tabular.atomic_write(protocol_path, frozen.raw)
        _write_rows(data_path, session)
        certificate_path = certificate_engine.issue(
            protocol_path,
            data_path,
            certificate_root,
        )
        certificate = certificate_engine.verify(
            certificate_path,
            protocol_path,
            data_path,
        )

    if certificate["protocol"]["sha256"] != frozen.record["selected_protocol_sha256"]:
        raise certificate_engine.CertificateError(
            "certificate does not bind the frozen selected protocol"
        )
    if (
        certificate["data"]["normalized_stream_sha256"]
        != frozen.record["normalized_stream_sha256"]
    ):
        raise certificate_engine.CertificateError(
            "certificate does not bind the live normalized stream"
        )
    session.certificates[observations] = (
        certificate_path,
        certificate,
        frozen.record,
    )
    certificate_id = f"{monitor_id}:{observations}"
    summary = summary_engine.certificate_summary(
        certificate,
        certificate_sha256=certificate_engine.sha256_file(certificate_path),
        selected_model=str(frozen.record["selected_model"]),
    )
    return certificate_id, certificate, frozen.record, summary


def create_app(output_root: Path | None = None) -> FastAPI:
    root = output_root or Path(tempfile.mkdtemp(prefix="formalslt-monitor-service-"))
    state = ServiceState(root)
    app = FastAPI(
        title="FormalSLT Brier Monitor",
        version="1.0.0",
        description=(
            "Local exact streaming monitor with independently replayed Lean "
            "certificate issuance."
        ),
    )
    app.state.formalslt = state

    @app.get("/healthz")
    def health() -> dict[str, str]:
        return {"status": "ok"}

    @app.post("/v1/monitors", response_model=MonitorResponse, status_code=201)
    def create_monitor(request: CreateMonitorRequest) -> MonitorResponse:
        try:
            monitor_id, session = state.create(request.protocol)
        except (streaming.StreamingMonitorError, tabular.PreparationError) as error:
            raise HTTPException(status_code=422, detail=str(error)) from error
        return _monitor_response(monitor_id, session, include_models=False)

    @app.get("/v1/monitors/{monitor_id}", response_model=MonitorResponse)
    def get_monitor(
        monitor_id: str,
        include_models: bool = Query(default=False),
    ) -> MonitorResponse:
        try:
            session = state.get(monitor_id)
        except KeyError as error:
            raise HTTPException(status_code=404, detail="monitor not found") from error
        with session.lock:
            return _monitor_response(
                monitor_id,
                session,
                include_models=include_models,
            )

    @app.get("/v1/monitors/{monitor_id}/events")
    async def monitor_events(
        monitor_id: str,
        request: Request,
        include_models: bool = Query(default=False),
        once: bool = Query(default=False),
    ) -> StreamingResponse:
        try:
            session = state.get(monitor_id)
        except KeyError as error:
            raise HTTPException(status_code=404, detail="monitor not found") from error

        async def event_stream():
            previous_head: str | None = None
            last_emit = time.monotonic()
            while not await request.is_disconnected():
                with session.lock:
                    response = _monitor_response(
                        monitor_id,
                        session,
                        include_models=include_models,
                    )
                    payload = response.model_dump(mode="json")
                head = str(payload["commitment"]["head_sha256"])
                now = time.monotonic()
                if head != previous_head:
                    encoded = json.dumps(
                        payload,
                        separators=(",", ":"),
                        sort_keys=True,
                    )
                    yield f"event: snapshot\ndata: {encoded}\n\n"
                    previous_head = head
                    last_emit = now
                    if once:
                        return
                elif now - last_emit >= EVENT_KEEPALIVE_SECONDS:
                    yield ": keepalive\n\n"
                    last_emit = now
                await asyncio.sleep(EVENT_POLL_SECONDS)

        return StreamingResponse(
            event_stream(),
            media_type="text/event-stream",
            headers={
                "Cache-Control": "no-cache",
                "X-Accel-Buffering": "no",
            },
        )

    @app.post(
        "/v1/monitors/{monitor_id}/observations",
        response_model=MonitorResponse,
    )
    def append_observation(
        monitor_id: str,
        request: ObservationRequest,
    ) -> MonitorResponse:
        try:
            session = state.get(monitor_id)
        except KeyError as error:
            raise HTTPException(status_code=404, detail="monitor not found") from error
        with session.lock:
            if session.monitor.observations >= MAX_OBSERVATIONS:
                raise HTTPException(
                    status_code=409,
                    detail=f"monitor reached the {MAX_OBSERVATIONS} observation limit",
                )
            try:
                session.monitor.update(
                    time=request.time,
                    outcome=request.outcome,
                    predictions=request.predictions,
                )
            except streaming.StreamingMonitorError as error:
                raise HTTPException(status_code=422, detail=str(error)) from error
            row: dict[str, int | dict[str, int]] = {
                "time": int(request.time),
                "outcome": int(request.outcome),
                "predictions": {
                    model_id: int(request.predictions[model_id])
                    for model_id in session.monitor.model_ids
                },
            }
            session.rows.append(row)
            session.chain_head = _prefix_chain_step(session, row)
            return _monitor_response(monitor_id, session, include_models=False)

    @app.post(
        "/v1/monitors/{monitor_id}/freeze",
        response_model=FreezeResponse,
    )
    def freeze_monitor(monitor_id: str) -> FreezeResponse:
        try:
            session = state.get(monitor_id)
        except KeyError as error:
            raise HTTPException(status_code=404, detail="monitor not found") from error
        with session.lock:
            try:
                frozen = session.monitor.freeze_selected_protocol(input_format="csv")
            except streaming.StreamingMonitorError as error:
                raise HTTPException(status_code=409, detail=str(error)) from error
            return FreezeResponse(
                frozen_protocol=frozen.protocol,
                monitor_id=monitor_id,
                selection=frozen.record,
            )

    @app.post(
        "/v1/monitors/{monitor_id}/certify",
        response_model=CertificateResponse,
    )
    def certify_monitor(monitor_id: str) -> CertificateResponse:
        try:
            session = state.get(monitor_id)
        except KeyError as error:
            raise HTTPException(status_code=404, detail="monitor not found") from error
        with session.lock:
            try:
                (
                    certificate_id,
                    certificate,
                    selection,
                    summary,
                ) = _issue_session_certificate(state, monitor_id, session)
            except (
                certificate_engine.CertificateError,
                summary_engine.SummaryError,
                streaming.StreamingMonitorError,
                tabular.PreparationError,
            ) as error:
                raise HTTPException(status_code=409, detail=str(error)) from error
            return CertificateResponse(
                certificate=certificate,
                certificate_id=certificate_id,
                monitor_id=monitor_id,
                selection=selection,
                summary=summary,
            )

    @app.get(
        "/v1/monitors/{monitor_id}/certificates/{observations}",
        response_model=CertificateResponse,
    )
    def get_certificate(monitor_id: str, observations: int) -> CertificateResponse:
        try:
            session = state.get(monitor_id)
        except KeyError as error:
            raise HTTPException(status_code=404, detail="monitor not found") from error
        with session.lock:
            stored = session.certificates.get(observations)
            if stored is None:
                raise HTTPException(status_code=404, detail="certificate not found")
            certificate_path, certificate, selection = stored
            try:
                summary = summary_engine.certificate_summary(
                    certificate,
                    certificate_sha256=certificate_engine.sha256_file(
                        certificate_path
                    ),
                    selected_model=str(selection["selected_model"]),
                )
            except summary_engine.SummaryError as error:
                raise HTTPException(status_code=409, detail=str(error)) from error
            return CertificateResponse(
                certificate=certificate,
                certificate_id=f"{monitor_id}:{observations}",
                monitor_id=monitor_id,
                selection=selection,
                summary=summary,
            )

    return app


_configured_output_root = os.environ.get("FORMALSLT_CERTIFICATE_ROOT")
app = create_app(Path(_configured_output_root) if _configured_output_root else None)
