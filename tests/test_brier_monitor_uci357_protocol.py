from __future__ import annotations

import io
import json
import math
import warnings
import zipfile
from datetime import datetime
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

import pytest

from scripts import prepare_brier_monitor_uci357 as protocol_tool


def _source_bytes(rows: list[tuple[int, str, str]]) -> bytes:
    header = '"date","Temperature","Humidity","Light","CO2","HumidityRatio","Occupancy"\n'
    body = "".join(
        f'"{record_id}","{timestamp}",20.5,30.25,100,600,0.004,{label}\n'
        for record_id, timestamp, label in rows
    )
    return (header + body).encode("utf-8")


def _fixture_protocol_and_archive(
    *,
    duplicate_timestamp: bool = False,
    missing_value: bool = False,
    invalid_label: bool = False,
    extra_member: bool = False,
) -> tuple[dict[str, object], bytes]:
    protocol = json.loads(protocol_tool.DEFAULT_PROTOCOL.read_bytes())
    second_test2_timestamp = (
        "2020-01-01 00:04:00" if duplicate_timestamp else "2020-01-01 00:03:00"
    )
    label = "2" if invalid_label else "0"
    members = {
        "datatest.txt": _source_bytes(
            [(1, "2020-01-01 00:00:00", "0"), (2, "2020-01-01 00:01:00", "1")]
        ),
        "datatraining.txt": _source_bytes(
            [(1, "2020-01-01 00:04:00", "0"), (2, "2020-01-01 00:05:00", "1")]
        ),
        "datatest2.txt": _source_bytes(
            [(1, "2020-01-01 00:02:00", "1"), (2, second_test2_timestamp, label)]
        ),
    }
    if missing_value:
        members["datatraining.txt"] = members["datatraining.txt"].replace(
            b",30.25,100,", b",,100,", 1
        )
    archive_buffer = io.BytesIO()
    with zipfile.ZipFile(archive_buffer, mode="w", compression=zipfile.ZIP_STORED) as archive:
        for name in ("datatest.txt", "datatest2.txt", "datatraining.txt"):
            archive.writestr(name, members[name])
        if extra_member:
            archive.writestr("unexpected.txt", b"not allowed")
    archive_raw = archive_buffer.getvalue()

    dataset = protocol["dataset"]
    assert isinstance(dataset, dict)
    archive_spec = dataset["archive"]
    assert isinstance(archive_spec, dict)
    archive_spec["bytes"] = len(archive_raw)
    archive_spec["sha256"] = protocol_tool.sha256_bytes(archive_raw)
    member_specs = dataset["members"]
    assert isinstance(member_specs, list)
    for member_spec in member_specs:
        assert isinstance(member_spec, dict)
        raw = members[str(member_spec["name"])]
        member_spec["bytes"] = len(raw)
        member_spec["rows"] = 2
        member_spec["sha256"] = protocol_tool.sha256_bytes(raw)
    preprocessing = protocol["preprocessing"]
    assert isinstance(preprocessing, dict)
    preprocessing["expected_rows"] = 6
    protocol["splits"] = [
        {"count": 2, "name": "train", "start": 0, "stop": 2},
        {"count": 2, "name": "validation", "start": 2, "stop": 4},
        {"count": 2, "name": "monitor", "start": 4, "stop": 6},
    ]
    return protocol, archive_raw


def test_fixture_is_merged_and_sorted_chronologically() -> None:
    protocol, archive_raw = _fixture_protocol_and_archive()
    protocol_tool.validate_protocol(protocol, enforce_frozen_identity=False)
    prepared = protocol_tool.prepare_archive(archive_raw, protocol)
    assert [row.timestamp for row in prepared.observations] == [
        datetime(2020, 1, 1, 0, minute) for minute in range(6)
    ]
    assert [row.source_member for row in prepared.observations] == [
        "datatest.txt",
        "datatest.txt",
        "datatest2.txt",
        "datatest2.txt",
        "datatraining.txt",
        "datatraining.txt",
    ]
    first = protocol_tool.canonical_stream_bytes(prepared.observations)
    second = protocol_tool.canonical_stream_bytes(prepared.observations)
    assert first == second
    assert b"HumidityRatio,Occupancy\n" in first


@pytest.mark.parametrize(
    "mutation, message",
    [
        ({"duplicate_timestamp": True}, "duplicate timestamps"),
        ({"missing_value": True}, "missing or padded field"),
        ({"invalid_label": True}, "invalid Occupancy label"),
        ({"extra_member": True}, "ZIP member set mismatch"),
    ],
)
def test_source_mutations_fail_closed(mutation: dict[str, bool], message: str) -> None:
    protocol, archive_raw = _fixture_protocol_and_archive(**mutation)
    with pytest.raises(protocol_tool.ProtocolError, match=message):
        protocol_tool.prepare_archive(archive_raw, protocol)


def test_stale_archive_hash_fails_before_parsing() -> None:
    protocol, archive_raw = _fixture_protocol_and_archive()
    dataset = protocol["dataset"]
    assert isinstance(dataset, dict)
    archive = dataset["archive"]
    assert isinstance(archive, dict)
    archive["sha256"] = "0" * 64
    with pytest.raises(protocol_tool.ProtocolError, match="archive SHA-256"):
        protocol_tool.prepare_archive(archive_raw, protocol)


@pytest.mark.parametrize("leaked", ["Occupancy", "HumidityRatio", "record_id", "timestamp"])
def test_feature_allowlist_rejects_leakage(leaked: str) -> None:
    protocol = json.loads(protocol_tool.DEFAULT_PROTOCOL.read_bytes())
    feature_contract = protocol["feature_contract"]
    assert isinstance(feature_contract, dict)
    allowlists = feature_contract["allowlists"]
    assert isinstance(allowlists, dict)
    all_sensor = allowlists["all_sensor"]
    assert isinstance(all_sensor, list)
    all_sensor.append(leaked)
    with pytest.raises(protocol_tool.ProtocolError, match="feature allowlists"):
        protocol_tool.validate_protocol(protocol)


def test_fixed_splits_must_be_contiguous_and_exact() -> None:
    protocol = json.loads(protocol_tool.DEFAULT_PROTOCOL.read_bytes())
    splits = protocol["splits"]
    assert isinstance(splits, list)
    monitor = splits[2]
    assert isinstance(monitor, dict)
    monitor["start"] = 12_337
    with pytest.raises(protocol_tool.ProtocolError, match="not a contiguous exact slice"):
        protocol_tool.validate_protocol(protocol)


def test_quantization_and_exact_brier_helpers() -> None:
    assert protocol_tool.quantize_probability(Decimal("0")) == 0
    assert protocol_tool.quantize_probability(Decimal("1")) == 65_535
    assert protocol_tool.quantize_probability(Fraction(1, 2)) == 32_768
    exact_half_step = Fraction(2 * 12_345 - 1, 2 * 65_535)
    assert protocol_tool.quantize_probability(exact_half_step) == 12_345
    assert protocol_tool.brier_loss(32_768, 1) == Fraction(32_767**2, 65_535**2)
    assert protocol_tool.brier_loss(32_768, 0) == Fraction(32_768**2, 65_535**2)
    with pytest.raises(protocol_tool.ProtocolError, match="outside"):
        protocol_tool.quantize_probability(Decimal("1.0001"))
    with pytest.raises(protocol_tool.ProtocolError, match="0 or 1"):
        protocol_tool.brier_loss_numerator(0, 2)


def test_quantization_is_exact_around_half_step_under_low_decimal_precision() -> None:
    boundary = Fraction(1, 10)
    tiny_fraction = Fraction(1, 10**80)
    below_text = "0.0" + "9" * 79
    above_text = "0.1" + "0" * 78 + "1"
    below_decimal = Decimal(below_text)
    at_decimal = Decimal("0.1")
    above_decimal = Decimal(above_text)
    assert Fraction(*below_decimal.as_integer_ratio()) == boundary - tiny_fraction
    assert Fraction(*above_decimal.as_integer_ratio()) == boundary + tiny_fraction

    with localcontext() as context:
        context.prec = 6
        assert protocol_tool.quantize_probability(boundary - tiny_fraction) == 6_553
        assert protocol_tool.quantize_probability(boundary) == 6_554
        assert protocol_tool.quantize_probability(boundary + tiny_fraction) == 6_554
        assert protocol_tool.quantize_probability(below_decimal) == 6_553
        assert protocol_tool.quantize_probability(at_decimal) == 6_554
        assert protocol_tool.quantize_probability(above_decimal) == 6_554
        assert protocol_tool.quantize_probability(below_text) == 6_553
        assert protocol_tool.quantize_probability("0.1") == 6_554
        assert protocol_tool.quantize_probability(above_text) == 6_554
        assert protocol_tool.quantize_probability(math.nextafter(0.1, 0.0)) == 6_553
        assert protocol_tool.quantize_probability(0.1) == 6_554
        assert protocol_tool.quantize_probability(math.nextafter(0.1, 1.0)) == 6_554


def test_fit_rejects_declared_convergence_warning() -> None:
    class WarningEstimator:
        def fit(self, _features: object, _outcomes: object) -> None:
            warnings.warn("did not converge", UserWarning, stacklevel=2)

    with pytest.raises(
        protocol_tool.ProtocolError,
        match="baseline model emitted a convergence warning",
    ) as raised:
        protocol_tool._fit_rejecting_warning(
            WarningEstimator(),
            object(),
            object(),
            UserWarning,
        )
    assert isinstance(raised.value.__cause__, UserWarning)


def test_deterministic_five_model_posterior_and_tie_break() -> None:
    model_order = ["m0", "m1", "m2", "m3", "m4"]
    posterior = protocol_tool.deterministic_soft_winner_posterior(
        model_order,
        {"m0": 10, "m1": 5, "m2": 5, "m3": 20, "m4": 30},
    )
    assert posterior == {
        "m0": Fraction(1, 10),
        "m1": Fraction(3, 5),
        "m2": Fraction(1, 10),
        "m3": Fraction(1, 10),
        "m4": Fraction(1, 10),
    }
    assert sum(posterior.values(), Fraction(0)) == 1


def test_manifest_is_canonical_and_deterministic_for_fixture() -> None:
    protocol, archive_raw = _fixture_protocol_and_archive()
    prepared = protocol_tool.prepare_archive(archive_raw, protocol)
    protocol_raw = protocol_tool.canonical_json_bytes(protocol)
    first = protocol_tool.build_manifest(prepared, protocol, protocol_raw, b"script")
    second = protocol_tool.build_manifest(prepared, protocol, protocol_raw, b"script")
    assert protocol_tool.canonical_json_bytes(first) == protocol_tool.canonical_json_bytes(second)
    assert first["canonical_stream"]["rows"] == 6
    assert [row["count"] for row in first["splits"]] == [2, 2, 2]


def test_tracked_manifest_self_binds_protocol_and_preparer_without_data() -> None:
    manifest_raw = protocol_tool.DEFAULT_MANIFEST.read_bytes()
    manifest = protocol_tool.parse_json_bytes(manifest_raw, "tracked manifest")
    assert manifest_raw == protocol_tool.canonical_json_bytes(manifest)
    assert isinstance(manifest, dict)
    bindings = manifest["files"]
    assert bindings == [
        {
            "path": "applications/brier_monitor/uci357-protocol-v1.json",
            "role": "protocol",
            "sha256": bindings[0]["sha256"],
        },
        {
            "path": "scripts/prepare_brier_monitor_uci357.py",
            "role": "preparer",
            "sha256": bindings[1]["sha256"],
        },
    ]
    for binding in bindings:
        path = protocol_tool.ROOT / binding["path"]
        assert path.is_file()
        assert protocol_tool.sha256_bytes(path.read_bytes()) == binding["sha256"]


def test_nonclaim_boundary_is_frozen_exactly() -> None:
    protocol = json.loads(protocol_tool.DEFAULT_PROTOCOL.read_bytes())
    protocol["nonclaims"][0] = "a weaker substitute"
    with pytest.raises(protocol_tool.ProtocolError, match="nonclaim boundary"):
        protocol_tool.validate_protocol(protocol)


def test_cli_rejects_alternate_protocol_path_before_archive_access(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    alternate_protocol = tmp_path / "protocol.json"
    alternate_protocol.write_bytes(protocol_tool.DEFAULT_PROTOCOL.read_bytes())
    result = protocol_tool.main(
        [
            "--protocol",
            str(alternate_protocol),
            "--archive",
            str(tmp_path / "absent.zip"),
        ]
    )
    assert result == 1
    assert "must resolve to the frozen tracked UCI-357 protocol" in capsys.readouterr().err


def test_tracked_manifest_binds_authoritative_source_and_fixed_splits() -> None:
    manifest = json.loads(protocol_tool.DEFAULT_MANIFEST.read_bytes())
    assert manifest["dataset"]["uci_dataset_id"] == 357
    assert manifest["dataset"]["doi"] == "10.24432/C5X01N"
    assert manifest["dataset"]["license"]["spdx"] == "CC-BY-4.0"
    assert manifest["dataset"]["archive"]["sha256"] == (
        "4ae3f46aa98eedff564a9f6924d1635173e2fd2c816004342a9be93076d3a81a"
    )
    assert manifest["canonical_stream"] == {
        "bytes": 1_843_339,
        "columns": [
            "source_member",
            "source_line",
            "record_id",
            "timestamp",
            "Temperature",
            "Humidity",
            "Light",
            "CO2",
            "HumidityRatio",
            "Occupancy",
        ],
        "first_timestamp": "2015-02-02T14:19:00",
        "last_timestamp": "2015-02-18T09:19:00",
        "rows": 20_560,
        "sha256": "c2db5942015195266becce67b2ee882596fd17541230f483fb08a10b52553bd0",
    }
    assert [(row["name"], row["count"]) for row in manifest["splits"]] == [
        ("train", 8_224),
        ("validation", 4_112),
        ("monitor", 8_224),
    ]


@pytest.mark.skipif(
    not protocol_tool.DEFAULT_ARCHIVE.exists(),
    reason="authoritative archive is intentionally untracked",
)
def test_local_authoritative_archive_replays_to_tracked_manifest() -> None:
    protocol, protocol_raw = protocol_tool._load_protocol(protocol_tool.DEFAULT_PROTOCOL)
    prepared = protocol_tool.prepare_archive(
        protocol_tool.DEFAULT_ARCHIVE.read_bytes(), protocol
    )
    manifest = protocol_tool.build_manifest(
        prepared,
        protocol,
        protocol_raw,
        Path(protocol_tool.__file__).read_bytes(),
    )
    assert protocol_tool.canonical_json_bytes(manifest) == protocol_tool.DEFAULT_MANIFEST.read_bytes()
    local_result = protocol_tool.build_local_baseline_result(
        prepared, protocol, protocol_raw, manifest
    )
    assert local_result["posterior_after_monitor"]["winner"] == "logistic_all_sensor"
    assert Fraction(
        local_result["splits"]["monitor"]["logistic_all_sensor"]["brier_rational"]
    ) < Fraction(1, 10)
