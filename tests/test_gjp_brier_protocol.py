from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import urllib.request

import pytest

from scripts import check_gjp_brier_protocol as checker
from scripts import fetch_gjp_brier_inputs as fetcher


def _mutated(tmp_path: Path, mutate) -> Path:
    protocol = json.loads(checker.DEFAULT_PROTOCOL.read_bytes())
    mutate(protocol)
    target = tmp_path / "protocol.json"
    target.write_bytes(checker.canonical_json_bytes(protocol))
    return target


def test_tracked_protocol_validates() -> None:
    assert checker.main([]) == 0


def test_protocol_declares_no_result_and_no_certification() -> None:
    protocol = json.loads(checker.DEFAULT_PROTOCOL.read_bytes())
    assert protocol["artifact_status"] == checker.ARTIFACT_STATUS
    assert protocol["lean_binding"]["certified"] is False
    for relative in protocol["fresh_output_paths"]:
        assert not (checker.ROOT / relative).exists()


def test_max_index_matches_the_lean_arithmetic() -> None:
    # (Nat.log 4 n).pred + 2 for the sample sizes the protocol admits.
    assert checker.max_geometric_atom(4) == 2
    assert checker.max_geometric_atom(15) == 2
    assert checker.max_geometric_atom(16) == 3
    assert checker.max_geometric_atom(177) == 4
    assert checker.max_geometric_atom(512) == 5


def test_split_counts_must_match_the_disclosed_question_count(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["chronological_split"]["monitor"]["expected_count"] = 176

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_overlapping_windows_are_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["chronological_split"]["calibration"]["date_closed_from"] = "2012-06-01"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_a_rounding_direction_that_loosens_the_bound_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["quantization"]["rounding_directions"]["psi"] = "down"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_unquantized_monitored_forecaster_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["quantization"]["monitored_forecaster_is_the_quantized_forecaster"] = False

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_a_wake_leaving_too_short_a_suffix_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["confidence_contract"]["wake_grid"] = [0, 8, 32, 175]

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_self_declared_certification_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["lean_binding"]["certified"] = True

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_an_existing_reserved_output_fails_the_gate(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["fresh_output_paths"] = ["README.md"]

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_a_dropped_leakage_test_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["leakage_tests"] = [
            test
            for test in protocol["leakage_tests"]
            if test["id"] != "deliberately_leaked_tripwire"
        ]

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_date_suspend_only_cutoff_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["prediction_before_outcome"]["effective_cutoff_formula"] = "date_suspend"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_pre_start_forecasts_cannot_be_admitted(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["prediction_before_outcome"]["rule"] = (
            "every consumed forecast timestamp is strictly less than effective_cutoff"
        )

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_receipt_must_expose_the_minimum_consumed_timestamp(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["prediction_before_outcome"][
            "receipt_records_per_observation_min_consumed_timestamp"
        ] = False

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_unknown_forecast_event_policy_is_pinned(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["prediction_before_outcome"]["survey_forecast_event_types"]["allowed"] = [0, 1]

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_missing_cutoff_amendment_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["protocol_amendments"] = []

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_amendment_must_precede_numerical_results(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["protocol_amendments"][0]["result_existed_before_amendment"] = True

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_rational_posterior_grid_is_pinned(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["posterior_rule"]["quantization_denominator"] = 10**12

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_null_replay_seed_is_pinned(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["baselines"]["null_generator"]["seed_u64_hex"] = "0x1"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_repeated_look_grid_is_pinned(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["baselines"]["B2_evaluation"] = "evaluate selected prefixes"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_null_win_thresholds_are_pinned(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["baselines"]["win_condition"] = "looks favorable"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_eligible_count_must_partition_candidates(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["eligibility_after_temporal_amendment"]["included_count"] = 382

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_a_non_original_access_route_is_refused(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["dataset"]["access_route"] = (
            "https://dataverse.harvard.edu/api/access/datafile/{id}"
        )

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_prior_must_be_a_full_support_pmf(tmp_path: Path) -> None:
    def mutate(protocol: dict) -> None:
        protocol["model_catalog"]["prior"] = ["1/2", "1/2", "0", "0"]

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1


def test_fetcher_refuses_an_output_directory_inside_the_repository(tmp_path: Path) -> None:
    assert fetcher.main(["--out", str(checker.ROOT / "applications"), "--verify-only"]) == 1


def test_fetcher_verify_only_reports_absent_inputs(tmp_path: Path) -> None:
    assert fetcher.main(["--out", str(tmp_path / "inputs"), "--verify-only"]) == 1


def test_fetcher_identifies_itself_for_dataverse_redirects(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    payload = b"pinned original bytes"
    captured: dict[str, object] = {}

    def fake_urlopen(request: urllib.request.Request, timeout: int) -> io.BytesIO:
        captured["request"] = request
        captured["timeout"] = timeout
        return io.BytesIO(payload)

    monkeypatch.setattr(fetcher.urllib.request, "urlopen", fake_urlopen)
    entry = {
        "dataverse_id": 7,
        "filename": "input.csv",
        "md5": hashlib.md5(payload).hexdigest(),
        "original_bytes_confirmed": len(payload),
    }
    target = fetcher.fetch_one(
        "https://example.test/api/access/datafile/{id}?format=original",
        entry,
        tmp_path,
        30,
    )

    request = captured["request"]
    assert isinstance(request, urllib.request.Request)
    assert request.get_header("User-agent") == fetcher.USER_AGENT
    assert request.get_header("Accept-encoding") == "identity"
    assert captured["timeout"] == 30
    assert target.read_bytes() == payload


@pytest.mark.parametrize(
    "field", ["artifact_status", "protocol_version", "schema_version"]
)
def test_identity_fields_are_pinned(tmp_path: Path, field: str) -> None:
    def mutate(protocol: dict) -> None:
        protocol[field] = "something-else"

    assert checker.main(["--protocol", str(_mutated(tmp_path, mutate))]) == 1
