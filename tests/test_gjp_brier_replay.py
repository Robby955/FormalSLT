from __future__ import annotations

import csv
import copy
import inspect
import json
from types import SimpleNamespace
from datetime import datetime
from fractions import Fraction
from pathlib import Path

import pytest

from scripts import build_gjp_brier_replay as builder


def _forecast_row(**changes: str) -> dict[str, str]:
    row = {field: "" for field in builder.FORECAST_FIELDS}
    row.update(
        {
            "ifp_id": "q1",
            "user_id": "u1",
            "forecast_id": "1",
            "fcast_type": "0",
            "answer_option": "a",
            "value": "0.2",
            "year": "1",
            "timestamp": "2020-01-02 12:00:00",
        }
    )
    row.update(changes)
    return row


def _write_forecasts(path: Path, rows: list[dict[str, str]]) -> None:
    with path.open("w", encoding="latin-1", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=builder.FORECAST_FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def _window() -> builder.QuestionWindow:
    return builder.QuestionWindow(
        ifp_id="q1",
        date_start=datetime(2020, 1, 2),
        date_suspend=datetime(2020, 1, 10, 18),
        date_closed=datetime(2020, 1, 8),
        effective_cutoff=datetime(2020, 1, 8),
        source_date_start="1/2/20",
        source_date_suspend="1/10/20 18:00",
        source_date_closed="1/8/20",
        split="monitor",
    )


def _long_window() -> builder.QuestionWindow:
    return builder.QuestionWindow(
        ifp_id="q1",
        date_start=datetime(2020, 1, 2),
        date_suspend=datetime(2020, 2, 10),
        date_closed=datetime(2020, 2, 1),
        effective_cutoff=datetime(2020, 2, 1),
        source_date_start="1/2/20",
        source_date_suspend="2/10/20",
        source_date_closed="2/1/20",
        split="monitor",
    )


def test_forecast_reducer_has_no_outcome_parameter() -> None:
    assert list(inspect.signature(builder.reduce_forecasts).parameters) == [
        "windows",
        "forecast_paths",
        "allowed_event_types",
    ]


def test_deliberately_leaked_tripwire_refuses_outcome_dependency() -> None:
    result = builder._deliberately_leaked_tripwire(
        [{"outcome": 0}, {"outcome": 1}, {"outcome": 1}]
    )
    assert result["status"] == "PASS"
    assert result["oracle_prediction_count"] == 3
    assert len(result["oracle_predictions_sha256"]) == 64
    assert result["scored"] is False


def test_deliberately_leaked_tripwire_fails_if_ingestor_accepts_oracle() -> None:
    def permissive_ingestor(
        _model_id: str, predictions: list[Fraction], _source: str
    ) -> list[Fraction]:
        return predictions

    with pytest.raises(builder.ReplayError, match="oracle model passed"):
        builder._deliberately_leaked_tripwire(
            [{"outcome": 0}, {"outcome": 1}], permissive_ingestor
        )


def test_brier_scorer_refuses_same_observation_outcome_source() -> None:
    with pytest.raises(builder.ReplayError, match="same observation outcome"):
        builder._score_brier_prediction(
            Fraction(1), Fraction(1), "same-observation outcome column (oracle-leak)"
        )


def test_temporal_reduction_and_last_event_tie_break_are_exact(tmp_path: Path) -> None:
    source = tmp_path / "survey_fcasts.yr1.tab"
    _write_forecasts(
        source,
        [
            _forecast_row(timestamp="2020-01-01 23:59:59", value="0.9"),
            _forecast_row(forecast_id="1", fcast_type="0", value="0.2"),
            _forecast_row(forecast_id="2", fcast_type="1", value="0.4"),
            _forecast_row(forecast_id="3", fcast_type="2", value="0.6"),
            _forecast_row(
                user_id="u2", forecast_id="4", fcast_type="4", value="0.8"
            ),
            _forecast_row(
                timestamp="2020-01-08 00:00:00", forecast_id="5", value="0.99"
            ),
        ],
    )
    accumulators, audit = builder.reduce_forecasts(
        {"q1": _window()}, [source], {0, 1, 2, 4}
    )
    accumulator = accumulators["q1"]
    assert audit["counts"]["excluded_before_date_start"] == 1
    assert audit["counts"]["excluded_at_or_after_effective_cutoff"] == 1
    assert accumulator.first_week_count == 4
    assert accumulator.first_week_sum == 2
    assert accumulator.latest_by_user["u1"].value == Fraction(3, 5)
    assert accumulator.max_timestamp_ties == 2
    assert accumulator.differing_value_ties == 1
    assert [
        accumulator.window_accumulators[days].count
        for days in builder.ABLATION_DAYS
    ] == [4, 4, 4, 4]

    predictions, missing = builder.crowd_predictions(
        {"q1": _window()}, accumulators, 10**6
    )
    assert missing["missing_count_by_model"] == {
        "extremized-final-consensus": 0,
        "final-consensus-median": 0,
        "first-week-mean": 0,
    }
    assert predictions["q1"]["first-week-mean"] == Fraction(1, 2)
    assert predictions["q1"]["final-consensus-median"] == Fraction(7, 10)
    assert (
        predictions["q1"]["provenance"]["first_week"]["min_consumed_timestamp"]
        >= "2020-01-02T00:00:00"
    )
    assert (
        predictions["q1"]["provenance"]["final_consensus"]["max_consumed_timestamp"]
        < "2020-01-08T00:00:00"
    )

    protocol = json.loads(builder.DEFAULT_PROTOCOL.read_bytes())
    ablation = builder._future_feature_ablation(
        protocol, {"q1": _window()}, accumulators, predictions
    )
    assert ablation["status"] == "PASS"
    assert ablation["windows_days"] == [1, 3, 7, 14]
    assert ablation["primary_7_day_predictions_match"] is True
    assert all(row["observations"] for row in ablation["windows"])


def test_unknown_forecast_event_type_fails_closed(tmp_path: Path) -> None:
    source = tmp_path / "survey_fcasts.yr1.tab"
    _write_forecasts(source, [_forecast_row(fcast_type="9")])
    with pytest.raises(builder.ReplayError, match="unrecognized fcast_type"):
        builder.reduce_forecasts({"q1": _window()}, [source], {0, 1, 2, 4})


def test_ablation_windows_exercise_exact_day_boundaries(tmp_path: Path) -> None:
    source = tmp_path / "survey_fcasts.yr1.tab"
    _write_forecasts(
        source,
        [
            _forecast_row(timestamp="2020-01-02 12:00:00", forecast_id="1"),
            _forecast_row(timestamp="2020-01-03 00:00:00", forecast_id="2"),
            _forecast_row(timestamp="2020-01-05 00:00:00", forecast_id="3"),
            _forecast_row(timestamp="2020-01-09 00:00:00", forecast_id="4"),
            _forecast_row(timestamp="2020-01-16 00:00:00", forecast_id="5"),
        ],
    )
    accumulators, _audit = builder.reduce_forecasts(
        {"q1": _long_window()}, [source], {0, 1, 2, 4}
    )
    assert [
        accumulators["q1"].window_accumulators[days].count
        for days in builder.ABLATION_DAYS
    ] == [1, 2, 3, 4]


@pytest.mark.parametrize(
    ("value", "denominator", "expected"),
    [
        (Fraction(1, 4), 2, Fraction(0)),
        (Fraction(3, 4), 2, Fraction(1)),
        (Fraction(5, 4), 2, Fraction(1)),
        (Fraction(7, 4), 2, Fraction(2)),
    ],
)
def test_forecast_quantization_uses_ties_to_even(
    value: Fraction, denominator: int, expected: Fraction
) -> None:
    assert builder.round_fraction_ties_even(value, denominator) == expected


def test_posterior_largest_remainder_uses_model_id_ties() -> None:
    posterior, audit = builder.rationalized_posterior(
        ["z-model", "a-model"],
        [Fraction(1, 2), Fraction(1, 2)],
        [Fraction(0), Fraction(0)],
        3,
    )
    assert posterior == [Fraction(1, 3), Fraction(2, 3)]
    assert audit["simplex_units"] == [1, 2]
    assert audit["decimal_precision"] == 80


def test_splitmix64_matches_the_pinned_unsigned_stream() -> None:
    generator = builder.SplitMix64(0)
    assert generator.next_u64() == 0xE220A8397B1DCDAF
    assert generator.next_u64() == 0x6E789E6AA1B965F4
    assert generator.words == 2


def test_exact_bernoulli_handles_endpoints_without_floats() -> None:
    zero_generator = builder.SplitMix64(7)
    one_generator = builder.SplitMix64(7)
    assert builder._bernoulli_exact(zero_generator, Fraction(0)) == (0, 0)
    assert builder._bernoulli_exact(one_generator, Fraction(1)) == (1, 0)


def test_small_null_replay_is_byte_deterministic() -> None:
    protocol = json.loads(builder.DEFAULT_PROTOCOL.read_bytes())
    protocol = copy.deepcopy(protocol)
    protocol["baselines"]["null_replicates"] = 2
    protocol["confidence_contract"]["wake_grid"] = [0]
    predictions = [[Fraction(1, 2)] * 4 for _ in range(4)]
    first = builder._null_replay(
        protocol,
        predictions,
        [Fraction(1, 4)] * 4,
        [Fraction(1, 4)] * 4,
        Fraction(1, 2),
        Fraction(1, 4),
        Fraction(1),
    )
    second = builder._null_replay(
        protocol,
        predictions,
        [Fraction(1, 4)] * 4,
        [Fraction(1, 4)] * 4,
        Fraction(1, 2),
        Fraction(1, 4),
        Fraction(1),
    )
    assert builder.canonical_json_bytes(first) == builder.canonical_json_bytes(second)
    assert first["generator"]["words_consumed"] == 8
    assert first["replicates"] == 2


def test_posthoc_shuffle_sensitivity_is_exact_and_deterministic() -> None:
    identifiers = [f"q{index}" for index in range(8)]
    losses = [
        [Fraction(index, 9) for index in range(8)],
        [Fraction(8 - index, 9) for index in range(8)],
    ]
    posterior = [Fraction(1, 3), Fraction(2, 3)]
    first = builder._posthoc_shuffled_time_sensitivity(
        identifiers, losses, posterior
    )
    second = builder._posthoc_shuffled_time_sensitivity(
        identifiers, losses, posterior
    )
    assert builder.canonical_json_bytes(first) == builder.canonical_json_bytes(second)
    assert first["status"] == "PASS"
    assert first["permutations"] == 200
    assert first["distinct_permutations"] == 200
    assert first["all_exact_empirical_risks_equal"] is True
    assert first["every_order_is_bijection"] is True
    assert first["quadratic_variation_changed_in_observed_sample"] is True
    assert len(first["quadratic_variation_distribution"]["sorted_exact_values"]) == 200
    assert first["statistical_status"].startswith("POSTHOC")


def test_failed_b2_win_condition_forces_overall_fail_and_incomplete() -> None:
    null_replay = {
        "win_condition_checks": {
            "B1_count_at_most_nominal_ceiling": True,
            "B2_count_at_least_25": False,
            "B3_count_at_most_nominal_ceiling": True,
            "B3_final_width_at_most_twice_B1": True,
        },
        "win_condition_passed": False,
    }
    leakage_tests = {
        "shuffled_time_control": {
            "status": "UNDERSPECIFIED_NOT_UNIQUELY_REPLAYABLE"
        }
    }
    verdict = builder._overall_preregistered_verdict(null_replay, leakage_tests)
    assert verdict == {
        "control_completion": "INCOMPLETE",
        "failed_win_condition_checks": ["B2_count_at_least_25"],
        "incomplete_controls": ["shuffled_time_control"],
        "status": "FAIL",
        "win_condition_passed": False,
    }


def test_implementation_pin_refuses_dirty_checkout(monkeypatch: pytest.MonkeyPatch) -> None:
    def fake_run(args: list[str], **_kwargs: object) -> SimpleNamespace:
        if args[1] == "rev-parse":
            return SimpleNamespace(stdout="a" * 40 + "\n")
        if args[1] == "status":
            return SimpleNamespace(stdout="?? stray-file\n")
        raise AssertionError(args)

    monkeypatch.setattr(builder.subprocess, "run", fake_run)
    with pytest.raises(builder.ReplayError, match="clean"):
        builder._implementation_commit([builder.DEFAULT_PROTOCOL], "b" * 40)


def test_implementation_pin_refuses_modified_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_run(args: list[str], **_kwargs: object) -> SimpleNamespace:
        if args[1] == "rev-parse":
            return SimpleNamespace(stdout="a" * 40 + "\n")
        if args[1] == "status":
            return SimpleNamespace(stdout="")
        if args[1] == "merge-base":
            return SimpleNamespace(stdout=b"")
        if args[1] == "show":
            return SimpleNamespace(stdout=b"different committed bytes")
        raise AssertionError(args)

    monkeypatch.setattr(builder.subprocess, "run", fake_run)
    with pytest.raises(builder.ReplayError, match="working implementation bytes differ"):
        builder._implementation_commit([builder.DEFAULT_PROTOCOL], "b" * 40)


def test_output_directory_inside_repository_is_refused() -> None:
    with pytest.raises(builder.ReplayError, match="outside the repository"):
        builder._external_output_dir(builder.ROOT / "applications")


def test_reserved_result_paths_remain_absent() -> None:
    protocol, _raw = builder.load_protocol(builder.DEFAULT_PROTOCOL)
    for relative in protocol["fresh_output_paths"]:
        assert not (builder.ROOT / relative).exists()


def test_independent_verifier_does_not_import_builder() -> None:
    if not builder.DEFAULT_VERIFIER.exists():
        pytest.skip("independent verifier is being implemented")
    source = builder.DEFAULT_VERIFIER.read_text(encoding="utf-8")
    assert "import build_gjp_brier_replay" not in source
    assert "from scripts import build_gjp_brier_replay" not in source
