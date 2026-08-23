from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import pytest

from scripts import verify_empirical_bernstein_boundary_witnesses as mirror


F = Fraction


def write_fixture(tmp_path: Path, source: str) -> Path:
    path = tmp_path / "WitnessFixture.lean"
    path.write_text(source, encoding="utf-8")
    return path


def marked_equality(
    witness_id: str = "PM-01",
    marker_theorem: str = "fixture_eq",
    actual_theorem: str = "fixture_eq",
    marker_pin: str = "right:7/16",
    actual_rhs: str = "(7 : ℝ) / 16",
) -> str:
    return f"""
/--
BOUNDARY_WITNESS|id={witness_id}|theorem={marker_theorem}|relation=eq|pin={marker_pin}
-/
theorem {actual_theorem} :
    fixtureValue = {actual_rhs} := by
  sorry
"""


def test_structured_marker_is_bound_to_the_adjacent_theorem(tmp_path: Path) -> None:
    path = write_fixture(tmp_path, marked_equality())

    assert mirror.lean_witness_ids(path) == ("PM-01",)


def test_duplicate_structured_marker_is_rejected(tmp_path: Path) -> None:
    source = marked_equality().replace(
        "BOUNDARY_WITNESS|",
        "BOUNDARY_WITNESS|id=PM-01|theorem=fixture_eq|relation=eq|pin=right:7/16\n"
        "BOUNDARY_WITNESS|",
        1,
    )
    path = write_fixture(tmp_path, source)

    with pytest.raises(ValueError, match="exactly one structured marker"):
        mirror.lean_witness_ids(path)


def test_orphan_prose_marker_is_rejected(tmp_path: Path) -> None:
    source = """
/-!
This is module prose rather than a theorem receipt.
BOUNDARY_WITNESS|id=PM-01|theorem=fixture_eq|relation=eq|pin=right:7/16
-/

def unrelated : Nat := 0
"""
    path = write_fixture(tmp_path, source)

    with pytest.raises(ValueError, match="immediately precede a theorem"):
        mirror.lean_witness_ids(path)


def test_marker_bound_to_wrong_theorem_is_rejected(tmp_path: Path) -> None:
    path = write_fixture(
        tmp_path,
        marked_equality(marker_theorem="fixture_eq", actual_theorem="other_eq"),
    )

    with pytest.raises(ValueError, match="names theorem fixture_eq.*other_eq"):
        mirror.lean_witness_ids(path)


def test_marker_with_changed_rhs_is_rejected(tmp_path: Path) -> None:
    path = write_fixture(tmp_path, marked_equality(marker_pin="right:8/16"))

    with pytest.raises(ValueError, match="pins 1/2.*statement has 7/16"):
        mirror.lean_witness_ids(path)


def test_changed_lhs_fails_the_bound_proposition_manifest() -> None:
    source = mirror.LEAN_WITNESS_FILE.read_text(encoding="utf-8")
    old_lhs = "forwardPrefixMean skewFour 4 ="
    new_lhs = "forwardPrefixMean balancedFour 4 ="
    assert source.count(old_lhs) == 1

    changed_bindings = mirror.parse_lean_witnesses(
        source.replace(old_lhs, new_lhs, 1)
    )
    expected = mirror.EXPECTED_LEAN_BINDINGS[0]
    changed = changed_bindings[0]

    assert (
        changed.witness_id,
        changed.theorem,
        changed.relation,
        changed.pin_kind,
        changed.pin,
    ) == (
        expected.witness_id,
        expected.theorem,
        expected.relation,
        expected.pin_kind,
        expected.pin,
    )
    assert changed.proposition_sha256 != expected.proposition_sha256
    assert changed_bindings != mirror.EXPECTED_LEAN_BINDINGS


def test_duplicate_id_across_separate_theorems_is_rejected(tmp_path: Path) -> None:
    source = marked_equality() + marked_equality(
        marker_theorem="second_eq", actual_theorem="second_eq"
    )
    path = write_fixture(tmp_path, source)

    with pytest.raises(ValueError, match="duplicate witness id PM-01"):
        mirror.lean_witness_ids(path)


def test_right_factor_change_from_half_to_third_is_rejected(tmp_path: Path) -> None:
    source = """
/--
BOUNDARY_WITNESS|id=BND-SHAPE|theorem=shape_eq|relation=eq|pin=right_factor:1/2
-/
theorem shape_eq :
    catalogBoundary = endpoint (delta / 3) := by
  sorry
"""
    path = write_fixture(tmp_path, source)

    with pytest.raises(ValueError, match="pins 1/2.*statement has 1/3"):
        mirror.lean_witness_ids(path)


def test_every_lean_id_has_the_expected_exact_python_value() -> None:
    source = mirror.LEAN_WITNESS_FILE.read_text(encoding="utf-8")
    assert mirror.parse_lean_witnesses(source) == mirror.EXPECTED_LEAN_BINDINGS
    assert mirror.lean_witness_ids() == tuple(mirror.EXPECTED_WITNESS_VALUES)
    assert mirror.computed_witness_values() == mirror.EXPECTED_WITNESS_VALUES
    assert mirror.validate() == []


def test_prefix_formulas_ignore_out_of_prefix_sentinels() -> None:
    changed_sentinel = (*mirror.SKEW_FOUR[:4], F(-1000003, 17))

    assert mirror.prefix_mean(changed_sentinel, 4) == F(7, 16)
    assert mirror.bessel_q(changed_sentinel, 4) == F(35, 64)
    assert mirror.predictable_quadratic(changed_sentinel, 4) == F(65, 64)


def test_hybrid_battery_strictly_selects_both_branches() -> None:
    skew_affine, skew_harmonic = mirror.hybrid_components(mirror.SKEW_FOUR, 4)
    balanced_affine, balanced_harmonic = mirror.hybrid_components(
        mirror.BALANCED_FOUR, 4
    )
    split_affine, split_harmonic = mirror.hybrid_components(mirror.SPLIT_FIVE, 5)

    assert (skew_affine, skew_harmonic) == (F(169, 128), F(65, 48))
    assert skew_affine < skew_harmonic
    assert (balanced_affine, balanced_harmonic) == (F(2), F(47, 24))
    assert balanced_harmonic < balanced_affine
    assert (split_affine, split_harmonic) == (F(23, 10), F(53, 24))
    assert split_harmonic < split_affine


def test_three_term_atanh_enclosure_matches_lean_rationals() -> None:
    enclosure = mirror.forward_psi_enclosure(F(1, 4), terms=3)

    assert enclosure == mirror.RationalEnclosure(
        F(37999, 1008420), F(76003, 2016840)
    )
    assert enclosure.upper - enclosure.lower == F(1, 403368)
    assert mirror.empirical_bernstein_cgf(F(1), F(1, 4)) == F(3, 88)
    assert F(3, 88) < enclosure.lower


def test_boundary_certificates_recompute_from_their_separate_terms() -> None:
    split_hybrid = mirror.hybrid_penalty(mirror.SPLIT_FIVE, 5)
    psi_upper = mirror.forward_psi_quadratic_upper(F(1, 4))

    assert split_hybrid == F(53, 24)
    assert psi_upper == F(1, 24)
    assert mirror.closed_boundary(split_hybrid, F(0), F(1, 8), 5, F(1, 4)) == F(
        1, 10
    )
    assert mirror.closed_boundary(
        split_hybrid, psi_upper, F(1, 8), 5, F(1, 4)
    ) == F(25, 144)
    assert mirror.closed_boundary(split_hybrid, F(0), F(1), 5, F(1, 4)) == F(
        4, 5
    )
    assert mirror.closed_boundary(
        split_hybrid, psi_upper, F(1), 5, F(1, 4)
    ) == F(629, 720)


def test_two_sided_endpoint_uses_exact_half_budget() -> None:
    total_budget_coefficient = F(2)
    per_tail_coefficient = total_budget_coefficient / 2

    assert per_tail_coefficient == F(1)
    # Thus total delta = 2*exp(-1) becomes exp(-1) per tail, whose exact
    # log-budget is 1; no floating-point exp/log evaluation is needed.
    assert mirror.computed_witness_values()["BND-TWO-SIDED"] == F(629, 720)


@pytest.mark.parametrize("n", [0, -1])
def test_nonpositive_prefixes_fail_closed(n: int) -> None:
    with pytest.raises(ValueError, match="positive prefixes"):
        mirror.prefix_mean(mirror.SKEW_FOUR, n)
