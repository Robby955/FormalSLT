from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "statement_fidelity_check.py"


def run_checker(tmp_path: Path, body: str) -> subprocess.CompletedProcess[str]:
    fixture = tmp_path / "Fixture.lean"
    fixture.write_text(body, encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(CHECKER), str(fixture)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_private_and_protected_decls_are_checked(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
private theorem hidden_vacuous {t : ℝ} (f g : ℝ → ℝ) :
    ∃ c : ℝ, ‖f t‖ ≤ c * (g t) := by
  sorry

protected lemma exposed_vacuous {x : ℝ} (f g : ℝ → ℝ) :
    ∃ c : ℝ, ‖f x‖ ≤ c * (g x) := by
  sorry
""",
    )

    assert result.returncode == 1
    assert "hidden_vacuous" in result.stdout
    assert "exposed_vacuous" in result.stdout
    assert "--- checked 2 decl(s), 2 flag(s)" in result.stdout


def test_attribute_prefixed_decls_are_checked(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
@[simp] theorem attributed_vacuous {t : ℝ} (f g : ℝ → ℝ) :
    ∃ c : ℝ, ‖f t‖ ≤ c * (g t) := by
  sorry
""",
    )

    assert result.returncode == 1
    assert "attributed_vacuous" in result.stdout
    assert "--- checked 1 decl(s), 1 flag(s)" in result.stdout


def test_param_mentions_use_whole_tokens(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
theorem substring_only_is_sound {t : ℝ} (foo_atlas : ℝ → ℝ) :
    ∃ c : ℝ, ‖foo_atlas 0‖ ≤ c * 1 := by
  sorry
""",
    )

    assert result.returncode == 0
    assert "QUANTIFIER-INVERSION" not in result.stdout


def test_fidelity_signoff_must_be_comment_line(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
theorem spoofed_fidelity {t : ℝ} (f g : ℝ → ℝ)
    (label : String := "-- fidelity: not a comment") :
    ∃ c : ℝ, ‖f t‖ ≤ c * (g t) := by
  sorry
""",
    )

    assert result.returncode == 1
    assert "FLAG QUANTIFIER-INVERSION" in result.stdout
    assert "ok(signed)" not in result.stdout


def test_term_proof_after_walrus_is_not_linted_as_statement(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
theorem term_proof_body_is_ignored {t : ℝ} (f g : ℝ → ℝ) : 0 = 0 := (by
    have h : ∃ c : ℝ, ‖f t‖ ≤ c * (g t) := by
      exact ⟨0, by simp⟩
    rfl)
""",
    )

    assert result.returncode == 0
    assert "QUANTIFIER-INVERSION" not in result.stdout
    assert "--- checked 1 decl(s), 0 flag(s)" in result.stdout


def test_comment_line_fidelity_signoff_is_accepted(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
-- fidelity: this fixture intentionally signs a synthetic flag.
theorem signed_fidelity {t : ℝ} (f g : ℝ → ℝ) :
    ∃ c : ℝ, ‖f t‖ ≤ c * (g t) := by
  sorry
""",
    )

    assert result.returncode == 0
    assert "ok(signed) QUANTIFIER-INVERSION" in result.stdout
