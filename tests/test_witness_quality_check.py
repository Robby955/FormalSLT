from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "witness_quality_check.py"


def run_checker(tmp_path: Path, source: str) -> subprocess.CompletedProcess[str]:
    fixture = tmp_path / "Fixture.lean"
    fixture.write_text(source, encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(CHECKER), str(fixture)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_comment_only_declaration_is_rejected(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
#check Demo.target
-- theorem fake : Demo.Target := Demo.target
/- example : Demo.Target := Demo.target -/
""",
    )

    assert result.returncode == 1
    assert result.stdout.rstrip().endswith("FAKE")


def test_unrelated_trivial_theorem_is_rejected(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
#check Demo.target
theorem unrelated_arithmetic : (1 : Nat) + 1 = 2 := rfl
#print axioms unrelated_arithmetic
""",
    )

    assert result.returncode == 1
    assert result.stdout.rstrip().endswith("FAKE")


def test_linked_anonymous_example_is_accepted(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
#check Demo.target
example : Demo.Target := Demo.target
""",
    )

    assert result.returncode == 0
    assert result.stdout.rstrip().endswith("CONCRETE")


def test_own_axiom_print_does_not_make_declaration_a_receipt(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
theorem circular_receipt : True := by trivial
#print axioms circular_receipt
""",
    )

    assert result.returncode == 1
    assert result.stdout.rstrip().endswith("FAKE")


def test_snake_case_parameter_does_not_fake_project_link(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
#check Demo.target
theorem unrelated_parameter (fake_input : Nat) : fake_input = fake_input := rfl
""",
    )

    assert result.returncode == 1
    assert result.stdout.rstrip().endswith("FAKE")


def test_imported_formalslt_declaration_is_a_project_link(tmp_path: Path) -> None:
    result = run_checker(
        tmp_path,
        """
import FormalSLT.AnytimeValid.DyadicEpochCS
example : ¬ Summable literalDyadicEpochWeight :=
  literalDyadicEpochWeight_not_summable
""",
    )

    assert result.returncode == 0
    assert result.stdout.rstrip().endswith("CONCRETE")
