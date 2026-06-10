"""Golden-file regression: committed generated certificates match the compiler.

The ``FormalSLT/PACBayes/Generated/Cert_*.lean`` modules and their
``examples/Check_Cert_*.lean`` companions are compiler outputs that get
committed. If ``compiler/compile.py`` changes its emission logic (or a
generated file is hand-edited), the committed artifacts silently stop being
reproducible. This test re-emits every spec in ``compiler/specs/`` and
requires byte-for-byte equality with the committed files.

On failure: either regenerate the certificates with
``python3 compiler/compile.py --spec compiler/specs/<id>.json`` or revert the
emission change, then rebuild and re-run the axiom checks before committing.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from compile import REPO_ROOT, emit_check_example, emit_lean, load_spec  # noqa: E402

SPECS_DIR = REPO_ROOT / "compiler" / "specs"
SPEC_PATHS = sorted(SPECS_DIR.glob("*.json"))


def test_specs_directory_is_nonempty():
    assert SPEC_PATHS, f"no specs found under {SPECS_DIR}"


@pytest.mark.parametrize("spec_path", SPEC_PATHS, ids=lambda p: p.stem)
def test_generated_lean_matches_compiler(spec_path: Path):
    spec = load_spec(spec_path)
    assert spec.lean_path.exists(), f"missing committed module {spec.lean_path}"
    assert emit_lean(spec) == spec.lean_path.read_text(), (
        f"{spec.lean_path.relative_to(REPO_ROOT)} is not reproducible from "
        f"{spec_path.name}; regenerate or revert the emission change"
    )


@pytest.mark.parametrize("spec_path", SPEC_PATHS, ids=lambda p: p.stem)
def test_check_example_matches_compiler(spec_path: Path):
    spec = load_spec(spec_path)
    assert spec.check_path.exists(), f"missing committed example {spec.check_path}"
    assert emit_check_example(spec) == spec.check_path.read_text(), (
        f"{spec.check_path.relative_to(REPO_ROOT)} is not reproducible from "
        f"{spec_path.name}; regenerate or revert the emission change"
    )
