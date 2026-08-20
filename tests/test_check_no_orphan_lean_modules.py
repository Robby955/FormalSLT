from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_no_orphan_lean_modules.py"


def load_script():
    spec = importlib.util.spec_from_file_location("check_no_orphan_lean_modules", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_find_orphan_modules_reports_unreachable_formalslt_files(tmp_path: Path) -> None:
    write(tmp_path / "FormalSLT.lean", "import FormalSLT.A\n")
    write(tmp_path / "FormalSLT" / "A.lean", "import FormalSLT.B\n")
    write(tmp_path / "FormalSLT" / "B.lean", "")
    write(tmp_path / "FormalSLT" / "Orphan.lean", "")

    module = load_script()

    assert module.find_orphan_modules(tmp_path) == ["FormalSLT.Orphan"]


def test_find_orphan_modules_accepts_all_root_reachable_files(tmp_path: Path) -> None:
    write(tmp_path / "FormalSLT.lean", "import FormalSLT.A\n")
    write(tmp_path / "FormalSLT" / "A.lean", "import FormalSLT.B\n")
    write(tmp_path / "FormalSLT" / "B.lean", "")

    module = load_script()

    assert module.find_orphan_modules(tmp_path) == []


def test_applications_umbrella_is_independent_reachability_root(tmp_path: Path) -> None:
    write(tmp_path / "FormalSLT.lean", "import FormalSLT.Core\n")
    write(tmp_path / "FormalSLT" / "Core.lean", "")
    write(
        tmp_path / "FormalSLT" / "Applications.lean",
        "import FormalSLT.Applications.WorkedExample\n",
    )
    write(tmp_path / "FormalSLT" / "Applications" / "WorkedExample.lean", "")

    module = load_script()

    assert module.find_orphan_modules(tmp_path) == []
    assert module.find_core_application_imports(tmp_path) == []


def test_default_umbrella_must_not_import_applications(tmp_path: Path) -> None:
    write(tmp_path / "FormalSLT.lean", "import FormalSLT.Applications\n")
    write(
        tmp_path / "FormalSLT" / "Applications.lean",
        "import FormalSLT.Applications.WorkedExample\n",
    )
    write(tmp_path / "FormalSLT" / "Applications" / "WorkedExample.lean", "")

    module = load_script()

    assert module.find_orphan_modules(tmp_path) == []
    assert module.find_core_application_imports(tmp_path) == [
        "FormalSLT.Applications",
        "FormalSLT.Applications.WorkedExample",
    ]
