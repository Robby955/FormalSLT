#!/usr/bin/env python3
"""
FormalSLT Coverage Benchmark  --  g4_coverage.py
=================================================
Inventories the theorem/lemma surface of FormalSLT by category, emits a
machine-regenerable coverage table and a figure (matplotlib if available,
SVG bar chart otherwise).

Usage
-----
    python3 benchmark/g4_coverage.py [--src <path>] [--out <dir>]

Defaults:
    --src  ../FormalSLT          (relative to this script's directory)
    --out  benchmark/output/     (relative to repo root)

Output files
------------
    coverage_table.txt    — human-readable plain-text table
    coverage_table.csv    — machine-readable CSV
    coverage_figure.png   — bar chart (matplotlib)  OR
    coverage_figure.svg   — bar chart (SVG fallback)

Honest framing
--------------
FormalSLT is one of at least three Lean 4 formalizations covering aspects of
statistical learning theory. The peer columns in the CSV are scaffold
placeholders; they must be filled in by a human after verifying each library's
actual coverage. Do NOT interpret TODO/UNVERIFIED entries as evidence that
those libraries lack coverage.

Known peer libraries (as of 2026-06; citations from reviewers, NOT verified
against the actual Lean sources):
    - Karayel-Tan  (AFP 2023) — Isabelle/HOL, not Lean; listed for context
    - Sonoda et al. 2025      — arXiv:2503.19605 (Lean 4, partial)
    - Zhang-Lee-Liu 2026      — arXiv:2602.02285 (Lean 4, partial)

Rob must verify which categories each peer library covers before any of these
columns appear in a publication.
"""

import argparse
import csv
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Category routing  —  maps each .lean file path to a benchmark category.
# The path segments used here are the actual FormalSLT directory names.
# ---------------------------------------------------------------------------

# Each entry: (path_fragment_regex, category_label)
# First match wins.
_PATH_RULES: List[Tuple[str, str]] = [
    # Anytime-valid / sequential testing
    (r"AnytimeValid",        "Anytime-Valid"),
    # Covering numbers and Dudley chaining
    (r"Covering",            "Covering / Dudley"),
    # Algorithmic stability (Bousquet-Elisseeff, RKHS)
    (r"Stability",           "Stability"),
    # VC dimension, Sauer-Shelah, sample complexity
    (r"VC",                  "VC Theory"),
    # Rademacher complexity
    (r"Rademacher",          "Rademacher"),
    # PAC-Bayes bounds
    (r"PACBayes",            "PAC-Bayes"),
    (r"PACBayes[A-Z]",       "PAC-Bayes"),   # top-level flat files
    # Online-to-PAC conversion
    (r"OnlineToPAC",         "Online-to-PAC"),
    # Azuma / McDiarmid concentration
    (r"Azuma",               "Concentration"),
    # Sub-Gamma and other concentration helpers
    (r"Concentration",       "Concentration"),
    # Probability infrastructure (sub-Gaussian, union bound, MGF, …)
    (r"Probability",         "Probability Foundations"),
    # Flagship composition / test-time meta proofs
    (r"TestTimeMeta",        "Flagship Meta"),
    # Top-level glue files
    (r"AlgorithmicStability","Stability"),
    (r"ERM\.lean",           "PAC-Bayes"),
    (r"GhostSample",         "Probability Foundations"),
    (r"Risk\.lean",          "Probability Foundations"),
    (r"UniformConvergence",  "Rademacher"),
    (r"PACBayesBernstein",   "PAC-Bayes"),
    (r"PACBayesBoundedLoss", "PAC-Bayes"),
    (r"PACBayesFiniteProductMGF", "PAC-Bayes"),
    (r"PACBayesKL",          "PAC-Bayes"),
    (r"PACBayesMcAllester",  "PAC-Bayes"),
    (r"PACBayesSeeger",      "PAC-Bayes"),
]

# Files to SKIP entirely when counting theorems/lemmas
_SKIP_PATTERNS: List[str] = [
    r"/Test/",
    r"/Generated/",
    r"TestTimeMeta/Flagship\.lean",  # pure import aggregator
    r"TestTimeMeta/MainTheorem\.lean",  # meta-composition only
]

# ---------------------------------------------------------------------------
# Benchmark categories and their descriptions
# ---------------------------------------------------------------------------

CATEGORIES: List[str] = [
    "Concentration",
    "Rademacher",
    "VC Theory",
    "Covering / Dudley",
    "PAC-Bayes",
    "Stability",
    "Anytime-Valid",
    "Online-to-PAC",
    "Probability Foundations",
    "Flagship Meta",
]

# Human-readable description for each category (used in README / table header)
CATEGORY_NOTES: Dict[str, str] = {
    "Concentration":          "Azuma, McDiarmid, sub-Gamma, Bennett",
    "Rademacher":             "Symmetrization, contraction, high-prob bounds, ERM generalization",
    "VC Theory":              "Sauer-Shelah, VC dimension, sample complexity (binary + real-valued)",
    "Covering / Dudley":      "Covering numbers, Dudley chaining, entropy integral",
    "PAC-Bayes":              "McAllester, Seeger, Bernstein, KL, Gaussian certificates, compiler",
    "Stability":              "Bousquet-Elisseeff uniform stability, RKHS regularised ERM",
    "Anytime-Valid":          "Ville maximal inequality, sub-Gamma confidence sequences",
    "Online-to-PAC":          "Cesa-Bianchi-Conconi-Gentile regret conversion",
    "Probability Foundations": "IID concentration, union bound, sub-Gaussian max, MGF infrastructure",
    "Flagship Meta":          "Test-time meta composition; online population decomposition",
}

# ---------------------------------------------------------------------------
# Peer libraries — placeholders only; do NOT invent numbers
# ---------------------------------------------------------------------------

PEERS: List[Dict] = [
    {
        "name": "Sonoda et al. 2025",
        "ref": "arXiv:2503.19605",
        "note": "Lean 4 — partial SLT formalization; coverage UNVERIFIED against source",
    },
    {
        "name": "Zhang-Lee-Liu 2026",
        "ref": "arXiv:2602.02285",
        "note": "Lean 4 — partial SLT formalization; coverage UNVERIFIED against source",
    },
    {
        "name": "Karayel-Tan 2023",
        "ref": "AFP 2023",
        "note": "Isabelle/HOL (not Lean 4); listed for completeness; coverage UNVERIFIED",
    },
]

# ---------------------------------------------------------------------------
# Verified peer cells — Zhang-Lee-Liu 2026 (YuanheZ, arXiv:2602.02285).
# Source-checked 2026-07-03 against the raw repo (github.com/YuanheZ/
# lean-stat-learning-theory @ be5d5a8) and README. Each cell carries a decl
# name + textbook ref. "no" = confirmed absent by whole-repo grep, not
# un-checked. The other two peer columns remain TODO/UNVERIFIED.
# Full write-up: HQ/ROB_QUEUE/yuanhez_coverage_diff_2026-07-03.md
# ---------------------------------------------------------------------------

_ZHANG_LEE_LIU_2026: Dict[str, str] = {
    "Concentration":
        "partial (gaussian_lipschitz_concentration/efronStein/gaussianPoincare, "
        "BLM 5.6/3.1/3.20; no Azuma/McDiarmid/Bennett/sub-Gamma)",
    "Rademacher":
        "no (no Rademacher-complexity spine; Gaussian analogue only: "
        "local_gaussian_complexity_bound, Wainwright 5.48)",
    "VC Theory":
        "no (no shatter/Sauer-Shelah/VC; grep=0)",
    "Covering / Dudley":
        "yes (dudley, BLM Cor 13.2, SLT/Dudley.lean:2517; continuous, more general)",
    "PAC-Bayes":
        "no (no PAC-Bayes/KL/posterior; convex-dual sibling only: "
        "entropy_duality, BLM Thm 4.13)",
    "Stability":
        "no (no Bousquet-Elisseeff/uniform stability; grep=0)",
    "Anytime-Valid":
        "no (no sequential/anytime-valid content)",
    "Online-to-PAC":
        "no (no online-learning/regret content)",
    "Probability Foundations":
        "partial (subGaussian_finite_max_bound, Wainwright Ex 2.12; "
        "lipschitz_cgf_bound, BLM Thm 5.5)",
    "Flagship Meta":
        "no (no analogue; their top-level assembly = master_error_bound, "
        "Wainwright Thm 13.5)",
}


def _peer_cell(peer_name: str, category: str) -> str:
    """Return the coverage cell for a given peer/category, cited where verified."""
    if peer_name == "Zhang-Lee-Liu 2026":
        return _ZHANG_LEE_LIU_2026.get(category, "TODO/UNVERIFIED")
    return "TODO/UNVERIFIED"


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class FileStats:
    path: Path
    category: str
    n_theorems: int    # `theorem` declarations
    n_lemmas: int      # `lemma` declarations
    n_lines: int
    has_sorry: bool


@dataclass
class CategoryStats:
    name: str
    files: List[FileStats] = field(default_factory=list)

    @property
    def n_theorems(self) -> int:
        return sum(f.n_theorems for f in self.files)

    @property
    def n_lemmas(self) -> int:
        return sum(f.n_lemmas for f in self.files)

    @property
    def n_total(self) -> int:
        return self.n_theorems + self.n_lemmas

    @property
    def n_lines(self) -> int:
        return sum(f.n_lines for f in self.files)

    @property
    def n_files(self) -> int:
        return len(self.files)

    @property
    def any_sorry(self) -> bool:
        return any(f.has_sorry for f in self.files)


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

_THEOREM_RE = re.compile(r"^\s*theorem\s+\w")
_LEMMA_RE   = re.compile(r"^\s*lemma\s+\w")
# sorry detection:
#   - skip pure comment lines (-- ...)
#   - skip lines where sorry/admit appear only inside backtick spans (`sorry`, `admit`)
#     or in prose negations ("no sorry", "no admit", "without sorry")
_SORRY_RE       = re.compile(r"\bsorry\b|\badmit\b")
_COMMENT_RE     = re.compile(r"^\s*--")
# Matches mentions that are documentation prose, not actual tactic calls
_SORRY_PROSE_RE = re.compile(
    r"`sorry`|`admit`"              # backtick-quoted references in doc strings
    r"|no\s+`?sorry`?"             # "no sorry" / "no `sorry`"
    r"|no\s+`?admit`?"             # "no admit" / "no `admit`"
    r"|without\s+sorry"
    r"|sorry-free"
)


def _line_has_real_sorry(line: str) -> bool:
    """True iff the line contains a genuine sorry/admit tactic call."""
    if _COMMENT_RE.match(line):
        return False
    if not _SORRY_RE.search(line):
        return False
    # Remove all prose-mention spans, then check again
    cleaned = _SORRY_PROSE_RE.sub("", line)
    return bool(_SORRY_RE.search(cleaned))


def parse_lean_file(path: Path) -> Tuple[int, int, int, bool]:
    """Return (n_theorems, n_lemmas, n_lines, has_sorry)."""
    n_theorems = 0
    n_lemmas = 0
    n_lines = 0
    has_sorry = False
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return 0, 0, 0, False

    for line in text.splitlines():
        n_lines += 1
        if _THEOREM_RE.match(line):
            n_theorems += 1
        if _LEMMA_RE.match(line):
            n_lemmas += 1
        if _line_has_real_sorry(line):
            has_sorry = True

    return n_theorems, n_lemmas, n_lines, has_sorry


def classify_file(path: Path, src_root: Path) -> Optional[str]:
    """Return the benchmark category for a .lean file, or None to skip."""
    rel = str(path.relative_to(src_root))
    # Skip patterns
    for pat in _SKIP_PATTERNS:
        if re.search(pat, rel):
            return None
    # Routing rules
    for pat, cat in _PATH_RULES:
        if re.search(pat, rel):
            return cat
    return "Probability Foundations"   # safe fallback for unmapped top-level files


# ---------------------------------------------------------------------------
# Inventory builder
# ---------------------------------------------------------------------------

def build_inventory(src_root: Path) -> Dict[str, CategoryStats]:
    stats: Dict[str, CategoryStats] = {cat: CategoryStats(cat) for cat in CATEGORIES}

    lean_files = sorted(src_root.rglob("*.lean"))
    if not lean_files:
        print(f"WARNING: no .lean files found under {src_root}", file=sys.stderr)

    for path in lean_files:
        cat = classify_file(path, src_root)
        if cat is None:
            continue
        if cat not in stats:
            stats[cat] = CategoryStats(cat)
        n_th, n_le, n_li, has_sorry = parse_lean_file(path)
        stats[cat].files.append(FileStats(
            path=path,
            category=cat,
            n_theorems=n_th,
            n_lemmas=n_le,
            n_lines=n_li,
            has_sorry=has_sorry,
        ))

    return stats


# ---------------------------------------------------------------------------
# Table rendering
# ---------------------------------------------------------------------------

def render_table(stats: Dict[str, CategoryStats]) -> str:
    """Return a plain-text, column-aligned table."""
    # Column headers
    col_cat   = "Category"
    col_files = "Files"
    col_thm   = "Theorems"
    col_lem   = "Lemmas"
    col_total = "Total Decls"
    col_lines = "LoC"
    col_sorry = "Sorry-free"
    peer_headers = [p["name"] for p in PEERS]

    rows = []
    for cat in CATEGORIES:
        if cat not in stats:
            continue
        s = stats[cat]
        sorry_flag = "YES" if not s.any_sorry else "NO (check source)"
        peer_vals = [_peer_cell(p["name"], cat) for p in PEERS]
        rows.append([cat, str(s.n_files), str(s.n_theorems), str(s.n_lemmas),
                     str(s.n_total), str(s.n_lines), sorry_flag] + peer_vals)

    # Totals
    total_files  = sum(stats[c].n_files  for c in CATEGORIES if c in stats)
    total_th     = sum(stats[c].n_theorems for c in CATEGORIES if c in stats)
    total_le     = sum(stats[c].n_lemmas   for c in CATEGORIES if c in stats)
    total_total  = sum(stats[c].n_total    for c in CATEGORIES if c in stats)
    total_lines  = sum(stats[c].n_lines    for c in CATEGORIES if c in stats)
    any_sorry    = any(stats[c].any_sorry  for c in CATEGORIES if c in stats)
    sorry_total  = "YES" if not any_sorry else "NO"
    rows.append(["TOTAL", str(total_files), str(total_th), str(total_le),
                 str(total_total), str(total_lines), sorry_total]
                + ["—"] * len(PEERS))

    headers = [col_cat, col_files, col_thm, col_lem, col_total,
               col_lines, col_sorry] + peer_headers

    # Compute column widths
    widths = [len(h) for h in headers]
    for row in rows:
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(cell))

    sep  = "  ".join("-" * w for w in widths)
    fmt  = "  ".join(f"{{:<{w}}}" for w in widths)

    lines = []
    lines.append(fmt.format(*headers))
    lines.append(sep)
    for row in rows[:-1]:
        lines.append(fmt.format(*row))
    lines.append(sep)
    lines.append(fmt.format(*rows[-1]))   # TOTAL row
    return "\n".join(lines)


def render_csv(stats: Dict[str, CategoryStats]) -> str:
    """Return CSV content."""
    import io
    buf = io.StringIO()
    peer_names = [p["name"] for p in PEERS]
    fieldnames = ["category", "files", "theorems", "lemmas", "total_decls",
                  "loc", "sorry_free", "notes"] + peer_names
    writer = csv.DictWriter(buf, fieldnames=fieldnames)
    writer.writeheader()

    for cat in CATEGORIES:
        if cat not in stats:
            continue
        s = stats[cat]
        row = {
            "category":    cat,
            "files":       s.n_files,
            "theorems":    s.n_theorems,
            "lemmas":      s.n_lemmas,
            "total_decls": s.n_total,
            "loc":         s.n_lines,
            "sorry_free":  "yes" if not s.any_sorry else "no",
            "notes":       CATEGORY_NOTES.get(cat, ""),
        }
        for p in PEERS:
            row[p["name"]] = _peer_cell(p["name"], cat)
        writer.writerow(row)

    # Totals
    total_th    = sum(stats[c].n_theorems for c in CATEGORIES if c in stats)
    total_le    = sum(stats[c].n_lemmas   for c in CATEGORIES if c in stats)
    total_total = sum(stats[c].n_total    for c in CATEGORIES if c in stats)
    total_files = sum(stats[c].n_files    for c in CATEGORIES if c in stats)
    total_lines = sum(stats[c].n_lines    for c in CATEGORIES if c in stats)
    any_sorry   = any(stats[c].any_sorry  for c in CATEGORIES if c in stats)
    total_row = {
        "category":    "TOTAL",
        "files":       total_files,
        "theorems":    total_th,
        "lemmas":      total_le,
        "total_decls": total_total,
        "loc":         total_lines,
        "sorry_free":  "yes" if not any_sorry else "no",
        "notes":       "",
    }
    for p in PEERS:
        total_row[p["name"]] = "—"
    writer.writerow(total_row)

    return buf.getvalue()


# ---------------------------------------------------------------------------
# Figure rendering
# ---------------------------------------------------------------------------

def _try_matplotlib(stats: Dict[str, CategoryStats], out_path: Path) -> bool:
    """Try to render with matplotlib. Return True on success."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        return False

    cats  = [c for c in CATEGORIES if c in stats and stats[c].n_total > 0]
    totals = [stats[c].n_total for c in cats]
    thms   = [stats[c].n_theorems for c in cats]
    lems   = [stats[c].n_lemmas   for c in cats]

    x = range(len(cats))
    fig, ax = plt.subplots(figsize=(12, 6))
    bar_w = 0.55
    ax.bar(x, lems,  bar_w, label="Lemmas",   color="#4c84c4")
    ax.bar(x, thms,  bar_w, bottom=lems, label="Theorems", color="#e07b42")

    ax.set_xticks(list(x))
    ax.set_xticklabels(cats, rotation=30, ha="right", fontsize=9)
    ax.set_ylabel("Declarations (theorems + lemmas)")
    ax.set_title("FormalSLT: formal declaration count by category\n"
                 "(generated by benchmark/g4_coverage.py — local only, not published)")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return True


def _svg_fallback(stats: Dict[str, CategoryStats], out_path: Path) -> None:
    """Emit a minimal SVG bar chart."""
    cats   = [c for c in CATEGORIES if c in stats and stats[c].n_total > 0]
    totals = [stats[c].n_total for c in cats]
    max_v  = max(totals) if totals else 1

    bar_w   = 60
    gap     = 14
    margin  = 60
    height  = 300
    label_h = 90
    svg_w   = margin * 2 + len(cats) * (bar_w + gap)
    svg_h   = height + label_h + 40

    bars = []
    for i, (cat, tot) in enumerate(zip(cats, totals)):
        bh = int(tot / max_v * height)
        x  = margin + i * (bar_w + gap)
        y  = height - bh + 20
        bars.append(
            f'<rect x="{x}" y="{y}" width="{bar_w}" height="{bh}" '
            f'fill="#4c84c4" opacity="0.85"/>'
        )
        bars.append(
            f'<text x="{x + bar_w//2}" y="{y - 4}" '
            f'text-anchor="middle" font-size="10" fill="#222">{tot}</text>'
        )
        # Rotated label
        lx = x + bar_w // 2
        ly = height + 28
        bars.append(
            f'<text transform="rotate(-35,{lx},{ly})" x="{lx}" y="{ly}" '
            f'text-anchor="end" font-size="9" fill="#333">{cat}</text>'
        )

    title_y = svg_h - 10
    svg = (
        f'<svg xmlns="http://www.w3.org/2000/svg" '
        f'width="{svg_w}" height="{svg_h}">\n'
        f'<rect width="{svg_w}" height="{svg_h}" fill="#fafafa"/>\n'
        + "\n".join(bars) +
        f'\n<text x="{svg_w//2}" y="15" text-anchor="middle" '
        f'font-size="12" fill="#111">FormalSLT declaration count by category</text>\n'
        f'</svg>\n'
    )
    out_path.write_text(svg, encoding="utf-8")


def render_figure(stats: Dict[str, CategoryStats], out_dir: Path) -> Path:
    png_path = out_dir / "coverage_figure.png"
    svg_path = out_dir / "coverage_figure.svg"
    if _try_matplotlib(stats, png_path):
        return png_path
    _svg_fallback(stats, svg_path)
    return svg_path


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> None:
    script_dir = Path(__file__).resolve().parent
    repo_root  = script_dir.parent

    parser = argparse.ArgumentParser(
        description="FormalSLT coverage inventory (G4 benchmark)"
    )
    parser.add_argument(
        "--src", default=str(repo_root / "FormalSLT"),
        help="Path to the FormalSLT source directory (contains .lean files)"
    )
    parser.add_argument(
        "--out", default=str(script_dir / "output"),
        help="Output directory for table, CSV, and figure"
    )
    args = parser.parse_args(argv)

    src_root = Path(args.src).resolve()
    out_dir  = Path(args.out).resolve()

    if not src_root.exists():
        print(f"ERROR: source directory not found: {src_root}", file=sys.stderr)
        sys.exit(1)

    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Scanning: {src_root}")
    stats = build_inventory(src_root)

    # ---- plain-text table ----
    table_txt = render_table(stats)
    txt_path  = out_dir / "coverage_table.txt"
    txt_path.write_text(table_txt + "\n", encoding="utf-8")
    print(f"Table  -> {txt_path}")
    print()
    print(table_txt)
    print()

    # ---- CSV ----
    csv_content = render_csv(stats)
    csv_path    = out_dir / "coverage_table.csv"
    csv_path.write_text(csv_content, encoding="utf-8")
    print(f"CSV    -> {csv_path}")

    # ---- figure ----
    fig_path = render_figure(stats, out_dir)
    print(f"Figure -> {fig_path}")

    # ---- peer library reminder ----
    print()
    print("=" * 70)
    print("PEER LIBRARY COLUMNS  —  require Rob to verify before publication")
    print("=" * 70)
    for p in PEERS:
        print(f"  {p['name']}  [{p['ref']}]")
        print(f"    {p['note']}")
    print()
    print("Do NOT publish the peer columns until each library's .lean source")
    print("has been manually checked for each category listed above.")
    print("=" * 70)


if __name__ == "__main__":
    main()
