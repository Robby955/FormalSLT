#!/usr/bin/env python3
"""Stage the FormalSLT research landing page over a doc-gen4 build.

The doc-gen4 output remains the source of declaration pages and search. This
script preserves its generated root as ``api.html``, installs the small static
reader-facing site, and publishes the concept index with source links pinned to
the exact commit that produced the documentation artifact.
"""

from __future__ import annotations

import argparse
import re
import shutil
import tempfile
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit
from xml.etree import ElementTree


ROOT = Path(__file__).resolve().parents[1]
SITE_ROOT = ROOT / "docs" / "site"
CONCEPT_INDEX = ROOT / "docs" / "INDEX.html"
THEOREM_CHAIN_SOURCE = ROOT / "docs" / "theorem-chain.svg"
SOURCE_REF_TOKEN = "__FORMALSLT_SOURCE_REF__"
UNPINNED_SOURCE_PREFIX = "https://github.com/Robby955/FormalSLT/blob/main/"
PINNED_SOURCE_PREFIX = "https://github.com/Robby955/FormalSLT/blob/{source_ref}/"
SITE_MARKER = 'data-formalslt-site="research"'

SITE_FILES = (
    "index.html",
    "assets/favicon.svg",
    "assets/formalslt-overview.mp4",
    "assets/formalslt-overview-poster.jpg",
    "assets/formalslt-overview.vtt",
    "assets/research-map.js",
    "assets/site.css",
    "assets/theorem-chain.svg",
    "readers/stats-ml/index.html",
    "readers/probability/index.html",
    "readers/lean/index.html",
    "readers/verification/index.html",
)

DOCGEN_PATHS = (
    "index.html",
    "search.html",
    "FormalSLT.html",
    "FormalSLT/PACBayes.html",
    "FormalSLT/Sequential.html",
    "FormalSLT/StochasticDynamics.html",
    "FormalSLT/VC.html",
    "FormalSLT/AnytimeValid/EProcess.html",
    "FormalSLT/PACBayes/ContinuousInfiniteEmpiricalBernsteinStitch.html",
    "FormalSLT/PACBayes/ForwardBesselPACBayesCountable.html",
    "FormalSLT/PACBayes/ForwardPredictableStrategyPACBayes.html",
    "FormalSLT/PACBayes/ForwardPredictableStrategyPACBayesCountable.html",
    "FormalSLT/PACBayes/ForwardBesselPACBayesOracle.html",
    "FormalSLT/PACBayes/ContinuousForwardPredictableMeanBesselPACBayesCountable.html",
    "FormalSLT/PACBayes/ContinuousForwardPredictableMeanBesselPACBayesOracle.html",
    "FormalSLT/StochasticDynamics/TrajectoryEmpiricalBernsteinPACBayesCountable.html",
    "FormalSLT/StochasticDynamics/TrajectoryForwardBesselPACBayesOracle.html",
    "FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes.html",
    "FormalSLT/StochasticDynamics/ContinuousMeasurableTrajectoryForwardBesselPACBayesOracle.html",
    "FormalSLT/StochasticDynamics/StationaryPoissonDepthSelection.html",
    "FormalSLT/StochasticDynamics/EmpiricalStationaryCatalog.html",
    "FormalSLT/StochasticDynamics/EmpiricalTransitionConfidenceCountable.html",
)

PUBLIC_ENDPOINTS = (
    "exists_continuousInfiniteEmpiricalBernstein_event",
    "exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event",
    "exists_continuousMeasurableTrajectoryGrowingPrefixForwardBesselPACBayesOracle_event",
    "exists_stationaryPoissonDepthSelection_allTime_vanishing_event",
    "exists_selectedCanonicalEmpiricalStationaryCatalog_event",
    "exists_growingPrefixForwardBesselPACBayesOracle_event",
    "exists_trajectoryGrowingPrefixForwardBesselPACBayesOracle_event",
)


class SiteHTMLParser(HTMLParser):
    """Collect local assets and basic accessibility failures."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.targets: list[str] = []
        self.images_without_alt = 0

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        values = dict(attrs)
        if tag == "a" and values.get("href"):
            self.targets.append(values["href"] or "")
        if tag in {"link", "script", "img", "source"}:
            target = values.get("href") if tag == "link" else values.get("src")
            if target:
                self.targets.append(target)
        if tag == "video":
            for attribute in ("src", "poster"):
                if values.get(attribute):
                    self.targets.append(values[attribute] or "")
        if tag == "img" and "alt" not in values:
            self.images_without_alt += 1


def _local_target(base: Path, href: str) -> Path | None:
    parsed = urlsplit(href)
    if parsed.scheme or parsed.netloc or not parsed.path:
        return None
    if parsed.path.startswith("/"):
        raise ValueError(
            f"root-relative link {href!r} would escape the GitHub Pages project path"
        )
    target = (base / unquote(parsed.path)).resolve()
    if parsed.path.endswith("/"):
        target /= "index.html"
    return target


def _parse_html(path: Path) -> SiteHTMLParser:
    parser = SiteHTMLParser()
    parser.feed(path.read_text(encoding="utf-8"))
    parser.close()
    if parser.images_without_alt:
        raise ValueError(f"{path}: image missing alt text")
    return parser


def validate_source_tree() -> None:
    missing = [rel for rel in SITE_FILES if not (SITE_ROOT / rel).is_file()]
    if missing:
        raise ValueError("missing static site files: " + ", ".join(missing))

    root_html = (SITE_ROOT / "index.html").read_text(encoding="utf-8")
    if SITE_MARKER not in root_html:
        raise ValueError("docs/site/index.html is missing the research-site marker")
    for endpoint in PUBLIC_ENDPOINTS:
        # Each endpoint occurs once in the doc-gen fragment and once as the
        # visible declaration label. Requiring the pair catches missing or
        # accidentally duplicated public rows.
        if root_html.count(endpoint) != 2:
            raise ValueError(
                f"docs/site/index.html must contain endpoint {endpoint!r} "
                "exactly twice (link and label)"
            )

    for rel in SITE_FILES:
        path = SITE_ROOT / rel
        if path.suffix != ".html":
            continue
        text = path.read_text(encoding="utf-8")
        if SOURCE_REF_TOKEN not in text:
            raise ValueError(f"{path}: missing exact-source placeholder")
        for marker in ('name="theme-color"', 'rel="canonical"', 'rel="icon"'):
            if marker not in text:
                raise ValueError(f"{path}: missing metadata marker {marker}")
        parser = _parse_html(path)
        for href in parser.targets:
            target = _local_target(path.parent, href)
            if target is None:
                continue
            try:
                relative = target.relative_to(SITE_ROOT)
            except ValueError as exc:
                raise ValueError(f"{path}: local link escapes docs/site: {href}") from exc
            runtime_rel = relative.as_posix()
            if runtime_rel in {
                "api.html",
                "search.html",
                "FormalSLT.html",
                "theorems/index.html",
            }:
                continue
            if runtime_rel.startswith("FormalSLT/"):
                continue
            if not target.is_file():
                raise ValueError(f"{path}: broken static link {href!r}")

    for marker in (
        'property="og:title"',
        'property="og:description"',
        'property="og:url"',
        'name="twitter:card"',
    ):
        if marker not in root_html:
            raise ValueError(f"docs/site/index.html is missing social marker {marker}")

    site_chain = SITE_ROOT / "assets" / "theorem-chain.svg"
    if not THEOREM_CHAIN_SOURCE.is_file():
        raise ValueError("docs/theorem-chain.svg is missing")
    if site_chain.read_bytes() != THEOREM_CHAIN_SOURCE.read_bytes():
        raise ValueError(
            "docs/site/assets/theorem-chain.svg is out of sync with "
            "docs/theorem-chain.svg"
        )
    ElementTree.parse(site_chain)
    if not CONCEPT_INDEX.is_file():
        raise ValueError("docs/INDEX.html is missing")
    concept_html = CONCEPT_INDEX.read_text(encoding="utf-8")
    if UNPINNED_SOURCE_PREFIX not in concept_html:
        raise ValueError("docs/INDEX.html has no main-branch source links to pin")
    if concept_html.count(SOURCE_REF_TOKEN) != 2:
        raise ValueError(
            "docs/INDEX.html must contain the exact-source placeholder twice "
            "(tree link and visible commit)"
        )


def _validate_source_ref(source_ref: str) -> str:
    if not re.fullmatch(r"[0-9a-fA-F]{40}", source_ref):
        raise ValueError("--source-ref must be a full 40-character Git commit SHA")
    return source_ref.lower()


def _copy_site(source_ref: str, doc_root: Path) -> None:
    for source in sorted(SITE_ROOT.rglob("*")):
        if not source.is_file():
            continue
        relative = source.relative_to(SITE_ROOT)
        destination = doc_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source.suffix == ".html":
            rendered = source.read_text(encoding="utf-8").replace(
                SOURCE_REF_TOKEN, source_ref
            )
            if SOURCE_REF_TOKEN in rendered:
                raise ValueError(f"unresolved source placeholder in {source}")
            destination.write_text(rendered, encoding="utf-8")
        else:
            shutil.copy2(source, destination)


def _copy_concept_index(source_ref: str, doc_root: Path) -> None:
    concept_html = CONCEPT_INDEX.read_text(encoding="utf-8")
    link_count = concept_html.count(UNPINNED_SOURCE_PREFIX)
    if link_count == 0:
        raise ValueError("docs/INDEX.html contains no source links to rewrite")
    staged = concept_html.replace(
        UNPINNED_SOURCE_PREFIX,
        PINNED_SOURCE_PREFIX.format(source_ref=source_ref),
    ).replace(SOURCE_REF_TOKEN, source_ref)
    if UNPINNED_SOURCE_PREFIX in staged:
        raise ValueError("an unpinned concept-index source link remains")
    if SOURCE_REF_TOKEN in staged:
        raise ValueError("an unresolved concept-index source placeholder remains")
    indexed_label = " indexed declarations &middot;"
    if staged.count(indexed_label) != 1 or " public declarations &middot;" in staged:
        raise ValueError("unexpected declaration-count label in docs/INDEX.html")
    destination = doc_root / "theorems" / "index.html"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(staged, encoding="utf-8")


def _validate_staged_links(doc_root: Path) -> None:
    staged_pages = [doc_root / rel for rel in SITE_FILES if rel.endswith(".html")]
    staged_pages.append(doc_root / "theorems" / "index.html")
    for page in staged_pages:
        parser = _parse_html(page)
        for href in parser.targets:
            target = _local_target(page.parent, href)
            if target is None:
                continue
            try:
                target.relative_to(doc_root)
            except ValueError as exc:
                raise ValueError(
                    f"{page}: staged link escapes documentation root: {href!r}"
                ) from exc
            if not target.is_file():
                raise ValueError(f"{page}: staged link target is missing: {href!r}")


def stage_site(doc_root: Path, source_ref: str) -> None:
    validate_source_tree()
    source_ref = _validate_source_ref(source_ref)
    doc_root = doc_root.resolve()
    missing = [rel for rel in DOCGEN_PATHS if not (doc_root / rel).is_file()]
    if missing:
        raise ValueError("doc-gen4 output is incomplete: " + ", ".join(missing))

    generated_root = doc_root / "index.html"
    api_root = doc_root / "api.html"
    generated_text = generated_root.read_text(encoding="utf-8")
    if SITE_MARKER in generated_text:
        if not api_root.is_file():
            raise ValueError("staged root found without preserved api.html")
    else:
        shutil.copy2(generated_root, api_root)

    _copy_site(source_ref, doc_root)
    _copy_concept_index(source_ref, doc_root)
    _validate_staged_links(doc_root)

    if SITE_MARKER not in generated_root.read_text(encoding="utf-8"):
        raise ValueError("custom landing page did not replace the doc-gen4 root")
    if SITE_MARKER in api_root.read_text(encoding="utf-8"):
        raise ValueError("api.html does not contain the preserved doc-gen4 root")
    print(
        f"staged FormalSLT research site in {doc_root} at source ref {source_ref}"
    )


def self_test() -> None:
    validate_source_tree()
    source_ref = "0123456789abcdef0123456789abcdef01234567"
    with tempfile.TemporaryDirectory(prefix="formalslt-docs-stage-") as tmp:
        fixture_root = Path(tmp)
        doc_root = fixture_root / "doc"
        for rel in DOCGEN_PATHS:
            path = doc_root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"<html><body>doc-gen4 {rel}</body></html>", encoding="utf-8")
        original_root = (doc_root / "index.html").read_bytes()
        stage_site(doc_root, source_ref)
        assert (doc_root / "api.html").read_bytes() == original_root
        assert SITE_MARKER in (doc_root / "index.html").read_text(encoding="utf-8")
        staged_index = (doc_root / "theorems" / "index.html").read_text(
            encoding="utf-8"
        )
        assert f"/blob/{source_ref}/" in staged_index
        assert UNPINNED_SOURCE_PREFIX not in staged_index
        assert " indexed declarations &middot;" in staged_index
        assert 'href="../">FormalSLT</a>' in staged_index
        assert 'aria-pressed="false"' in staged_index
        assert 'role="status" aria-live="polite" aria-atomic="true"' in staged_index
        assert 'rel="canonical" href="https://robby955.github.io/FormalSLT/theorems/"' in staged_index
        assert (doc_root / "assets" / "favicon.svg").is_file()
        assert SOURCE_REF_TOKEN not in "".join(
            page.read_text(encoding="utf-8")
            for page in doc_root.rglob("*.html")
        )
        outside = fixture_root / "outside.html"
        outside.write_text("<html><body>outside</body></html>", encoding="utf-8")
        staged_index_path = doc_root / "theorems" / "index.html"
        staged_index_path.write_text(
            staged_index + '<a href="../../outside.html">escape</a>',
            encoding="utf-8",
        )
        try:
            _validate_staged_links(doc_root)
        except ValueError as exc:
            assert "staged link escapes documentation root" in str(exc)
        else:
            raise AssertionError("staged-link validation accepted an escaping link")
        # Re-running staging must preserve the original generated API root.
        stage_site(doc_root, source_ref)
        assert (doc_root / "api.html").read_bytes() == original_root
    print("docs-site staging self-test passed")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check-source", action="store_true", help="validate docs/site without staging"
    )
    mode.add_argument(
        "--self-test", action="store_true", help="run staging against a temporary fixture"
    )
    parser.add_argument("--doc-root", type=Path, help="doc-gen4 output directory")
    parser.add_argument("--source-ref", help="full Git commit SHA for exact source links")
    args = parser.parse_args()

    if args.check_source:
        validate_source_tree()
        print("docs-site source check passed")
        return 0
    if args.self_test:
        self_test()
        return 0
    if args.doc_root is None or args.source_ref is None:
        parser.error("staging requires both --doc-root and --source-ref")
    stage_site(args.doc_root, args.source_ref)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
