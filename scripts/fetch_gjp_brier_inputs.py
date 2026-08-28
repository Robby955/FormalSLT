#!/usr/bin/env python3
"""Fetch and digest-verify the pinned Good Judgment Project input files.

This fetcher writes only to a caller-supplied directory outside the tracked
tree.  It does not parse a forecast, join an outcome, build a stream, or write
any tracked artifact.  It refuses to run while any reserved prospective output
already exists, so it cannot be used to quietly produce a result under the
prospective protocol.

Each file is requested with ``?format=original``.  Dataverse ingests tabular
files and the plain access route returns a regenerated TSV whose bytes do not
match the published MD5, so the original route is the only one that replays.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.request
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROTOCOL = (
    ROOT / "applications" / "brier_monitor" / "realdata" / "gjp-brier-protocol-v1.json"
)
CHUNK = 1 << 20


class FetchError(RuntimeError):
    """Raised when a download is missing, malformed, or fails its digest."""


def load_protocol(path: Path) -> dict[str, Any]:
    protocol = json.loads(path.read_text(encoding="utf-8"))
    for relative in protocol["fresh_output_paths"]:
        if (ROOT / relative).exists():
            raise FetchError(
                f"reserved prospective output already exists: {relative}; refusing to fetch"
            )
    return protocol


def md5_of(path: Path) -> str:
    digest = hashlib.md5()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(CHUNK), b""):
            digest.update(block)
    return digest.hexdigest()


def fetch_one(route: str, entry: dict[str, Any], out_dir: Path, timeout: int) -> Path:
    target = out_dir / str(entry["filename"])
    url = route.format(id=entry["dataverse_id"])
    if not url.startswith("https://"):
        raise FetchError(f"refusing a non-HTTPS access route: {url}")
    if not target.exists():
        temporary = target.with_suffix(target.suffix + ".partial")
        with urllib.request.urlopen(url, timeout=timeout) as response:
            with temporary.open("wb") as handle:
                while True:
                    block = response.read(CHUNK)
                    if not block:
                        break
                    handle.write(block)
        temporary.replace(target)
    actual = md5_of(target)
    if actual != entry["md5"]:
        raise FetchError(
            f"{entry['filename']} MD5 {actual} does not match the pinned {entry['md5']}; "
            "check that the request used format=original"
        )
    expected_bytes = entry.get("original_bytes_confirmed")
    size = target.stat().st_size
    if expected_bytes is not None and size != expected_bytes:
        raise FetchError(
            f"{entry['filename']} is {size} bytes, not the confirmed {expected_bytes}"
        )
    return target


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument(
        "--verify-only",
        action="store_true",
        help="verify digests of files already present and download nothing",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        protocol = load_protocol(args.protocol)
        dataset = protocol["dataset"]
        out_dir = args.out.resolve()
        try:
            out_dir.relative_to(ROOT.resolve())
        except ValueError:
            pass
        else:
            raise FetchError("--out must lie outside the repository; inputs are never tracked")
        out_dir.mkdir(parents=True, exist_ok=True)
        for entry in dataset["files"]:
            target = out_dir / str(entry["filename"])
            if args.verify_only:
                if not target.exists():
                    raise FetchError(f"{entry['filename']} is absent under {out_dir}")
                actual = md5_of(target)
                if actual != entry["md5"]:
                    raise FetchError(
                        f"{entry['filename']} MD5 {actual} does not match the pinned {entry['md5']}"
                    )
            else:
                target = fetch_one(str(dataset["access_route"]), entry, out_dir, args.timeout)
            print(f"verified {entry['filename']} {entry['md5']}")
    except (OSError, KeyError, ValueError, FetchError) as error:
        print(f"ERROR: GJP input fetch refused: {error}", file=sys.stderr)
        return 1
    print(f"all pinned {protocol['dataset']['persistent_id']} inputs verified under {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
