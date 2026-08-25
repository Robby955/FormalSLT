#!/usr/bin/env python3
"""Stage checked stitched-LIL films, posters, captions, and receipts."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


PACKAGE_DIR = Path(__file__).resolve().parent
OUT_DIR = PACKAGE_DIR / "out"
DELIVERY_DIR = PACKAGE_DIR / "delivery"
FACTS = json.loads((PACKAGE_DIR / "facts.json").read_text(encoding="utf-8"))
CLAIMS = json.loads((PACKAGE_DIR / "claim-receipt.json").read_text(encoding="utf-8"))

CUTS = {
    "main": {
        "video": "stitched-lil-result-1920x1080.mp4",
        "receipt": "stitched-lil-result-1920x1080-receipt.json",
        "poster": "stitched-lil-result-poster-1920x1080.png",
        "resolution": [1920, 1080],
        "captions": "captions-main.vtt",
        "transcript": "TRANSCRIPT.md",
    },
    "social": {
        "video": "stitched-lil-result-1080x1350.mp4",
        "receipt": "stitched-lil-result-1080x1350-receipt.json",
        "poster": "stitched-lil-result-poster-1080x1350.png",
        "resolution": [1080, 1350],
        "captions": "captions-social.vtt",
        "transcript": "TRANSCRIPT-SOCIAL.md",
    },
}
STATIC_FILES = (
    "facts.json",
    "claim-receipt.json",
    "README.md",
    "SOUNDTRACK.md",
    "DELIVERY.md",
)
BUILT_IN_SOUNDTRACK_ID = "formalslt-stitched-lil-sparse-score-v2"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def soundtrack_mode(soundtrack: dict[str, Any]) -> str | None:
    mode = soundtrack.get("soundtrack_mode")
    if mode is None and soundtrack.get("soundtrack_id") == BUILT_IN_SOUNDTRACK_ID:
        return "built_in"
    return mode


def validate_common_soundtrack_source(cut_receipts: dict[str, Any]) -> str:
    modes = {
        soundtrack_mode(receipt["soundtrack"]) for receipt in cut_receipts.values()
    }
    if len(modes) != 1:
        raise ValueError("the two films use different soundtrack modes")
    mode = next(iter(modes))
    if mode == "external_master":
        source_pairs = {
            (
                receipt["soundtrack"]["raw_master"].get("sha256"),
                receipt["soundtrack"]["provenance"].get("sha256"),
            )
            for receipt in cut_receipts.values()
        }
        if len(source_pairs) != 1:
            raise ValueError("the two films do not bind the same external master and provenance")
    if mode not in ("built_in", "external_master", "silent"):
        raise ValueError("the two films have an invalid soundtrack mode")
    return mode


def probe_image(path: Path, ffprobe: str) -> dict[str, Any]:
    completed = subprocess.run(
        [
            ffprobe,
            "-v",
            "error",
            "-select_streams",
            "v:0",
            "-show_entries",
            "stream=codec_name,width,height",
            "-of",
            "json",
            str(path),
        ],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    streams = json.loads(completed.stdout).get("streams", [])
    if len(streams) != 1:
        raise ValueError(f"expected one poster image stream: {path}")
    stream = streams[0]
    return {
        "codec": stream.get("codec_name"),
        "width": int(stream.get("width", 0)),
        "height": int(stream.get("height", 0)),
    }


def validate_media_receipt(
    receipt: dict[str, Any],
    composition: str,
    video: Path,
) -> str:
    if receipt.get("schema") != "formalslt-stitched-lil-media-receipt-v2":
        raise ValueError(f"unexpected media receipt schema for {composition}")
    if receipt.get("quality") != "final" or receipt.get("composition") != composition:
        raise ValueError(f"media receipt does not identify final {composition} composition")
    if receipt.get("theorem_source_commit") != FACTS["commit"]:
        raise ValueError(f"media receipt theorem commit drifted for {composition}")
    if receipt.get("theorem_blob_oid") != CLAIMS["theorem_blob_oid"]:
        raise ValueError(f"media receipt theorem blob drifted for {composition}")
    video_receipt = receipt.get("video", {})
    if video_receipt.get("file") != video.name:
        raise ValueError(f"media receipt filename drifted for {composition}")
    if video_receipt.get("sha256") != sha256(video):
        raise ValueError(f"media receipt hash does not match {video.name}")
    if int(video_receipt.get("bytes", -1)) != video.stat().st_size:
        raise ValueError(f"media receipt size does not match {video.name}")
    soundtrack = receipt.get("soundtrack", {})
    mode = soundtrack_mode(soundtrack)
    if mode not in ("built_in", "external_master", "silent"):
        raise ValueError(f"media receipt has an invalid soundtrack mode for {composition}")
    if mode == "external_master":
        if soundtrack.get("third_party_audio") is not True:
            raise ValueError(f"external soundtrack disclosure is missing for {composition}")
        for section in ("raw_master", "provenance", "derivation"):
            if not isinstance(soundtrack.get(section), dict):
                raise ValueError(f"external soundtrack {section} is missing for {composition}")
    if mode == "silent":
        if soundtrack.get("third_party_audio") is not False:
            raise ValueError(f"silent soundtrack disclosure is invalid for {composition}")
        if int(video_receipt.get("audio_streams", -1)) != 0:
            raise ValueError(f"silent media receipt has an audio stream for {composition}")
        if "muxed_audio_measurement" in receipt:
            raise ValueError(f"silent media receipt has an audio measurement for {composition}")
    expected = CUTS[composition]["resolution"]
    observed = [video_receipt.get("width"), video_receipt.get("height")]
    if observed != expected:
        raise ValueError(f"media receipt dimensions drifted for {composition}: {observed}")
    render_commit = receipt.get("render_source_commit")
    if not isinstance(render_commit, str) or len(render_commit) != 40:
        raise ValueError(f"invalid render-source commit for {composition}")
    return render_commit


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def delivery_cut(receipt: dict[str, Any]) -> dict[str, Any]:
    payload = {
        "video": receipt["video"],
        "soundtrack": receipt["soundtrack"],
    }
    if "muxed_audio_measurement" in receipt:
        payload["muxed_audio_measurement"] = receipt["muxed_audio_measurement"]
    return payload


def stage(ffprobe: str) -> Path:
    if FACTS["commit"] != CLAIMS["theorem_source_commit"]:
        raise ValueError("fact and claim receipts bind different theorem commits")
    payloads: dict[str, Path] = {}
    cut_receipts: dict[str, Any] = {}
    render_commits: set[str] = set()
    posters: dict[str, Any] = {}

    for composition, contract in CUTS.items():
        video = OUT_DIR / contract["video"]
        receipt_path = OUT_DIR / contract["receipt"]
        poster = OUT_DIR / contract["poster"]
        for path in (video, receipt_path, poster):
            if not path.is_file():
                raise ValueError(f"missing final artifact: {path}")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        render_commits.add(validate_media_receipt(receipt, composition, video))
        image = probe_image(poster, ffprobe)
        if image["codec"] != "png" or [image["width"], image["height"]] != contract["resolution"]:
            raise ValueError(f"poster dimensions or codec drifted for {composition}: {image}")
        image.update({"file": poster.name, "bytes": poster.stat().st_size, "sha256": sha256(poster)})
        posters[composition] = image
        cut_receipts[composition] = receipt
        payloads[video.name] = video
        payloads[receipt_path.name] = receipt_path
        payloads[poster.name] = poster
        for source_name in (contract["captions"], contract["transcript"]):
            payloads[source_name] = PACKAGE_DIR / source_name

    if len(render_commits) != 1:
        raise ValueError("the two films were not rendered from one source commit")
    validate_common_soundtrack_source(cut_receipts)
    for name in STATIC_FILES:
        payloads[name] = PACKAGE_DIR / name
    for name, path in payloads.items():
        if not path.is_file():
            raise ValueError(f"missing delivery payload {name}: {path}")

    temporary = Path(tempfile.mkdtemp(prefix=".stitched-lil-delivery-", dir=PACKAGE_DIR))
    try:
        for name, source in sorted(payloads.items()):
            shutil.copy2(source, temporary / name)
        receipt = {
            "schema": "formalslt-stitched-lil-delivery-receipt-v1",
            "theorem_source_commit": FACTS["commit"],
            "theorem_blob_oid": CLAIMS["theorem_blob_oid"],
            "render_source_commit": next(iter(render_commits)),
            "classification": CLAIMS["classification"],
            "posters": posters,
            "cuts": {
                composition: delivery_cut(receipt)
                for composition, receipt in cut_receipts.items()
            },
            "files": {
                path.name: {"bytes": path.stat().st_size, "sha256": sha256(path)}
                for path in sorted(
                    (temporary / name for name in payloads),
                    key=lambda item: item.name,
                )
            },
        }
        write_json(temporary / "delivery-receipt.json", receipt)
        manifest_files = sorted(
            path for path in temporary.iterdir() if path.name != "MANIFEST.sha256"
        )
        manifest = "".join(f"{sha256(path)}  {path.name}\n" for path in manifest_files)
        (temporary / "MANIFEST.sha256").write_text(manifest, encoding="utf-8")

        expected_names = {path.name for path in temporary.iterdir()}
        if DELIVERY_DIR.exists():
            unexpected = {
                path.name for path in DELIVERY_DIR.iterdir()
            } - expected_names
            if unexpected:
                raise ValueError(
                    "delivery directory contains unrecognized files: "
                    + ", ".join(sorted(unexpected))
                )
        DELIVERY_DIR.mkdir(parents=True, exist_ok=True)
        for path in sorted(temporary.iterdir()):
            path.replace(DELIVERY_DIR / path.name)
    finally:
        if temporary.exists():
            for path in temporary.iterdir():
                if not path.is_file():
                    raise ValueError(f"unexpected directory in delivery staging area: {path}")
                path.unlink()
            temporary.rmdir()
    return DELIVERY_DIR


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ffprobe", default="ffprobe")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    destination = stage(args.ffprobe)
    print(destination)


if __name__ == "__main__":
    main()
