#!/usr/bin/env python3
"""Verify a rendered stitched-LIL film and write a source-bound receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any


PACKAGE_DIR = Path(__file__).resolve().parent
ROOT = PACKAGE_DIR.parents[1]
CONFIG = json.loads((PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8"))
FACTS = json.loads((PACKAGE_DIR / "facts.json").read_text(encoding="utf-8"))
MAX_DURATION_DRIFT_SECONDS = 0.50
MAX_AUDIO_VIDEO_DRIFT_SECONDS = 0.10
MAX_PEAK_DBFS = -3.0
SOURCE_ASSETS = (
    "STORYBOARD.md",
    "TRANSCRIPT.md",
    "SOUNDTRACK.md",
    "compose_soundtrack.py",
    "extract_facts.py",
    "facts.json",
    "film_config.json",
    "manim.cfg",
    "render.sh",
    "stitched_lil_result.py",
    "verify_media.py",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_head() -> str:
    return subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout.strip()


def source_asset_hashes(head: str) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for name in SOURCE_ASSETS:
        path = PACKAGE_DIR / name
        relative = path.relative_to(ROOT).as_posix()
        try:
            committed = subprocess.run(
                ["git", "-C", str(ROOT), "show", f"{head}:{relative}"],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            ).stdout
        except subprocess.CalledProcessError as error:
            raise ValueError(f"source asset is not committed at HEAD: {relative}") from error
        worktree_hash = sha256(path)
        committed_hash = hashlib.sha256(committed).hexdigest()
        if worktree_hash != committed_hash:
            raise ValueError(f"source asset differs from HEAD: {relative}")
        hashes[name] = worktree_hash
    return hashes


def ffprobe(path: Path, executable: str) -> dict[str, Any]:
    completed = subprocess.run(
        [
            executable,
            "-v",
            "error",
            "-print_format",
            "json",
            "-show_format",
            "-show_streams",
            str(path),
        ],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return json.loads(completed.stdout)


def _one_stream(probe: dict[str, Any], codec_type: str) -> dict[str, Any]:
    streams = [
        stream for stream in probe.get("streams", [])
        if stream.get("codec_type") == codec_type
    ]
    if len(streams) != 1:
        raise ValueError(f"expected one {codec_type} stream, found {len(streams)}")
    return streams[0]


def _finite_float(value: Any, label: str) -> float:
    try:
        number = float(value)
    except (TypeError, ValueError) as error:
        raise ValueError(f"invalid {label}: {value!r}") from error
    if not math.isfinite(number):
        raise ValueError(f"non-finite {label}: {number!r}")
    return number


def validate_probe(probe: dict[str, Any], profile: str) -> dict[str, Any]:
    video = _one_stream(probe, "video")
    audio = _one_stream(probe, "audio")
    duration = _finite_float(probe.get("format", {}).get("duration"), "duration")
    expected_duration = float(CONFIG["duration_seconds"])
    if abs(duration - expected_duration) > MAX_DURATION_DRIFT_SECONDS:
        raise ValueError(
            f"movie duration {duration:.3f}s drifted from {expected_duration:.3f}s"
        )

    width = int(video.get("width", 0))
    height = int(video.get("height", 0))
    if width <= 0 or height <= 0:
        raise ValueError(f"invalid video dimensions {width}x{height}")
    if profile == "final" and [width, height] != CONFIG["resolution"]:
        raise ValueError(
            f"final dimensions {width}x{height} do not match "
            f"{CONFIG['resolution'][0]}x{CONFIG['resolution'][1]}"
        )

    frame_rate_text = video.get("avg_frame_rate") or video.get("r_frame_rate")
    try:
        frame_rate = Fraction(str(frame_rate_text))
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(f"invalid frame rate {frame_rate_text!r}") from error
    if frame_rate != Fraction(int(CONFIG["frame_rate"]), 1):
        raise ValueError(f"unexpected frame rate {frame_rate}")
    if video.get("codec_name") != "h264":
        raise ValueError(f"unexpected video codec {video.get('codec_name')!r}")
    if audio.get("codec_name") != "aac":
        raise ValueError(f"unexpected audio codec {audio.get('codec_name')!r}")
    if int(audio.get("channels", 0)) != 2:
        raise ValueError(f"unexpected audio channel count {audio.get('channels')!r}")
    if int(audio.get("sample_rate", 0)) != 48_000:
        raise ValueError(f"unexpected audio sample rate {audio.get('sample_rate')!r}")

    return {
        "duration_seconds": duration,
        "width": width,
        "height": height,
        "frame_rate": str(frame_rate),
        "video_codec": video["codec_name"],
        "audio_codec": audio["codec_name"],
        "audio_channels": int(audio["channels"]),
        "audio_sample_rate": int(audio["sample_rate"]),
    }


def validate_soundtrack(metadata: dict[str, Any], soundtrack: Path) -> dict[str, Any]:
    if metadata.get("sha256") != sha256(soundtrack):
        raise ValueError("soundtrack hash does not match its metadata")
    peak = _finite_float(metadata.get("peak_dbfs"), "soundtrack peak")
    if peak >= MAX_PEAK_DBFS:
        raise ValueError(f"soundtrack peak {peak:.2f} dBFS violates the ceiling")
    duration = _finite_float(metadata.get("duration_seconds"), "soundtrack duration")
    expected_duration = float(CONFIG["duration_seconds"])
    if abs(duration - expected_duration) > MAX_DURATION_DRIFT_SECONDS:
        raise ValueError("soundtrack duration drifted from the picture lock")
    if int(metadata.get("sample_rate", 0)) != 48_000 or int(metadata.get("channels", 0)) != 2:
        raise ValueError("soundtrack metadata is not 48 kHz stereo")
    return {
        "duration_seconds": duration,
        "peak_dbfs": peak,
        "sha256": metadata["sha256"],
        "sample_rate": int(metadata["sample_rate"]),
        "channels": int(metadata["channels"]),
    }


def build_receipt(
    video_path: Path,
    soundtrack_path: Path,
    soundtrack_metadata_path: Path,
    probe: dict[str, Any],
    profile: str,
    artifact_name: str | None = None,
) -> dict[str, Any]:
    media = validate_probe(probe, profile)
    soundtrack_metadata = json.loads(
        soundtrack_metadata_path.read_text(encoding="utf-8")
    )
    soundtrack = validate_soundtrack(soundtrack_metadata, soundtrack_path)
    if abs(media["duration_seconds"] - soundtrack["duration_seconds"]) > MAX_AUDIO_VIDEO_DRIFT_SECONDS:
        raise ValueError("audio and muxed-video durations do not match")

    head = git_head()
    assets = source_asset_hashes(head)
    return {
        "schema": "formalslt-stitched-lil-media-receipt-v1",
        "profile": profile,
        "render_source_commit": head,
        "render_source_state": "tracked source assets identical to render_source_commit",
        "theorem_source_commit": FACTS["commit"],
        "source_assets": assets,
        "video": {
            "file": artifact_name or video_path.name,
            "bytes": video_path.stat().st_size,
            "sha256": sha256(video_path),
            **media,
        },
        "soundtrack": {
            "file": soundtrack_path.name,
            **soundtrack,
        },
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--video", type=Path, required=True)
    parser.add_argument("--soundtrack", type=Path, required=True)
    parser.add_argument("--soundtrack-metadata", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profile", choices=("proof", "final"), required=True)
    parser.add_argument(
        "--artifact-name",
        help="final published filename when verifying a temporary candidate",
    )
    parser.add_argument("--ffprobe", default="ffprobe")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    for path in (args.video, args.soundtrack, args.soundtrack_metadata):
        if not path.is_file():
            raise SystemExit(f"missing render artifact: {path}")
    receipt = build_receipt(
        args.video,
        args.soundtrack,
        args.soundtrack_metadata,
        ffprobe(args.video, args.ffprobe),
        args.profile,
        args.artifact_name,
    )
    write_json(args.output, receipt)
    print(args.output)


if __name__ == "__main__":
    main()
