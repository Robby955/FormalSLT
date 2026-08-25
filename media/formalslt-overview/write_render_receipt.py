#!/usr/bin/env python3
"""Write a deterministic receipt for the reviewed overview-film assets."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MEDIA_ROOT = Path(__file__).resolve().parent
DEFAULT_OUTPUT = MEDIA_ROOT / "render-receipt.json"
DEFAULT_ASSET_ROOT = MEDIA_ROOT / "delivery"

SOURCE_PATHS = (
    MEDIA_ROOT / "TRANSCRIPT.md",
    MEDIA_ROOT / "compose_soundtrack.py",
    MEDIA_ROOT / "extract_facts.py",
    MEDIA_ROOT / "facts.json",
    MEDIA_ROOT / "formalslt_overview.py",
    MEDIA_ROOT / "manim.cfg",
    MEDIA_ROOT / "manim-social.cfg",
    MEDIA_ROOT / "render.sh",
    MEDIA_ROOT / "requirements.txt",
    MEDIA_ROOT / "test_compose_soundtrack.py",
    MEDIA_ROOT / "test_formalslt_overview_source.py",
    MEDIA_ROOT / "write_render_receipt.py",
    MEDIA_ROOT / "delivery/formalslt-overview.vtt",
)

ASSET_SPECS = (
    (
        "main",
        "formalslt-overview.mp4",
        "media/formalslt-overview/delivery/formalslt-overview.mp4",
        (1920, 1080),
    ),
    (
        "social",
        "formalslt-overview-social.mp4",
        "media/formalslt-overview/delivery/formalslt-overview-social.mp4",
        (1080, 1350),
    ),
    (
        "poster",
        "formalslt-overview-poster.jpg",
        "media/formalslt-overview/delivery/formalslt-overview-poster.jpg",
        (1200, 675),
    ),
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def version_line(*command: str) -> str:
    output = subprocess.run(
        command,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    ).stdout
    return output.splitlines()[0].strip()


def soundtrack_plan(cut: str) -> dict[str, object]:
    output = subprocess.run(
        [
            sys.executable,
            str(MEDIA_ROOT / "compose_soundtrack.py"),
            "--describe",
            cut,
        ],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout
    payload = json.loads(output)
    return {
        "reference_duration_seconds": payload["reference_duration_seconds"],
        "sample_rate": payload["sample_rate"],
        "swells": payload["swells"],
        "accents": payload["accents"],
    }


def loudness_metadata(role: str, path: Path, ffmpeg_bin: str) -> dict[str, float]:
    measured = subprocess.run(
        [
            ffmpeg_bin,
            "-hide_banner",
            "-nostats",
            "-i",
            str(path),
            "-filter_complex",
            "ebur128=peak=true",
            "-f",
            "null",
            "-",
        ],
        check=True,
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    ).stderr
    patterns = {
        "integrated_lufs": r"Integrated loudness:\s+I:\s+(-?\d+(?:\.\d+)?) LUFS",
        "loudness_range_lu": r"Loudness range:\s+LRA:\s+(-?\d+(?:\.\d+)?) LU",
        "true_peak_dbfs": r"True peak:\s+Peak:\s+(-?\d+(?:\.\d+)?) dBFS",
    }
    values: dict[str, float] = {}
    for name, pattern in patterns.items():
        matches = re.findall(pattern, measured, flags=re.MULTILINE)
        if not matches:
            raise SystemExit(f"could not parse {name} for {role}")
        values[name] = float(matches[-1])

    integrated_low = -23.5 if role == "main" else -24.0
    if not integrated_low <= values["integrated_lufs"] <= -21.0:
        raise SystemExit(
            f"{role} soundtrack loudness {values['integrated_lufs']} LUFS leaves "
            f"the reviewed [{integrated_low}, -21.0] LUFS range"
        )
    # A flat procedural bed can hit integrated loudness while still sounding
    # inert. Gate meaningful dynamic range in both the long and social cuts.
    lra_low, lra_high = ((6.0, 10.0) if role == "main" else (5.0, 9.0))
    if not lra_low <= values["loudness_range_lu"] <= lra_high:
        raise SystemExit(
            f"{role} soundtrack LRA {values['loudness_range_lu']} leaves the "
            f"reviewed [{lra_low}, {lra_high}] LU range"
        )
    if values["true_peak_dbfs"] > -3.0:
        raise SystemExit(
            f"{role} soundtrack true peak {values['true_peak_dbfs']} dBFS exceeds -3 dBFS"
        )
    return values


def media_metadata(
    role: str,
    path: Path,
    receipt_path: str,
    expected_size: tuple[int, int],
    ffprobe_bin: str,
    ffmpeg_bin: str,
) -> dict[str, object]:
    probe = subprocess.run(
        [
            ffprobe_bin,
            "-v",
            "error",
            "-show_entries",
            (
                "format=duration,size:"
                "stream=codec_type,codec_name,width,height,r_frame_rate,pix_fmt,"
                "sample_rate,channels,channel_layout"
            ),
            "-of",
            "json",
            str(path),
        ],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    payload = json.loads(probe.stdout)
    streams = payload.get("streams", [])
    video_streams = [
        stream for stream in streams if stream.get("codec_type") == "video"
    ]
    audio_streams = [
        stream for stream in streams if stream.get("codec_type") == "audio"
    ]
    if len(video_streams) != 1:
        raise SystemExit(f"{role} must contain exactly one video stream")
    video = video_streams[0]
    fmt = payload.get("format", {})
    actual_size = (video["width"], video["height"])
    if actual_size != expected_size:
        raise SystemExit(
            f"unexpected {role} dimensions: {actual_size}, expected {expected_size}"
        )
    if role in {"main", "social"}:
        if video["codec_name"] != "h264" or video.get("pix_fmt") != "yuv420p":
            raise SystemExit(
                f"{role} must be mobile H.264 yuv420p, got "
                f"{video['codec_name']} {video.get('pix_fmt')}"
            )
        if video.get("r_frame_rate") != "30/1":
            raise SystemExit(
                f"{role} must be 30 fps, got {video.get('r_frame_rate')}"
            )
    if role in {"main", "social"}:
        if len(audio_streams) != 1:
            raise SystemExit(f"{role} must contain exactly one AAC soundtrack")
        audio = audio_streams[0]
        if (
            audio.get("codec_name") != "aac"
            or audio.get("sample_rate") != "48000"
            or audio.get("channels") != 2
        ):
            raise SystemExit(
                f"{role} soundtrack must be stereo 48 kHz AAC, got "
                f"{audio.get('codec_name')} {audio.get('sample_rate')} Hz "
                f"{audio.get('channels')} channels"
            )
    elif audio_streams:
        raise SystemExit(f"{role} poster must not contain an audio stream")

    metadata: dict[str, object] = {
        "role": role,
        "path": receipt_path,
        "sha256": sha256(path),
        "bytes": path.stat().st_size,
        "codec": video["codec_name"],
        "width": video["width"],
        "height": video["height"],
    }
    for key in ("r_frame_rate", "pix_fmt"):
        if key in video:
            metadata[key] = video[key]
    if "duration" in fmt:
        metadata["duration_seconds"] = fmt["duration"]
    if role in {"main", "social"}:
        audio = audio_streams[0]
        metadata["audio"] = {
            "codec": audio["codec_name"],
            "sample_rate": audio["sample_rate"],
            "channels": audio["channels"],
            "channel_layout": audio.get("channel_layout"),
            "loudness": loudness_metadata(role, path, ffmpeg_bin),
        }
    return metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--asset-root",
        type=Path,
        default=DEFAULT_ASSET_ROOT,
        help="directory containing the three rendered delivery assets",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="receipt path (may be inside a transactional staging directory)",
    )
    parser.add_argument(
        "--manim-bin",
        default="manim",
        help="resolved Manim executable used for the render",
    )
    parser.add_argument(
        "--ffmpeg-bin",
        default="ffmpeg",
        help="resolved FFmpeg executable used for the delivery encodes",
    )
    parser.add_argument(
        "--ffprobe-bin",
        default="ffprobe",
        help="resolved FFprobe executable used to validate the delivery encodes",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    asset_root = args.asset_root.resolve()
    output = args.output.resolve()
    assets = tuple(
        (role, asset_root / filename, receipt_path, expected_size)
        for role, filename, receipt_path, expected_size in ASSET_SPECS
    )
    asset_paths = tuple(path for _role, path, _receipt_path, _size in assets)
    for path in (*SOURCE_PATHS, *asset_paths):
        if not path.is_file():
            raise SystemExit(f"missing render input or output: {path}")

    facts = json.loads((MEDIA_ROOT / "facts.json").read_text(encoding="utf-8"))
    receipt = {
        "schema": "formalslt-overview-render-receipt-v4",
        "fact_commit": facts["commit"],
        "source": {
            str(path.relative_to(ROOT)): {
                "sha256": sha256(path),
                "bytes": path.stat().st_size,
            }
            for path in SOURCE_PATHS
        },
        "assets": [
            media_metadata(
                role,
                path,
                receipt_path,
                expected_size,
                args.ffprobe_bin,
                args.ffmpeg_bin,
            )
            for role, path, receipt_path, expected_size in assets
        ],
        "soundtrack": {
            "id": version_line(
                sys.executable,
                str(MEDIA_ROOT / "compose_soundtrack.py"),
                "--version",
            ),
            "source": "media/formalslt-overview/compose_soundtrack.py",
            "generation": (
                "deterministic original synthesis; 80 Hz high-pass and "
                "EBU R128 delivery normalization"
            ),
            "third_party_audio": False,
            "license": "MIT",
            "cut_plans": {
                cut: soundtrack_plan(cut) for cut in ("main", "social")
            },
        },
        "renderer": {
            "python": platform.python_version(),
            "manim": version_line(args.manim_bin, "--version"),
            "ffmpeg": version_line(args.ffmpeg_bin, "-version"),
            "ffprobe": version_line(args.ffprobe_bin, "-version"),
            "display_font": "Avenir Next",
            "code_font": "Menlo",
        },
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    try:
        display_path = output.relative_to(ROOT)
    except ValueError:
        display_path = output
    print(f"wrote {display_path}")


if __name__ == "__main__":
    main()
