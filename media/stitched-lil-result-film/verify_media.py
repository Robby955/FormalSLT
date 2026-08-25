#!/usr/bin/env python3
"""Verify a rendered stitched-LIL film and write a source-bound receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any


PACKAGE_DIR = Path(__file__).resolve().parent
ROOT = PACKAGE_DIR.parents[1]
CONFIG = json.loads((PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8"))
FACTS = json.loads((PACKAGE_DIR / "facts.json").read_text(encoding="utf-8"))
CLAIMS = json.loads((PACKAGE_DIR / "claim-receipt.json").read_text(encoding="utf-8"))

MAX_DURATION_DRIFT_SECONDS = 0.50
MAX_AUDIO_VIDEO_DRIFT_SECONDS = 0.10
MAX_SCORE_PEAK_DBFS = -3.0
MIN_MUXED_INTEGRATED_LUFS = -36.0
MAX_MUXED_INTEGRATED_LUFS = -16.0
MAX_MUXED_TRUE_PEAK_DBFS = -2.0
MAX_MUXED_LRA_LU = 20.0
BUILT_IN_SOUNDTRACK_ID = "formalslt-stitched-lil-sparse-score-v2"
EXTERNAL_SOUNDTRACK_ID = "formalslt-stitched-lil-external-master-v1"
EXTERNAL_PROVENANCE_SCHEMA = "formalslt-external-soundtrack-provenance-v1"
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")

SOURCE_ASSETS = (
    ".gitignore",
    "DELIVERY.md",
    "README.md",
    "SOUNDTRACK.md",
    "STORYBOARD.md",
    "TRANSCRIPT.md",
    "TRANSCRIPT.template.md",
    "TRANSCRIPT-SOCIAL.md",
    "TRANSCRIPT-SOCIAL.template.md",
    "boundary_model.py",
    "captions-main.vtt",
    "captions-social.vtt",
    "claim-receipt.json",
    "compose_soundtrack.py",
    "extract_facts.py",
    "facts.json",
    "film_config.json",
    "manim.cfg",
    "manim-social.cfg",
    "render.sh",
    "requirements.txt",
    "stage_delivery.py",
    "stitched_lil_result.py",
    "test_boundary_model.py",
    "test_compose_soundtrack.py",
    "test_package.py",
    "test_stage_delivery.py",
    "test_verify_media.py",
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


def composition_contract(composition: str) -> dict[str, Any]:
    if composition == "main":
        return {
            "duration_seconds": float(CONFIG["duration_seconds"]),
            "resolution": list(CONFIG["resolution"]),
            "frame": list(CONFIG["frame"]),
        }
    if composition == "social":
        return {
            "duration_seconds": float(CONFIG["social"]["duration_seconds"]),
            "resolution": list(CONFIG["social"]["resolution"]),
            "frame": list(CONFIG["social"]["frame"]),
        }
    raise ValueError(f"unknown composition: {composition}")


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


def ffmpeg_loudness(path: Path, executable: str) -> dict[str, Any]:
    completed = subprocess.run(
        [
            executable,
            "-hide_banner",
            "-nostats",
            "-i",
            str(path),
            "-map",
            "0:a:0",
            "-af",
            "loudnorm=I=-22:LRA=7:TP=-3.5:print_format=json",
            "-f",
            "null",
            "-",
        ],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    matches = re.findall(r"\{\s*\"input_i\"[\s\S]*?\}", completed.stderr)
    if len(matches) != 1:
        raise ValueError(f"expected one loudness JSON object, found {len(matches)}")
    return json.loads(matches[0])


def _one_stream(probe: dict[str, Any], codec_type: str) -> dict[str, Any]:
    streams = [
        stream
        for stream in probe.get("streams", [])
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


def validate_probe(
    probe: dict[str, Any],
    quality: str,
    composition: str,
) -> dict[str, Any]:
    contract = composition_contract(composition)
    video = _one_stream(probe, "video")
    audio = _one_stream(probe, "audio")
    duration = _finite_float(probe.get("format", {}).get("duration"), "duration")
    expected_duration = contract["duration_seconds"]
    if abs(duration - expected_duration) > MAX_DURATION_DRIFT_SECONDS:
        raise ValueError(
            f"movie duration {duration:.3f}s drifted from {expected_duration:.3f}s"
        )

    width = int(video.get("width", 0))
    height = int(video.get("height", 0))
    if width <= 0 or height <= 0:
        raise ValueError(f"invalid video dimensions {width}x{height}")
    expected_width, expected_height = contract["resolution"]
    if quality == "final" and [width, height] != [expected_width, expected_height]:
        raise ValueError(
            f"final dimensions {width}x{height} do not match "
            f"{expected_width}x{expected_height}"
        )
    expected_aspect = expected_width / expected_height
    if abs(width / height - expected_aspect) > 0.01:
        raise ValueError(
            f"{composition} dimensions {width}x{height} have the wrong aspect ratio"
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


def validate_loudness(measurement: dict[str, Any]) -> dict[str, float]:
    integrated = _finite_float(measurement.get("input_i"), "integrated loudness")
    true_peak = _finite_float(measurement.get("input_tp"), "true peak")
    loudness_range = _finite_float(measurement.get("input_lra"), "loudness range")
    threshold = _finite_float(measurement.get("input_thresh"), "loudness threshold")
    if not MIN_MUXED_INTEGRATED_LUFS <= integrated <= MAX_MUXED_INTEGRATED_LUFS:
        raise ValueError(f"integrated loudness {integrated:.2f} LUFS is outside the film range")
    if true_peak > MAX_MUXED_TRUE_PEAK_DBFS:
        raise ValueError(f"muxed true peak {true_peak:.2f} dBFS violates the ceiling")
    if not 0.0 <= loudness_range <= MAX_MUXED_LRA_LU:
        raise ValueError(f"loudness range {loudness_range:.2f} LU is invalid")
    return {
        "integrated_lufs": integrated,
        "true_peak_dbfs": true_peak,
        "loudness_range_lu": loudness_range,
        "measurement_threshold_lufs": threshold,
    }


def _soundtrack_common(
    metadata: dict[str, Any],
    soundtrack: Path,
    composition: str,
) -> tuple[float, str]:
    derived_hash = sha256(soundtrack)
    if metadata.get("sha256") != derived_hash:
        raise ValueError("soundtrack hash does not match its metadata")
    if metadata.get("cut") != composition:
        raise ValueError("soundtrack cut does not match the composition")
    contract = composition_contract(composition)
    duration = _finite_float(metadata.get("duration_seconds"), "soundtrack duration")
    if abs(duration - contract["duration_seconds"]) > MAX_DURATION_DRIFT_SECONDS:
        raise ValueError("soundtrack duration drifted from the picture lock")
    if int(metadata.get("sample_rate", 0)) != 48_000 or int(metadata.get("channels", 0)) != 2:
        raise ValueError("soundtrack metadata is not 48 kHz stereo")
    return duration, derived_hash


def _sha_field(value: Any, label: str) -> str:
    text = str(value)
    if SHA256_PATTERN.fullmatch(text) is None:
        raise ValueError(f"invalid {label} SHA-256")
    return text


def _measurement(metadata: Any, label: str) -> dict[str, float]:
    if not isinstance(metadata, dict):
        raise ValueError(f"missing {label} measurement")
    fields = (
        "input_i",
        "input_tp",
        "input_lra",
        "input_thresh",
        "output_i",
        "output_tp",
        "output_lra",
        "output_thresh",
        "target_offset",
    )
    return {field: _finite_float(metadata.get(field), f"{label} {field}") for field in fields}


def _validate_built_in_soundtrack(
    metadata: dict[str, Any],
    duration: float,
    derived_hash: str,
) -> dict[str, Any]:
    if metadata.get("soundtrack_id") != BUILT_IN_SOUNDTRACK_ID:
        raise ValueError("unexpected built-in soundtrack identity")
    if metadata.get("third_party_audio") is not False:
        raise ValueError("built-in soundtrack must contain no third-party audio")
    peak = _finite_float(metadata.get("peak_dbfs"), "soundtrack peak")
    if peak >= MAX_SCORE_PEAK_DBFS:
        raise ValueError(f"soundtrack peak {peak:.2f} dBFS violates the ceiling")
    duty = _finite_float(metadata.get("active_duty_ratio"), "active duty ratio")
    if not 0.0 < duty < 0.75:
        raise ValueError("soundtrack lacks the required negative space")
    if len(metadata.get("accents", [])) != 3:
        raise ValueError("soundtrack transition-accent count drifted")
    return {
        "duration_seconds": duration,
        "peak_dbfs": peak,
        "rms_dbfs": _finite_float(metadata.get("rms_dbfs"), "soundtrack RMS"),
        "active_duty_ratio": duty,
        "sha256": derived_hash,
        "sample_rate": int(metadata["sample_rate"]),
        "channels": int(metadata["channels"]),
        "soundtrack_id": metadata["soundtrack_id"],
        "soundtrack_mode": "built_in",
        "third_party_audio": False,
    }


def _validate_external_soundtrack(
    metadata: dict[str, Any],
    duration: float,
    derived_hash: str,
) -> dict[str, Any]:
    if metadata.get("soundtrack_id") != EXTERNAL_SOUNDTRACK_ID:
        raise ValueError("unexpected external soundtrack identity")
    if metadata.get("third_party_audio") is not True:
        raise ValueError("external soundtrack must identify third-party audio")
    raw_master = metadata.get("raw_master")
    provenance = metadata.get("provenance")
    derivation = metadata.get("derivation")
    if not isinstance(raw_master, dict) or not isinstance(provenance, dict):
        raise ValueError("external soundtrack is missing master or provenance data")
    if not isinstance(derivation, dict):
        raise ValueError("external soundtrack is missing derivation data")
    master_hash = _sha_field(raw_master.get("sha256"), "raw master")
    if provenance.get("schema") != EXTERNAL_PROVENANCE_SCHEMA:
        raise ValueError("unexpected external soundtrack provenance schema")
    provenance_hash = _sha_field(provenance.get("sha256"), "provenance")
    if provenance.get("master_sha256") != master_hash:
        raise ValueError("external soundtrack provenance binds a different master")
    if provenance.get("source_service") != "Suno":
        raise ValueError("external soundtrack provenance is not from Suno")
    if provenance.get("commercial_use_authorized") is not True:
        raise ValueError("external soundtrack does not authorize commercial use")
    if provenance.get("rights_attested") is not True:
        raise ValueError("external soundtrack rights were not attested")
    analysis_filter = str(derivation.get("analysis_filter", ""))
    render_filter = str(derivation.get("render_filter", ""))
    if hashlib.sha256(analysis_filter.encode("utf-8")).hexdigest() != _sha_field(
        derivation.get("analysis_filter_sha256"),
        "analysis filter",
    ):
        raise ValueError("external soundtrack analysis-filter hash drifted")
    if hashlib.sha256(render_filter.encode("utf-8")).hexdigest() != _sha_field(
        derivation.get("render_filter_sha256"),
        "render filter",
    ):
        raise ValueError("external soundtrack render-filter hash drifted")
    tool_receipts: dict[str, dict[str, str]] = {}
    for label in ("ffmpeg", "ffprobe"):
        tool = derivation.get(label)
        if not isinstance(tool, dict):
            raise ValueError(f"external soundtrack is missing {label} identity")
        executable = Path(str(tool.get("path", "")))
        expected_hash = _sha_field(tool.get("sha256"), label)
        if not executable.is_absolute() or not executable.is_file():
            raise ValueError(f"external soundtrack {label} path is not an absolute file")
        if sha256(executable) != expected_hash:
            raise ValueError(f"external soundtrack {label} binary hash drifted")
        version = str(tool.get("version", ""))
        if not version:
            raise ValueError(f"external soundtrack {label} version is missing")
        tool_receipts[label] = {
            "path": str(executable),
            "sha256": expected_hash,
            "version": version,
        }
    pass_one = _measurement(derivation.get("pass_one_measurement"), "pass one")
    derived_measurement = _measurement(
        derivation.get("derived_measurement"),
        "derived soundtrack",
    )
    integrated = derived_measurement["input_i"]
    true_peak = derived_measurement["input_tp"]
    if not -24.0 <= integrated <= -20.0:
        raise ValueError(f"external soundtrack loudness {integrated:.2f} LUFS missed its target")
    if true_peak > -3.0:
        raise ValueError(f"external soundtrack true peak {true_peak:.2f} dBFS violates the ceiling")
    return {
        "duration_seconds": duration,
        "peak_dbfs": true_peak,
        "integrated_lufs": integrated,
        "sha256": derived_hash,
        "sample_rate": int(metadata["sample_rate"]),
        "channels": int(metadata["channels"]),
        "soundtrack_id": metadata["soundtrack_id"],
        "soundtrack_mode": "external_master",
        "third_party_audio": True,
        "raw_master": {
            "file": str(raw_master.get("file", "")),
            "bytes": int(raw_master.get("bytes", -1)),
            "sha256": master_hash,
            "duration_seconds": _finite_float(
                raw_master.get("duration_seconds"),
                "raw master duration",
            ),
        },
        "provenance": {
            "file": str(provenance.get("file", "")),
            "bytes": int(provenance.get("bytes", -1)),
            "sha256": provenance_hash,
            "schema": provenance["schema"],
            "source_service": provenance["source_service"],
            "source_url": str(provenance.get("source_url", "")),
            "track_title": str(provenance.get("track_title", "")),
            "generated_at_utc": str(provenance.get("generated_at_utc", "")),
            "license_basis": str(provenance.get("license_basis", "")),
            "commercial_use_authorized": True,
            "rights_attested": True,
            "rights_attested_by": str(provenance.get("rights_attested_by", "")),
            "rights_attested_at_utc": str(provenance.get("rights_attested_at_utc", "")),
            "master_sha256": master_hash,
        },
        "derivation": {
            "trim_start_seconds": _finite_float(
                derivation.get("trim_start_seconds"),
                "trim start",
            ),
            "trim_duration_seconds": _finite_float(
                derivation.get("trim_duration_seconds"),
                "trim duration",
            ),
            "fade_in_seconds": _finite_float(derivation.get("fade_in_seconds"), "fade in"),
            "fade_out_seconds": _finite_float(derivation.get("fade_out_seconds"), "fade out"),
            "analysis_filter_sha256": derivation["analysis_filter_sha256"],
            "render_filter_sha256": derivation["render_filter_sha256"],
            **tool_receipts,
            "pass_one_measurement": pass_one,
            "derived_measurement": derived_measurement,
        },
    }


def validate_soundtrack(
    metadata: dict[str, Any],
    soundtrack: Path,
    composition: str,
) -> dict[str, Any]:
    duration, derived_hash = _soundtrack_common(metadata, soundtrack, composition)
    mode = metadata.get("soundtrack_mode")
    if mode is None and metadata.get("soundtrack_id") == BUILT_IN_SOUNDTRACK_ID:
        mode = "built_in"
    if mode == "built_in":
        return _validate_built_in_soundtrack(metadata, duration, derived_hash)
    if mode == "external_master":
        return _validate_external_soundtrack(metadata, duration, derived_hash)
    raise ValueError(f"unexpected soundtrack mode {mode!r}")


def build_receipt(
    video_path: Path,
    soundtrack_path: Path,
    soundtrack_metadata_path: Path,
    probe: dict[str, Any],
    loudness_measurement: dict[str, Any],
    quality: str,
    composition: str,
    artifact_name: str | None = None,
) -> dict[str, Any]:
    if not (
        FACTS["commit"]
        == CLAIMS["theorem_source_commit"]
        == CONFIG["source_commit"]
    ):
        raise ValueError("fact, claim, and film receipts bind different theorem commits")
    media = validate_probe(probe, quality, composition)
    loudness = validate_loudness(loudness_measurement)
    soundtrack_metadata = json.loads(soundtrack_metadata_path.read_text(encoding="utf-8"))
    soundtrack = validate_soundtrack(soundtrack_metadata, soundtrack_path, composition)
    if abs(media["duration_seconds"] - soundtrack["duration_seconds"]) > MAX_AUDIO_VIDEO_DRIFT_SECONDS:
        raise ValueError("audio and muxed-video durations do not match")

    head = git_head()
    assets = source_asset_hashes(head)
    return {
        "schema": "formalslt-stitched-lil-media-receipt-v2",
        "quality": quality,
        "composition": composition,
        "render_source_commit": head,
        "render_source_state": "tracked source assets identical to render_source_commit",
        "theorem_source_commit": FACTS["commit"],
        "theorem_blob_oid": CLAIMS["theorem_blob_oid"],
        "claim_receipt_sha256": sha256(PACKAGE_DIR / "claim-receipt.json"),
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
        "muxed_audio_measurement": loudness,
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
    parser.add_argument("--quality", choices=("proof", "final"), required=True)
    parser.add_argument("--composition", choices=("main", "social"), required=True)
    parser.add_argument(
        "--artifact-name",
        help="final published filename when verifying a temporary candidate",
    )
    parser.add_argument("--ffprobe", default="ffprobe")
    parser.add_argument("--ffmpeg", default="ffmpeg")
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
        ffmpeg_loudness(args.video, args.ffmpeg),
        args.quality,
        args.composition,
        args.artifact_name,
    )
    write_json(args.output, receipt)
    print(args.output)


if __name__ == "__main__":
    main()
