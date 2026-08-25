#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
PACKAGE="media/stitched-lil-result-film"
MODE="${1:-validate}"
SOURCE="$PACKAGE/stitched_lil_result.py"
COMPOSER="$PACKAGE/compose_soundtrack.py"
VERIFIER="$PACKAGE/verify_media.py"
STAGER="$PACKAGE/stage_delivery.py"
OUT_DIR="$PACKAGE/out"
ACTIVE_TEMP_DIR=""
ACTIVE_CANDIDATE_VIDEO=""
ACTIVE_CANDIDATE_RECEIPT=""

cd "$ROOT"

cleanup_temp_tree() {
  local target="$1"
  if [[ -z "$target" ]]; then
    return
  fi
  case "$target" in
    "$OUT_DIR"/render.*)
      if [[ -d "$target" ]]; then
        find "$target" -depth -delete
      fi
      ;;
    *)
      echo "refusing to clean unexpected render path: $target" >&2
      return 1
      ;;
  esac
}

cleanup_active_temp() {
  if [[ -n "$ACTIVE_TEMP_DIR" ]]; then
    cleanup_temp_tree "$ACTIVE_TEMP_DIR"
  fi
  if [[ -n "$ACTIVE_CANDIDATE_VIDEO" ]]; then
    rm -f -- "$ACTIVE_CANDIDATE_VIDEO"
  fi
  if [[ -n "$ACTIVE_CANDIDATE_RECEIPT" ]]; then
    rm -f -- "$ACTIVE_CANDIDATE_RECEIPT"
  fi
}

trap cleanup_active_temp EXIT

validate_source() {
  python3 "$PACKAGE/extract_facts.py"
  python3 -m unittest discover -s "$PACKAGE" -p 'test_*.py'
  bash -n "$PACKAGE/render.sh"
}

find_renderer() {
  if [[ -z "${MANIM_BIN:-}" ]]; then
    MANIM_BIN="$(command -v manim || true)"
  fi
  if [[ -z "$MANIM_BIN" && -x /Library/Frameworks/Python.framework/Versions/3.13/bin/manim ]]; then
    MANIM_BIN=/Library/Frameworks/Python.framework/Versions/3.13/bin/manim
  fi
  if [[ -z "$MANIM_BIN" ]]; then
    echo "manim was not found; install $PACKAGE/requirements.txt in an isolated environment" >&2
    exit 1
  fi
}

find_video_tools() {
  if [[ -z "${FFMPEG_BIN:-}" ]]; then
    FFMPEG_BIN="$(command -v ffmpeg || true)"
  fi
  if [[ -z "${FFPROBE_BIN:-}" ]]; then
    FFPROBE_BIN="$(command -v ffprobe || true)"
  fi
  if [[ -z "$FFMPEG_BIN" || -z "$FFPROBE_BIN" ]]; then
    echo "ffmpeg and ffprobe are required for a movie render" >&2
    exit 1
  fi
}

movie_duration() {
  "$FFPROBE_BIN" -v error -show_entries format=duration \
    -of default=noprint_wrappers=1:nokey=1 "$1"
}

render_movie() {
  local quality="$1"
  local resolution="$2"
  local verification_quality="$3"
  local composition="$4"
  local config_file="$5"
  local scene="$6"
  local output="$7"
  local rendered
  local duration
  local soundtrack="$OUT_DIR/${output%.mp4}-score.wav"
  local soundtrack_metadata="$OUT_DIR/${output%.mp4}-score.json"
  local receipt="$OUT_DIR/${output%.mp4}-receipt.json"
  local candidate_video="$OUT_DIR/.${output%.mp4}-candidate.mp4"
  local candidate_receipt="$OUT_DIR/.${output%.mp4}-candidate-receipt.json"
  local matches

  mkdir -p "$OUT_DIR"
  rm -f -- "$OUT_DIR/$output" "$soundtrack" "$soundtrack_metadata" "$receipt" \
    "$candidate_video" "$candidate_receipt"
  ACTIVE_CANDIDATE_VIDEO="$candidate_video"
  ACTIVE_CANDIDATE_RECEIPT="$candidate_receipt"
  ACTIVE_TEMP_DIR="$(mktemp -d "$OUT_DIR/render.XXXXXX")"
  "$MANIM_BIN" --config_file "$config_file" \
    "$quality" --resolution "$resolution" --fps 30 --format mp4 \
    --media_dir "$ACTIVE_TEMP_DIR/media" \
    --output_file "$output" \
    "$SOURCE" "$scene"
  matches="$(find "$ACTIVE_TEMP_DIR/media/videos" -type f -name "$output" -print)"
  rendered="$(python3 - "$output" "$matches" <<'PY'
import sys

name, payload = sys.argv[1:]
paths = [line for line in payload.splitlines() if line]
if len(paths) != 1:
    raise SystemExit(f"expected exactly one fresh {name} render, found {len(paths)}")
print(paths[0])
PY
)"
  duration="$(movie_duration "$rendered")"
  python3 "$COMPOSER" --cut "$composition" --duration "$duration" \
    --output "$soundtrack" \
    --metadata-output "$soundtrack_metadata"
  "$FFMPEG_BIN" -hide_banner -loglevel error -y \
    -i "$rendered" -i "$soundtrack" \
    -map 0:v:0 -map 1:a:0 \
    -c:v libx264 -preset slow -crf 20 -pix_fmt yuv420p \
    -c:a aac -b:a 192k -ar 48000 -ac 2 \
    -af apad -shortest -movflags +faststart "$candidate_video"
  python3 "$VERIFIER" \
    --video "$candidate_video" \
    --soundtrack "$soundtrack" \
    --soundtrack-metadata "$soundtrack_metadata" \
    --quality "$verification_quality" \
    --composition "$composition" \
    --artifact-name "$output" \
    --ffprobe "$FFPROBE_BIN" \
    --ffmpeg "$FFMPEG_BIN" \
    --output "$candidate_receipt"
  mv -f -- "$candidate_video" "$OUT_DIR/$output"
  mv -f -- "$candidate_receipt" "$receipt"
  ACTIVE_CANDIDATE_VIDEO=""
  ACTIVE_CANDIDATE_RECEIPT=""
  cleanup_temp_tree "$ACTIVE_TEMP_DIR"
  ACTIVE_TEMP_DIR=""
  echo "$OUT_DIR/$output"
  echo "$receipt"
}

render_poster() {
  local composition="$1"
  local resolution="$2"
  local config_file="$3"
  local scene="$4"
  local output="$5"
  local rendered
  local matches

  mkdir -p "$OUT_DIR"
  rm -f -- "$OUT_DIR/$output"
  ACTIVE_TEMP_DIR="$(mktemp -d "$OUT_DIR/render.XXXXXX")"
  "$MANIM_BIN" --config_file "$config_file" \
    -qh --resolution "$resolution" --fps 30 --format png --save_last_frame \
    --media_dir "$ACTIVE_TEMP_DIR/media" --output_file "$output" \
    "$SOURCE" "$scene"
  matches="$(find "$ACTIVE_TEMP_DIR/media/images" -type f -name "$output" -print)"
  rendered="$(python3 - "$output" "$matches" <<'PY'
import sys

name, payload = sys.argv[1:]
paths = [line for line in payload.splitlines() if line]
if len(paths) != 1:
    raise SystemExit(f"expected exactly one fresh {name} render, found {len(paths)}")
print(paths[0])
PY
)"
  cp -- "$rendered" "$OUT_DIR/$output"
  cleanup_temp_tree "$ACTIVE_TEMP_DIR"
  ACTIVE_TEMP_DIR=""
  echo "$OUT_DIR/$output"
}

case "$MODE" in
  validate)
    validate_source
    ;;
  facts)
    python3 "$PACKAGE/extract_facts.py" --print
    ;;
  soundtrack-plan)
    python3 "$COMPOSER" --describe main
    python3 "$COMPOSER" --describe social
    ;;
  proof-main)
    validate_source
    find_renderer
    find_video_tools
    render_movie -ql 854,480 proof main "$PACKAGE/manim.cfg" \
      StitchedLILResultFilm stitched-lil-result-proof.mp4
    ;;
  proof-social)
    validate_source
    find_renderer
    find_video_tools
    render_movie -ql 432,540 proof social "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocial stitched-lil-result-social-proof.mp4
    ;;
  proofs)
    validate_source
    find_renderer
    find_video_tools
    render_movie -ql 854,480 proof main "$PACKAGE/manim.cfg" \
      StitchedLILResultFilm stitched-lil-result-proof.mp4
    render_movie -ql 432,540 proof social "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocial stitched-lil-result-social-proof.mp4
    ;;
  final-main)
    validate_source
    find_renderer
    find_video_tools
    render_movie -qh 1920,1080 final main "$PACKAGE/manim.cfg" \
      StitchedLILResultFilm stitched-lil-result-1920x1080.mp4
    ;;
  final-social)
    validate_source
    find_renderer
    find_video_tools
    render_movie -qh 1080,1350 final social "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocial stitched-lil-result-1080x1350.mp4
    ;;
  finals)
    validate_source
    find_renderer
    find_video_tools
    render_movie -qh 1920,1080 final main "$PACKAGE/manim.cfg" \
      StitchedLILResultFilm stitched-lil-result-1920x1080.mp4
    render_movie -qh 1080,1350 final social "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocial stitched-lil-result-1080x1350.mp4
    ;;
  poster-main)
    validate_source
    find_renderer
    render_poster main 1920,1080 "$PACKAGE/manim.cfg" \
      StitchedLILResultPoster stitched-lil-result-poster-1920x1080.png
    ;;
  poster-social)
    validate_source
    find_renderer
    render_poster social 1080,1350 "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocialPoster stitched-lil-result-poster-1080x1350.png
    ;;
  posters)
    validate_source
    find_renderer
    render_poster main 1920,1080 "$PACKAGE/manim.cfg" \
      StitchedLILResultPoster stitched-lil-result-poster-1920x1080.png
    render_poster social 1080,1350 "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocialPoster stitched-lil-result-poster-1080x1350.png
    ;;
  release)
    validate_source
    find_renderer
    find_video_tools
    render_movie -qh 1920,1080 final main "$PACKAGE/manim.cfg" \
      StitchedLILResultFilm stitched-lil-result-1920x1080.mp4
    render_movie -qh 1080,1350 final social "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocial stitched-lil-result-1080x1350.mp4
    render_poster main 1920,1080 "$PACKAGE/manim.cfg" \
      StitchedLILResultPoster stitched-lil-result-poster-1920x1080.png
    render_poster social 1080,1350 "$PACKAGE/manim-social.cfg" \
      StitchedLILResultSocialPoster stitched-lil-result-poster-1080x1350.png
    ;;
  stage-delivery)
    validate_source
    find_video_tools
    python3 "$STAGER" --ffprobe "$FFPROBE_BIN"
    ;;
  *)
    echo "usage: $0 [validate|facts|soundtrack-plan|proof-main|proof-social|proofs|final-main|final-social|finals|poster-main|poster-social|posters|release|stage-delivery]" >&2
    exit 2
    ;;
esac
