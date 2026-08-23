#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
MODE="${1:-proof}"
SCENE="FormalSLTOverview"
SOURCE="media/formalslt-overview/formalslt_overview.py"
OUT_DIR="media/formalslt-overview/out"

if [[ -z "${MANIM_BIN:-}" ]]; then
  MANIM_BIN="$(command -v manim || true)"
fi
if [[ -z "$MANIM_BIN" && -x /Library/Frameworks/Python.framework/Versions/3.13/bin/manim ]]; then
  MANIM_BIN=/Library/Frameworks/Python.framework/Versions/3.13/bin/manim
fi
if [[ -z "$MANIM_BIN" ]]; then
  echo "manim was not found; install media/formalslt-overview/requirements.txt" >&2
  exit 1
fi

if [[ -z "${FFMPEG_BIN:-}" ]]; then
  FFMPEG_BIN="$(command -v ffmpeg || true)"
fi
if [[ -z "$FFMPEG_BIN" ]]; then
  echo "ffmpeg was not found" >&2
  exit 1
fi

cd "$ROOT"
python3 media/formalslt-overview/extract_facts.py
mkdir -p "$OUT_DIR"

case "$MODE" in
  proof)
    QUALITY="-ql"
    OUTPUT="formalslt-overview-proof.mp4"
    ;;
  final)
    QUALITY="-qh"
    OUTPUT="formalslt-overview-1080p.mp4"
    ;;
  site)
    QUALITY="-qh"
    OUTPUT="formalslt-overview-1080p.mp4"
    ;;
  *)
    echo "usage: $0 [proof|final|site]" >&2
    exit 2
    ;;
esac

"$MANIM_BIN" --config_file media/formalslt-overview/manim.cfg \
  "$QUALITY" --fps 30 --format mp4 --output_file "$OUTPUT" \
  "$SOURCE" "$SCENE"

RENDERED="$(find media/formalslt-overview/media/videos -type f -name "$OUTPUT" -print -quit)"
if [[ -z "$RENDERED" ]]; then
  echo "render completed without the expected output: $OUTPUT" >&2
  exit 1
fi

"$FFMPEG_BIN" -hide_banner -loglevel error -y -i "$RENDERED" \
  -map 0:v:0 -c:v copy -an "$OUT_DIR/$OUTPUT"

if [[ "$MODE" == "site" ]]; then
  "$FFMPEG_BIN" -hide_banner -loglevel error -y -i "$OUT_DIR/$OUTPUT" \
    -map 0:v:0 -c:v copy -an -movflags +faststart \
    docs/site/assets/formalslt-overview.mp4
  "$FFMPEG_BIN" -hide_banner -loglevel error -y -ss 39 \
    -i "$OUT_DIR/$OUTPUT" -frames:v 1 -vf scale=1200:675 -q:v 2 \
    docs/site/assets/formalslt-overview-poster.jpg
fi

echo "$OUT_DIR/$OUTPUT"
