#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
MODE="${1:-proof}"
SOURCE="media/formalslt-overview/formalslt_overview.py"
COMPOSER="media/formalslt-overview/compose_soundtrack.py"
OUT_DIR="media/formalslt-overview/out"
MEDIA_DIR="media/formalslt-overview/media"
SOCIAL_MEDIA_DIR="media/formalslt-overview/media-social"
RELEASE_STAGE=""

cleanup_release_stage() {
  if [[ -n "$RELEASE_STAGE" && -d "$RELEASE_STAGE" ]]; then
    rm -rf -- "$RELEASE_STAGE"
  fi
}

trap cleanup_release_stage EXIT

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

if [[ -z "${FFPROBE_BIN:-}" ]]; then
  FFPROBE_BIN="$(command -v ffprobe || true)"
fi
if [[ -z "$FFPROBE_BIN" ]]; then
  echo "ffprobe was not found" >&2
  exit 1
fi

cd "$ROOT"
python3 media/formalslt-overview/extract_facts.py
mkdir -p "$OUT_DIR"

movie_duration() {
  "$FFPROBE_BIN" -v error -show_entries format=duration \
    -of default=noprint_wrappers=1:nokey=1 "$1"
}

add_soundtrack() {
  local movie="$1"
  local cut="$2"
  local basename="${movie##*/}"
  local stem="${basename%.mp4}"
  local soundtrack="$OUT_DIR/$stem-soundtrack.wav"
  local muxed="$OUT_DIR/$stem-with-audio.mp4"
  local duration

  duration="$(movie_duration "$movie")"
  python3 "$COMPOSER" \
    --cut "$cut" \
    --duration "$duration" \
    --output "$soundtrack"
  "$FFMPEG_BIN" -hide_banner -loglevel error -y \
    -i "$movie" -i "$soundtrack" \
    -map 0:v:0 -map 1:a:0 \
    -c:v copy -c:a aac -b:a 192k -ar 48000 -ac 2 \
    -af "highpass=f=80,loudnorm=I=-22:LRA=7:TP=-3.5,aresample=48000,apad" \
    -shortest -movflags +faststart \
    "$muxed"
  if [[ "$("$FFPROBE_BIN" -v error -select_streams a:0 \
    -show_entries stream=codec_name -of default=noprint_wrappers=1:nokey=1 \
    "$muxed")" != "aac" ]]; then
    echo "soundtrack mux did not produce an AAC stream: $muxed" >&2
    return 1
  fi
  mv -f -- "$muxed" "$movie"
}

render_movie() {
  local scene="$1"
  local quality="$2"
  local resolution="$3"
  local config_file="$4"
  local media_dir="$5"
  local output="$6"
  local cut="$7"

  "$MANIM_BIN" --config_file "$config_file" \
    "$quality" --resolution "$resolution" --fps 30 --format mp4 --output_file "$output" \
    "$SOURCE" "$scene"

  local rendered
  rendered="$(find "$media_dir/videos" -type f -name "$output" -print -quit)"
  if [[ -z "$rendered" ]]; then
    echo "render completed without the expected output: $output" >&2
    exit 1
  fi

  "$FFMPEG_BIN" -hide_banner -loglevel error -y -i "$rendered" \
    -map 0:v:0 -c:v copy -an "$OUT_DIR/$output"
  add_soundtrack "$OUT_DIR/$output" "$cut"
}

render_poster() {
  local output="formalslt-overview-poster.png"
  "$MANIM_BIN" --config_file media/formalslt-overview/manim.cfg \
    -qh --fps 30 --format png --save_last_frame --output_file "$output" \
    "$SOURCE" FormalSLTPoster

  local rendered
  rendered="$(find "$MEDIA_DIR/images" -type f -name "$output" -print -quit)"
  if [[ -z "$rendered" ]]; then
    echo "poster render completed without the expected output: $output" >&2
    exit 1
  fi
  cp "$rendered" "$OUT_DIR/$output"
}

stage_movie() {
  local input="$1"
  local output="$2"
  "$FFMPEG_BIN" -hide_banner -loglevel error -y -i "$input" \
    -map 0:v:0 -map 0:a:0 -c:v libx264 -preset slow -crf 22 \
    -pix_fmt yuv420p -c:a copy -movflags +faststart "$output"
}

publish_release_asset_set() {
  local stage="$1"
  local backup="$stage/previous"
  local names=(
    "formalslt-overview.mp4"
    "formalslt-overview-social.mp4"
    "formalslt-overview-poster.jpg"
    "render-receipt.json"
    "site-formalslt-overview.mp4"
    "site-formalslt-overview-poster.jpg"
    "site-formalslt-overview.vtt"
  )
  local destinations=(
    "media/formalslt-overview/delivery/formalslt-overview.mp4"
    "media/formalslt-overview/delivery/formalslt-overview-social.mp4"
    "media/formalslt-overview/delivery/formalslt-overview-poster.jpg"
    "media/formalslt-overview/render-receipt.json"
    "docs/site/assets/formalslt-overview.mp4"
    "docs/site/assets/formalslt-overview-poster.jpg"
    "docs/site/assets/formalslt-overview.vtt"
  )
  local index
  local rollback_index

  mkdir -p "$backup"
  for index in "${!destinations[@]}"; do
    if [[ -f "${destinations[$index]}" ]]; then
      ln "${destinations[$index]}" "$backup/$index"
    else
      : > "$backup/$index.missing"
    fi
  done

  for index in "${!destinations[@]}"; do
    if ! mv -f -- "$stage/${names[$index]}" "${destinations[$index]}"; then
      for rollback_index in "${!destinations[@]}"; do
        rm -f -- "${destinations[$rollback_index]}"
        if [[ -f "$backup/$rollback_index" ]]; then
          mv -- "$backup/$rollback_index" "${destinations[$rollback_index]}"
        fi
      done
      echo "release asset promotion failed; restored the previous complete set" >&2
      return 1
    fi
  done
}

case "$MODE" in
  proof)
    render_movie FormalSLTOverview -ql 854,480 \
      media/formalslt-overview/manim.cfg "$MEDIA_DIR" \
      formalslt-overview-proof.mp4 main
    echo "$OUT_DIR/formalslt-overview-proof.mp4"
    ;;
  social-proof)
    render_movie FormalSLTSocial -ql 432,540 \
      media/formalslt-overview/manim-social.cfg "$SOCIAL_MEDIA_DIR" \
      formalslt-overview-social-proof.mp4 social
    echo "$OUT_DIR/formalslt-overview-social-proof.mp4"
    ;;
  proofs)
    render_movie FormalSLTOverview -ql 854,480 \
      media/formalslt-overview/manim.cfg "$MEDIA_DIR" \
      formalslt-overview-proof.mp4 main
    render_movie FormalSLTSocial -ql 432,540 \
      media/formalslt-overview/manim-social.cfg "$SOCIAL_MEDIA_DIR" \
      formalslt-overview-social-proof.mp4 social
    echo "$OUT_DIR/formalslt-overview-proof.mp4"
    echo "$OUT_DIR/formalslt-overview-social-proof.mp4"
    ;;
  final)
    render_movie FormalSLTOverview -qh 1920,1080 \
      media/formalslt-overview/manim.cfg "$MEDIA_DIR" \
      formalslt-overview-1080p.mp4 main
    echo "$OUT_DIR/formalslt-overview-1080p.mp4"
    ;;
  social)
    render_movie FormalSLTSocial -qh 1080,1350 \
      media/formalslt-overview/manim-social.cfg "$SOCIAL_MEDIA_DIR" \
      formalslt-overview-social-1080x1350.mp4 social
    echo "$OUT_DIR/formalslt-overview-social-1080x1350.mp4"
    ;;
  poster)
    render_poster
    echo "$OUT_DIR/formalslt-overview-poster.png"
    ;;
  release)
    render_movie FormalSLTOverview -qh 1920,1080 \
      media/formalslt-overview/manim.cfg "$MEDIA_DIR" \
      formalslt-overview-1080p.mp4 main
    render_movie FormalSLTSocial -qh 1080,1350 \
      media/formalslt-overview/manim-social.cfg "$SOCIAL_MEDIA_DIR" \
      formalslt-overview-social-1080x1350.mp4 social
    render_poster
    RELEASE_STAGE="$(mktemp -d "$OUT_DIR/release-stage.XXXXXX")"
    stage_movie \
      "$OUT_DIR/formalslt-overview-1080p.mp4" \
      "$RELEASE_STAGE/formalslt-overview.mp4"
    stage_movie \
      "$OUT_DIR/formalslt-overview-social-1080x1350.mp4" \
      "$RELEASE_STAGE/formalslt-overview-social.mp4"
    "$FFMPEG_BIN" -hide_banner -loglevel error -y \
      -i "$OUT_DIR/formalslt-overview-poster.png" \
      -vf scale=1200:675 -frames:v 1 -q:v 2 \
      "$RELEASE_STAGE/formalslt-overview-poster.jpg"
    python3 media/formalslt-overview/write_render_receipt.py \
      --asset-root "$RELEASE_STAGE" \
      --output "$RELEASE_STAGE/render-receipt.json" \
      --manim-bin "$MANIM_BIN" \
      --ffmpeg-bin "$FFMPEG_BIN" \
      --ffprobe-bin "$FFPROBE_BIN"
    ln "$RELEASE_STAGE/formalslt-overview.mp4" \
      "$RELEASE_STAGE/site-formalslt-overview.mp4"
    ln "$RELEASE_STAGE/formalslt-overview-poster.jpg" \
      "$RELEASE_STAGE/site-formalslt-overview-poster.jpg"
    cp media/formalslt-overview/delivery/formalslt-overview.vtt \
      "$RELEASE_STAGE/site-formalslt-overview.vtt"
    publish_release_asset_set "$RELEASE_STAGE"
    echo "media/formalslt-overview/delivery/formalslt-overview.mp4"
    echo "media/formalslt-overview/delivery/formalslt-overview-social.mp4"
    echo "media/formalslt-overview/delivery/formalslt-overview-poster.jpg"
    ;;
  *)
    echo "usage: $0 [proof|social-proof|proofs|final|social|poster|release]" >&2
    exit 2
    ;;
esac
