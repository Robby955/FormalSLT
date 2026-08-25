# Delivery contract

The `delivery/` directory is generated only after both native films and both
posters pass their source-bound checks. It contains:

- `stitched-lil-result-1920x1080.mp4` and its media receipt;
- `stitched-lil-result-1080x1350.mp4` and its media receipt;
- native 16:9 and 4:5 poster PNGs;
- the two WebVTT caption sidecars and accessible transcripts;
- the exact fact and claim receipts;
- `delivery-receipt.json` and `MANIFEST.sha256`.

The media receipts bind the films to the committed render source and the
FormalSLT v0.2.0 theorem source. The delivery receipt checks both media hashes,
the poster dimensions, and the common render-source commit before copying any
artifact. The manifest covers every delivered file except itself.

Generate it after the final sequential render:

```bash
./media/stitched-lil-result-film/render.sh stage-delivery
```
