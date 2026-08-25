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
FormalSLT theorem source. The delivery receipt checks both media hashes, the
poster dimensions, the common render-source commit, and the soundtrack mode
before copying any artifact. If an external master is selected, both cuts must
bind the same master and provenance hashes. The raw master is not delivered.
An explicitly selected interim silent delivery must contain zero audio streams
in both cuts. It records `soundtrack_mode: silent` and omits loudness
measurements. Silent and scored cuts cannot be mixed.
The manifest covers every delivered file except itself.

Generate it after the final sequential render:

```bash
./media/stitched-lil-result-film/render.sh stage-delivery
```
