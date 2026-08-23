# FormalSLT overview film

This directory contains the fact-bound source for a silent, caption-led
overview of FormalSLT. The film presents the library as a broad checked proof
spine for statistical learning under adaptive and dependent data. It does not
promote one application or numerical receipt as the identity of the project.

The checked facts are extracted from the exact merged-main commit
`e18e3f52326c98c878e73557305fc9ee482f499e`. The extractor fails if that commit
does not contain the named declarations or the published library counts.

## Render

Requirements:

- Python 3.13
- Manim Community 0.20.1
- FFmpeg
- the Avenir Next and Menlo fonts included with macOS

Install the renderer into an isolated environment with:

```bash
python3 -m venv .venv
source .venv/bin/activate
python3 -m pip install -r media/formalslt-overview/requirements.txt
```

From the repository root:

```bash
./media/formalslt-overview/render.sh proof
./media/formalslt-overview/render.sh final
./media/formalslt-overview/render.sh site
```

`proof` renders a fast 854 by 480 review copy. `final` renders the 1920 by 1080
30 fps master. `site` also refreshes the reviewed web copy and poster under
`docs/site/assets/`. Intermediate files are written under
`media/formalslt-overview/out/` and are intentionally ignored by Git.

The film has no narration or soundtrack. It is designed to remain legible on
autoplay and to serve as the motion layer for a later narrated cut.

The committed `facts.json` is a reviewable receipt. Every render regenerates it
from the bound Git commit and stops if a named theorem or published library
count no longer matches.
