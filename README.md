# Tutorial slides for LeanCourse26

**Slides: https://felixpernegger.github.io/LeanCourse26-Tutorial/**

Weekly tutorial presentations for the
[Bonn Lean Course WiSe 26/27](https://github.com/fpvandoorn/LeanCourse26), written with
[VersoSlides](https://github.com/leanprover/verso-slides) (reveal.js slides from Lean files).
All Lean code on the slides is checked against Mathlib when the slides are built, and clicking
code (or a `-- ^ !click` step) shows proof states and types in a side panel.

## Setup (once)

```bash
lake exe cache get   # Mathlib build cache
lake build           # builds verso + verso-slides (~6 minutes the first time)
```

## Weekly workflow

```bash
./slides new 3 "Sets and functions"   # creates Slides/Week03.lean from scripts/template.lean
code Slides/Week03.lean               # write the slides; Lean checks them live in VS Code
./slides build 3                      # renders to _slides/week03/
./slides serve                        # open http://localhost:8000/week03/
```

`./slides all` renders every week and writes an overview page at `_slides/index.html`.

`./slides pdf 3` exports `_slides/week03.pdf` with one page per slide. Add `--steps` for one page
per fragment step. This needs `uv` and Chrome. Without them, open
`http://localhost:8000/week03/?print-pdf` in Chrome and print to PDF (landscape, no margins,
background graphics on). Proof states from `!click` steps don't appear in PDFs, because the
info panel is interactive.

The rendered folder works offline (reveal.js, KaTeX and the fonts are bundled). It must be
served over HTTP rather than opened as a `file://` URL.

## Presenting

| Key        | Action                                           |
| ---------- | ------------------------------------------------ |
| → / Space  | next fragment / slide (including proof steps)    |
| S          | speaker view with notes (`:::notes` blocks)      |
| F          | fullscreen                                       |
| Esc / O    | slide overview                                   |
| hover code | popup with type / docstring, as in VS Code (`hoverTooltips` in `Slides/Config.lean`) |
| click code | show its type / proof state in the panel (click again: enclosing term) |

## Writing slides

The template is also a cheat sheet: each example slide shows one feature.

- `# Heading` starts a new slide.
- ` ```lean ` blocks are elaborated with `import Mathlib`. Flags: `-show` (hidden setup code),
  `-panel` (no info panel), `-stretch` (do not fill the slide height). With two code blocks on
  one slide, give all but one of them `-stretch`.
- Inside code: `-- !fragment` reveals the code piece by piece. `-- ^ !click` reveals the proof
  state at the caret position. Code between `/- !hide -/` and `/- !end hide -/` is checked but
  not shown.
- ``{lean}`term` `` is inline checked code. ``$`…` `` is inline math and ``$$`…` `` is display math.
  `\N \Z \Q \R \C` are predefined.
- Directives: `:::fragment`, `:::notes`, `:::hstack` (columns), `:::class "small"`,
  `:::table +colHeaders`.

Full reference: the [verso-slides README](https://github.com/leanprover/verso-slides#writing-a-presentation).

Where the settings live:

- Shared settings (theme, 16:9 size, math macros) are in [Slides/Config.lean](Slides/Config.lean).
- CSS tweaks go in [assets/custom.css](assets/custom.css). They need no rebuild, only `./slides build`.
- To change the starting point for new weeks, edit [scripts/template.lean](scripts/template.lean).

## Publishing (optional)

After you push to GitHub and set Settings → Pages → Source to "GitHub Actions",
[.github/workflows/pages.yml](.github/workflows/pages.yml) publishes `./slides all` on every
push to `main`. Speaker notes end up in the published HTML too (hidden, but readable in the
page source).

## Updating Lean / Mathlib

Keep the versions in step with LeanCourse26. When the course bumps its `lean-toolchain`:

1. Set the same version in [lean-toolchain](lean-toolchain) and in both `require`s in
   [lakefile.lean](lakefile.lean). verso-slides has a git tag for every Lean release.
2. Run `lake update && lake exe cache get && lake build`.

## Why there is no executable

VersoSlides normally renders through a compiled `lean_exe`. Here the slides import Mathlib, so
that executable would have to compile and link all of Mathlib natively, which is a very long build.
`./slides build` instead runs the renderer in the Lean interpreter on a small generated file in
`.lake/render/`. Rendering takes about 10 seconds. For the same reason the slide files are
ordinary Lean files without a `module` header: the interpreter cannot run module-system docs.
