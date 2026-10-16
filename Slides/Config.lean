import VersoSlides

/-!
Settings shared by all tutorial decks. `./slides build NN` calls `Slides.render`.

All `Config` fields are documented at https://github.com/leanprover/verso-slides#document-level-configuration
-/

open Verso.Doc VersoSlides

namespace Slides

/-- KaTeX macros available in `$`…`$` and `$$`…`$$` on every slide. -/
def mathPrelude : String := "
\\def\\N{\\mathbb{N}}
\\def\\Z{\\mathbb{Z}}
\\def\\Q{\\mathbb{Q}}
\\def\\R{\\mathbb{R}}
\\def\\C{\\mathbb{C}}
"

/-- VS Code-style hover popups (type, docstring) on Lean code. VersoSlides turns these off by
default, so you can point at code with the mouse while presenting; clicking a token always
shows its info (and proof state) in the panel next to the code. -/
def hoverTooltips : Bool := true

/-- Scripts from `assets/` added to every deck:
`livereload.js` reloads the page after `./slides build` when viewed via `./slides serve`;
`quiz.js` reveals hidden answers in `:::class "quiz"` blocks on click. -/
def scripts : Array String := #["livereload.js", "quiz.js"]

def config (outputDir : System.FilePath) (css : String) : Config where
  theme := "white"
  -- 16:9 leaves room for the info panel next to Lean code.
  width := 1280
  height := 720
  slideNumber := true
  transition := "slide"
  outputDir := outputDir
  mathPrelude := mathPrelude
  extraCss := #[{ filename := "custom.css", contents := ⟨css⟩ }]
  extraJs := scripts

/-- Renders `doc` into `_slides/<name>/`. Run from the repository root. -/
def render (name : String) (doc : Part VersoSlides.Slides) : IO UInt32 := do
  -- Read the stylesheet at render time (not via `include_str`) so that CSS edits
  -- take effect without rebuilding anything.
  let css ← IO.FS.readFile "assets/custom.css"
  let outputDir : System.FilePath := "_slides" / name
  let code ← slidesMain (config outputDir css) doc
  for js in scripts do
    IO.FS.writeFile (outputDir / js) (← IO.FS.readFile ("assets" / js))
  if hoverTooltips then
    -- This VersoSlides script suppresses Verso's hover popups; replace it with a no-op.
    IO.FS.writeFile (outputDir / "lib" / "tippy-panel-filter.js") "// disabled by Slides.hoverTooltips\n"
  -- Written last: `livereload.js` reloads the page when this changes.
  IO.FS.writeFile (outputDir / "build-stamp.txt") (toString (← IO.monoMsNow))
  return code

end Slides
