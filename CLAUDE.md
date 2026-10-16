# Tutorial slides (VersoSlides + Mathlib)

- One deck per week: `Slides/WeekNN.lean` (`#doc (Slides) "..." =>`). Shared config: `Slides/Config.lean`.
- Render with `./slides build N`. This runs `lake env lean --run` on a generated `.lake/render/WeekNN.lean`.
- Do not add a `lean_exe` for rendering: it would link all of Mathlib natively.
- Do not add `module` headers to slide files: the interpreter then can't find the doc's IR.
- Versions (`lean-toolchain`, mathlib tag, verso-slides tag) must match LeanCourse26 and each other.
- To check rendering, use `./slides build N`, then screenshot `http://localhost:PORT/weekNN/#/<slide>` with headless Chrome.
  Click/fragment steps only show after real key presses, not when jumping via the URL hash.
- Never put `exact?`, `apply?`, `rw?`, `hint` or similar library searches in slide code: every build re-runs the
  search over all of Mathlib (minutes, ~8 GB RAM), and together with VS Code's worker this crashed the machine.
- Don't run `./slides build` while the same file is open in VS Code and still elaborating (two Mathlib processes).
