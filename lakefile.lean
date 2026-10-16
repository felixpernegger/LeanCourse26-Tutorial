import Lake

open Lake DSL

-- Keep these in sync with LeanCourse26 (its `lean-toolchain` and `lakefile.toml`),
-- so that code on the slides behaves exactly as in the course repository.
-- verso-slides publishes a tag for each Lean release.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc3"

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git" @ "v4.35.0-rc3"

package «tutorial-slides» where
  -- verso-slides recommends ordinary (non-`module`) files for slide decks,
  -- so silence the "consider adding `module`" warning.
  allowNonModules := true
  -- Same options as LeanCourse26.
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

/--
`Slides.Config` holds the shared settings, and `Slides/WeekNN.lean` holds one deck per session.

There is deliberately no `lean_exe`: an executable would have to compile and link all of
Mathlib natively. Instead, `./slides build` runs the renderer in the interpreter.
-/
@[default_target]
lean_lib Slides where
  globs := #[.submodules `Slides]
