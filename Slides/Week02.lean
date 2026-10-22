import VersoSlides
import Mathlib

/-!
Tutorial, week 2. Render with `./slides build 2`.

Syntax reference: https://github.com/leanprover/verso-slides#writing-a-presentation
-/

open VersoSlides

-- The `-- ^ !click` markers make code lines look longer than they are.
set_option verso.code.warnLineLength 0

#doc (Slides) "Tutorial 2: refine, ⟨…⟩ and convert" =>

# `refine`, `⟨…⟩` and `convert`

Bonn Lean Course WiSe 26/27 · Tutorial 2

Felix Pernegger

Friday, October 23 · S0.006

:::notes
Target: 20–30 minutes in total. Main part is `refine` (up to the golfing slides), `convert` is shorter.
Lectures so far: `rfl`, `ring`, `rw`, `calc`, `intro`, `exact`, `have`, `specialize`, `apply`,
`constructor`, `obtain`, `use`. `refine` was used once in Lecture 2 without explanation.
:::

# `refine` = `exact` with holes

* `exact t`: `t` proves the goal completely
* `apply t`: the premises of `t` become new goals
* `refine t`: like `exact`, but each hole `?_` in `t` becomes a new goal

```lean
example (p q r : Prop) (hq : p → p → q) (hr : q → r) :
    p → r := by
  intro hp
  refine hr ?_
-- ^ !click
  refine hq ?_ ?_
-- ^ !click
  · exact hp
  · exact hp
```

:::notes
This is the example from Lecture 2. Before clicking: ask what the goal is after `refine hr ?_`.
Here `refine hr ?_` does the same as `apply hr`, and `refine hq ?_ ?_` the same as `apply hq`.
:::

# `?_` versus `_`

* `_`: “Lean, figure this out from the goal”, e.g. `exact add_comm _ _`
* `?_`: “I will prove this later”: becomes a new goal

```lean
example : Continuous (fun x ↦ x + x * Real.sin x) := by
  refine Continuous.add continuous_id ?_
-- ^ !click
  exact Continuous.mul continuous_id Real.continuous_sin
```

::::fragment
```lean +error -stretch -panel
example : Continuous (fun x ↦ x + x * Real.sin x) := by
  refine Continuous.add continuous_id _
```
:::class "small"
Error: `don't know how to synthesize placeholder`: Lean can't guess proofs.
:::
::::

:::notes
`add_comm _ _`: Lean reads off `a` and `b` from the goal.
The last block fails: a *proof* of `Continuous (fun x ↦ x * sin x)` can't be guessed from the goal,
so `_` gives "don't know how to synthesize placeholder". With `?_` it becomes a goal instead.
:::

# Anonymous constructor `⟨…⟩`

Builds anything that is made of several pieces (`∧`, `↔`, `∃`, …):

```lean -panel -stretch
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := ⟨hpq, hqp⟩
example : ∃ n : ℕ, 2 < n := ⟨3, by norm_num⟩
example : ∃ n : ℕ, 2 < n ∧ n < 5 := ⟨3, by norm_num, by norm_num⟩
```

* Nesting can be flattened: `⟨3, h₁, h₂⟩` means `⟨3, ⟨h₁, h₂⟩⟩`
* Same pattern takes things apart: `obtain ⟨n, h₁, h₂⟩ := h`
* In tactic mode: `exact ⟨hp, hq⟩`

:::notes
`by norm_num` inside a term: proves that piece with a tactic.
`∃ n, 2 < n ∧ n < 5` is `∃ n, (2 < n ∧ n < 5)`: a pair of `3` and a pair of proofs, hence the nesting.
Lecture 3 had `exact ⟨hz₁.1, hz₁.2, hz₂.2⟩`: three pieces for `x < z₁ ∧ z₁ < z₂ ∧ z₂ < y`.
:::

# `refine` replaces `constructor`

:::hstack
```lean -panel
example (p q : Prop) (hp : p) (hq : q) :
    p ∧ q := by
  constructor
  · exact hp
  · exact hq
```

```lean -panel -stretch
example (p q : Prop) (hp : p) (hq : q) :
    p ∧ q := by
  refine ⟨?_, ?_⟩
  · exact hp
  · exact hq
```
:::

:::fragment
`refine` can do more in one step, e.g. `constructor` and `intro` on both sides of an `↔`:

```lean -panel -stretch
example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by
  refine ⟨fun hp ↦ ?_, fun hq ↦ ?_⟩
  · exact hpq hp
  · exact hqp hq
```
:::

:::notes
`fun hp ↦ ?_` is a function whose body is still a hole: the new goal has `hp` in its context,
exactly as after `intro hp`.
:::

# `refine` replaces `use`

:::hstack
```lean -panel
example : ∃ n : ℕ, 2 < n ∧ n < 5 := by
  use 3
  constructor
  · norm_num
  · norm_num
```

```lean -panel -stretch
example : ∃ n : ℕ, 2 < n ∧ n < 5 := by
  refine ⟨3, ?_, ?_⟩
  · norm_num
  · norm_num
```
:::

:::fragment
No holes left to fill later:

```lean -panel -stretch
example : ∃ n : ℕ, 2 < n ∧ n < 5 := by
  refine ⟨3, by norm_num, by norm_num⟩
```
:::

:::notes
Difference: `use` tries to close easy goals by itself afterwards (e.g. `rfl`), `refine` never does.
In the last version, `exact` would work just as well: there are no holes.
:::

# `refine` can do (almost) everything

::::class "compact"
:::table +colHeaders +rowSeps (cellGap := "0.35em 0.8em")
*
  * Tactic
  * With `refine`
*
  * `constructor`
  * `refine ⟨?_, ?_⟩`
*
  * `use 3`
  * `refine ⟨3, ?_⟩`
*
  * `intro x`
  * `refine fun x ↦ ?_`
*
  * `apply h` (with `h : p → q → r`)
  * `refine h ?_ ?_`
*
  * `exact h`
  * `refine h`
:::
::::

:::fragment
Why use the others at all? They read better, `apply` counts the holes for you,
`use` closes trivial goals. `refine` is strongest when it does several steps at once.
:::

:::notes
`refine h` with no `?_` is literally `exact h`.
Ask: how would you replace `intro x y`? (`refine fun x y ↦ ?_`)
:::

# Quiz: which `refine`?

```lean -show
-- Every answer below is checked here.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  refine ⟨?_, ?_, ?_⟩ <;> assumption
example : ∃ x : ℝ, 0 < x ∧ x < 1 := by
  refine ⟨1 / 2, ?_, ?_⟩ <;> norm_num
example (p q r s : Prop) (hq : p → s → q) (hr : q → r) (hp : p) (hs : s) : r := by
  refine hr (hq ?_ ?_)
  · exact hp
  · exact hs
example : ∀ ε : ℝ, ε > 0 → ∃ δ > 0, δ < ε := by
  refine fun ε hε ↦ ⟨ε / 2, ?_, ?_⟩ <;> linarith
```

::::class "compact"
:::table +colHeaders +rowSeps (cellGap := "0.35em 0.8em")
*
  * Goal
  * One `refine` for it
*
  * `p ∧ q ∧ r`
  * {fragment}[`refine ⟨?_, ?_, ?_⟩`]
*
  * `∃ x : ℝ, 0 < x ∧ x < 1`
  * {fragment}[`refine ⟨1 / 2, ?_, ?_⟩`]
*
  * `r`, with `hq : p → s → q`, `hr : q → r`
  * {fragment}[`refine hr (hq ?_ ?_)`]
*
  * `∀ ε : ℝ, ε > 0 → ∃ δ > 0, δ < ε`
  * {fragment}[`refine fun ε hε ↦ ⟨ε / 2, ?_, ?_⟩`]
:::
::::

:::notes
Let them answer each one before revealing.
Third row: two `apply`s in one step.
Fourth row: without `ε : ℝ`, Lean takes `ε : ℕ` and `ε / 2 > 0` becomes false for `ε = 1`
(junk values from last week!).
:::

# Pitfalls

```lean -show
-- The failing examples below leave hypotheses unused; don't underline them.
set_option linter.unusedVariables false
```

`refine` needs *exactly* the right number of holes:

```lean +error -panel -stretch
example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : r := by
  refine hr (hq ?_)
```
:::class "small"
Error: `hq ?_` still has type `s → q`, but `hr` needs a `q`.
:::

::::fragment
`⟨…⟩` needs to know what it builds:

```lean +error -panel -stretch
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h := ⟨hp, hq⟩
  exact h
```

:::class "small"
Error: `The expected type of this term could not be determined`.
:::

Fix: `have h : p ∧ q := ⟨hp, hq⟩`
::::

:::notes
First error: `hq ?_` still has type `s → q`, not `q`. `apply` would have added the missing hole.
Second error: "The expected type of this term could not be determined". `⟨hp, hq⟩` could also be
an `∃`, a pair `p × q`, …; Lean doesn't guess.
:::

# Golfing

*Golfing* a proof: making it shorter, without changing the statement
(as in golf: as few strokes as possible).

* Shorter proofs are often faster to check, Mathlib prefers concise proofs
* But: shorter is not always more readable, and harder to fix when something changes

:::fragment
Golf only *after* the proof works. In the assignments, readability beats length!
:::

:::notes
The name comes from "code golf" in programming.
Golfing is a good way to learn new tactics and to understand what a proof term is.
:::

# Golfing a proof

Prove `p ∧ q → r ∧ s` from `h : p → r` and `h' : q → s`:

```lean -show
section
variable (p q r s : Prop) (h : p → r) (h' : q → s)
include h h'
```

:::::::class "golf"
::::::hstack
```lean -panel
example : p ∧ q → r ∧ s := by
  intro hpq
  constructor
  · apply h
    exact hpq.1
  · apply h'
    exact hpq.2
```

::::vstack
:::fragment
```lean -panel -stretch
example : p ∧ q → r ∧ s := by
  refine fun hpq ↦ ⟨?_, ?_⟩
  · exact h hpq.1
  · exact h' hpq.2
```
:::

:::fragment
```lean -panel -stretch
example : p ∧ q → r ∧ s := by
  refine fun hpq ↦ ⟨h hpq.1, h' hpq.2⟩
```
:::

:::fragment
```lean -panel -stretch
example : p ∧ q → r ∧ s :=
  fun ⟨hp, hq⟩ ↦ ⟨h hp, h' hq⟩
```
:::
::::
::::::
:::::::

```lean -show
end
```

:::notes
Lecture 3's example. Steps: `intro` + `constructor` become `refine fun hpq ↦ ⟨?_, ?_⟩`;
`apply h` + `exact hpq.1` becomes `exact h hpq.1`; then fill the holes directly.
In the third version there are no holes left, so `exact` works too.
Last version: no `by` at all (term mode), and `fun ⟨hp, hq⟩ ↦` takes the pair apart like `obtain`.
:::

# `convert`: almost the right statement

`convert h`: use `h` even though it does not match the goal exactly.
Every difference between `h` and the goal becomes an equation to prove.

```lean
example (x : ℝ) (h : 2 * x ≤ 3) : x + x ≤ 3 := by
  convert h using 1
-- ^ !click
  ring
```

:::fragment
* `using 1`: how deep `convert` looks for differences (smaller number = stops earlier)
* Often `convert` does with a lemma what `rw` + `exact` would need several steps for
:::

:::notes
Here `x + x ≤ 3` and `2 * x ≤ 3` agree on the right, so the only goal left is `x + x = 2 * x`.
:::

# `convert` can go too deep

```lean
example (a b c : ℝ) (h : b * a ≤ c) : a * b ≤ c := by
  convert h
-- ^ !click
  all_goals sorry
-- !fragment

example (a b c : ℝ) (h : b * a ≤ c) : a * b ≤ c := by
  convert h using 1
-- ^ !click
  ring
```

:::fragment
`a = b` is unprovable, but the statement is true! Then try a smaller `using`.
:::

:::notes
Without `using`, `convert` matches `a * b` with `b * a` piece by piece: `a = b` and `b = a`.
(`using 2` still goes too deep here.) Moral: if `convert` leaves a false goal, it went too deep,
the statement may still be fine.
:::

# Putting it together: ε-δ

```lean
def EpsDeltaContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

example (x : ℝ) : EpsDeltaContinuousAt (fun x ↦ x + 1) x := by
  refine fun ε hε ↦ ⟨ε, hε, fun y hy ↦ ?_⟩
-- ^ !click
  convert hy using 2
-- ^ !click
  ring
```

:::notes
The definition from Tutorial 1. Ask first: which `δ` works? (`δ = ε`.)
`refine` does `intro ε hε`, `use ε`, `constructor`, `exact hε`, `intro y hy` in one line.
The goal still shows `(fun x => x + 1) y`: Lean hasn't plugged in `y` yet, `ring` doesn't mind.
Ask what `using 1` would leave: `|(fun x => x + 1) y - …| = |y - x|` (also fine, but harder for `ring`).
:::

# Summary

::::class "compact"
:::table +colHeaders +rowSeps (cellGap := "0.35em 0.8em")
*
  * Tactic
  * What it does
*
  * `exact t`
  * `t` proves the goal completely
*
  * `apply t`
  * `t` proves the goal from some premises, which become new goals
*
  * `refine t`
  * like `exact`, but each hole `?_` in `t` becomes a new goal
*
  * `⟨a, b, …⟩`
  * builds `∧`, `↔`, `∃`, … from its pieces (also in `obtain`, `fun`)
*
  * `convert t using n`
  * like `exact`, but differences between `t` and the goal become new goals
:::
::::

# To do this week

:::hstack
* Do tutorial exercises: [Exercises/Sheet02.lean](https://github.com/felixpernegger/LeanCourse26-Tutorial/blob/main/Exercises/Sheet02.lean) (see QR code)
* Assignment 2: upload on eCampus by 28.10, before class (contains material from Lecture 4)
* Try to golf your own proofs once they work

{image "../assets/qr/sheet02.svg" (width := "220px")}[QR code for exercise sheet 2 on GitHub]
:::
