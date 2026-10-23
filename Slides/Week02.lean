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

# Recap: `exact`, `apply`, `use`, `constructor`

```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  exact hpq hp      -- closes the goal

example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  apply hpq         -- new goal: p
-- ^ !click
  exact hp

example : ∃ x : ℝ, 2 * x = x + 3 := by
  use 3             -- x := 3
-- ^ !click
  ring

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor       -- goals: p and q
-- ^ !click
  · exact hp
  · exact hq
```

:::notes
All from Lectures 2 and 3. `constructor` also splits `↔`. Click through the goals quickly; ask what each tactic leaves.
`use` also closes goals that hold by `rfl` (e.g. `∃ n, n + 1 = 4` after `use 3`), here it doesn't.
Today: one tactic, `refine`, that can do all four.
:::

# `refine` = `exact/apply` with holes

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

# `apply` versus `refine`

```lean -show
-- The failing examples below leave hypotheses unused; don't underline them.
set_option linter.unusedVariables false
```

`apply` adds the missing holes by itself, `refine` does not:

:::hstack
```lean -panel
example (p q : Prop) (hp : p)
    (hq : p → p → q) : q := by
  apply hq
  · exact hp
  · exact hp
```

```lean +error -panel -stretch
example (p q : Prop) (hp : p)
    (hq : p → p → q) : q := by
  refine hq
```
:::

:::::fragment
Every hole must be written as `?_`, not `_`:

::::hstack
```lean +error -panel
example (p q : Prop) (hp : p)
    (hq : p → p → q) : q := by
  refine hq _ _
```

```lean -panel -stretch
example (p q : Prop) (hp : p)
    (hq : p → p → q) : q := by
  refine hq ?_ ?_
  · exact hp
  · exact hp
```
::::
:::::

:::notes
`refine hq`: "Type mismatch: `hq` has type `p → p → q` but is expected to have type `q`".
`refine hq _ _`: "don't know how to synthesize placeholder". `_` means "Lean, work this out yourself"
(as in `exact add_comm _ _`), but Lean can't guess a proof of `p`. `?_` means "I prove this later".
:::


# Why `refine` is more flexible

```lean
-- le_trans : a ≤ b → b ≤ c → a ≤ c
example (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  apply le_trans    -- which b? Three goals
-- ^ !click
  · exact hab
  · exact hbc
-- !fragment

example (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  refine le_trans hab ?_
-- ^ !click
  exact hbc
-- !fragment

example (p q r s : Prop) (hp : p) (hs : s)
    (hq : p → s → q) (hr : q → r) : r := by
  refine hr (hq hp ?_)    -- three steps in one
-- ^ !click
  exact hs
```

:::notes
`refine` lets you fill in what you already know, and put holes anywhere.
`apply le_trans` can't know the middle term: goals `a ≤ ?b`, `?b ≤ c` and `ℝ` (the `?b` itself).
It works out after `exact hab`, but the goals are confusing. `refine le_trans hab ?_` fixes `b` right away.
Last example: a hole deep inside the term, one line instead of `apply hr`, `apply hq`, `exact hp`.
Coming next: holes inside `⟨…⟩` and `fun`, which `apply` can't do at all.
:::

# Anonymous constructor `⟨…⟩`

Builds anything that is made of several pieces (`∧`, `↔`, `∃`, …):

```lean -panel -stretch
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := ⟨hpq, hqp⟩
example : ∃ n : ℕ, n + 2 = 5 := ⟨3, rfl⟩
example : ∃ n : ℕ, n + 2 = 5 ∧ 2 * n = 6 := ⟨3, rfl, rfl⟩
```

* Formally: Gives an element of an inductive type with a single constructor
* Nesting can be flattened: `⟨3, h₁, h₂⟩` means `⟨3, ⟨h₁, h₂⟩⟩`
* Same pattern takes things apart: `obtain ⟨n, h₁, h₂⟩ := h`
* In tactic mode: `exact ⟨hp, hq⟩`

:::notes
`rfl` is a term too: it proves `3 + 2 = 5` by computation.
`∃ n, n + 2 = 5 ∧ 2 * n = 6` is `∃ n, (n + 2 = 5 ∧ 2 * n = 6)`: a pair of `3` and a pair of proofs, hence the nesting.
Lecture 3 had `exact ⟨hz₁.1, hz₁.2, hz₂.2⟩`: three pieces for `x < z₁ ∧ z₁ < z₂ ∧ z₂ < y`.
:::

# `refine` replaces `constructor`

::::class "three"
:::hstack
```lean -panel
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
```

```lean -panel
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  · exact hp
  · exact hq
```

```lean -panel -stretch
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  refine ⟨hp, hq⟩
```
:::
::::

:::fragment
`refine` can do more in one step:
```lean -panel -stretch
example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by
  refine ⟨fun hp ↦ ?_, fun hq ↦ ?_⟩
  · exact hpq hp
  · exact hqp hq
```
:::

:::notes
Third version: instead of leaving holes and filling them later, put `hp` and `hq` in directly
(then `exact ⟨hp, hq⟩` does the same).
`fun hp ↦ ?_` is a function whose body is still a hole: the new goal has `hp` in its context,
exactly as after `intro hp`.
:::

# `refine` replaces `use`

::::class "three"
:::hstack
```lean -panel
example : ∃ x : ℝ,
    2 * x = 6 ∧ x * x = 9 := by
  use 3
  constructor
  · ring
  · ring
```

```lean -panel
example : ∃ x : ℝ,
    2 * x = 6 ∧ x * x = 9 := by
  refine ⟨3, ?_, ?_⟩
  · ring
  · ring
```

```lean -panel -stretch
example : ∃ x : ℝ,
    2 * x = 6 ∧ x * x = 9 := by
  refine ⟨3, by ring, by ring⟩
```
:::
::::

:::notes
Difference: `use` tries to close easy goals by itself afterwards (e.g. `rfl`), `refine` never does.
Third version: no holes left, every piece is filled in directly. `by ring` inside a term proves that
piece with a tactic. Here `exact` would work just as well: there are no holes.
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

# Pitfalls: count the holes

`refine` needs *exactly* one `?_` for each missing argument:

::::::class "three"
:::::hstack
::::vstack
```lean +error -panel
example (p q s : Prop)
    (hp : p) (hs : s)
    (hq : p → s → q) : q := by
  refine hq ?_
```
:::class "small"
✗ Too few: `hq ?_` is still `s → q`
:::
::::

::::vstack
```lean +error -panel
example (p q s : Prop)
    (hp : p) (hs : s)
    (hq : p → s → q) : q := by
  refine hq ?_ ?_ ?_
```
:::class "small"
✗ Too many: `hq ?_ ?_` is not a function
:::
::::

::::vstack
```lean -panel -stretch
example (p q s : Prop)
    (hp : p) (hs : s)
    (hq : p → s → q) : q := by
  refine hq ?_ ?_
  · exact hp
  · exact hs
```
:::class "small"
✓ Two arguments, two holes
:::
::::
:::::
::::::

:::fragment
Same with `⟨…⟩`: `refine ⟨?_, ?_, ?_⟩` for `p ∧ q` is an error. Count the pieces!
:::

:::notes
Ask before revealing the captions: what goes wrong in the first two?
Too few: "Type mismatch: `hq ?_` has type `s → q` but is expected to have type `q`". `apply hq` would add the hole.
Too many: "Function expected": `hq ?_ ?_` is already a proof of `q`, it takes no more arguments.
`⟨…⟩` is forgiving the other way: `refine ⟨?_, ?_⟩` for `p ∧ q ∧ r` works and leaves `p` and `q ∧ r`.
Another pitfall: `have h := ⟨hp, hq⟩` fails ("expected type could not be determined"), write `have h : p ∧ q := ⟨hp, hq⟩`.
:::

# Golfing

*Golfing* a proof: making it shorter, without changing the statement
(as in golf: as few strokes as possible).

* Shorter proofs are often faster to check, Mathlib prefers concise proofs
* But: shorter is not always more readable, and harder to fix when something changes
* Golf *after* proof is done, keep it readable

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

# `convert`: two more examples

```lean
-- sq_nonneg a : 0 ≤ a ^ 2
example (x y : ℝ) : 0 ≤ (x - y) * (x - y) := by
  convert sq_nonneg (x - y)
-- ^ !click
  ring
-- !fragment

example (f : ℝ → ℝ) (h : Continuous (fun x ↦ f (x * 2))) :
    Continuous (fun x ↦ f (2 * x)) := by
  convert h using 3
-- ^ !click
  ring
```

:::fragment
`rw [mul_comm]` fails on the second one: `rw` can't rewrite inside `fun x ↦ …`, `convert` can.
:::

:::notes
First: `convert` with a lemma instead of a hypothesis. The only difference is `(x - y) * (x - y)`
versus `(x - y) ^ 2`, so that equation is left. Ask: what goal do you expect?
Second: `x✝` is the variable of the `fun`: `convert` went inside it.
`using 1` leaves `(fun x ↦ f (2 * x)) = fun x ↦ f (x * 2)`, `using 4` goes too deep (`2 = x` and `x = 2`).
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
