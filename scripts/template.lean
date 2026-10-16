import VersoSlides
import Mathlib

/-!
Tutorial, week __WEEK__. Render with `./slides build __WEEK__`.

Syntax reference: https://github.com/leanprover/verso-slides#writing-a-presentation
Every top-level `#` heading is one slide. Delete the example slides you don't need.
-/

open VersoSlides

#doc (Slides) "Tutorial __WEEK__: __TITLE__" =>

# Tutorial __WEEK__: __TITLE__

LeanCourse26, Week __WEEK__

:::notes
Speaker notes: press *S* during the talk to open the speaker view.
:::

# Plan for today

:::fragment
* Questions about the lecture
:::

:::fragment
* Assignment __WEEK__: common pitfalls
:::

:::fragment
* Live exercise
:::

# A proof, step by step

Each `-- ^ !click` reveals the proof state at the caret on the next key press.

```lean
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
-- ^ !click
  rw [mul_assoc b a c]
-- ^ !click
```

# Revealing code gradually

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
-- !fragment
  · exact hp
-- !fragment
  · exact hq
```

Inline code is checked too: {lean}`(fun x : ℝ ↦ x ^ 2) 3`.

# Math

$$`\lim_{n \to \infty} \left(1 + \frac{1}{n}\right)^n = e`

Macros from `Slides/Config.lean` work everywhere: $`f : \R \to \R`.

# Two columns

:::hstack
```lean -stretch -panel
example : 2 + 2 = 4 := by
  norm_num
```

```lean -stretch -panel
example : 2 + 2 = 4 := rfl
```
:::

# Exercise

```lean -show
-- Hidden setup: elaborated, but not shown on the slide.
open Function
```

Prove that {lean}`fun x : ℝ ↦ 2 * x + 1` is injective:

```lean
example : Injective (fun x : ℝ ↦ 2 * x + 1) := by
  sorry
```
