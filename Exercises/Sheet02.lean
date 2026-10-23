import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exercise sheet 2: `refine`, `⟨…⟩` and `convert`

Replace every `sorry` by a proof. Besides the tactics from the lectures, you need `refine`,
anonymous constructors `⟨…⟩` and `convert` from the tutorial. You don't need `norm_num`,
`linarith` or `simp`. Hover over a name (or `#check` it) to see what it says.

Parts A–C should take about 35 minutes. Part D is a bonus.
-/

namespace Sheet02

/-! ## Part A: `refine` and `⟨…⟩`

Don't use `constructor` or `use` in this part: build everything with `refine`
(or `exact`) and `⟨…⟩`. -/

/- A1. Which `x` works? -/
example : ∃ x : ℝ, x * x = 4 ∧ x + 2 = 0 := by
  sorry

/- A2. Start with a single `refine`, without `intro`. -/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  sorry

/- A3. `Function.Surjective f` means `∀ y, ∃ x, f x = y`.
Hint: after one (`intro` and) `refine`, only an equation should be left. Lean may show it as
`(fun x ↦ x + 1) (y - 1) = y`: that is just `y - 1 + 1 = y`, and `ring` can handle it. -/
example : Function.Surjective (fun x : ℝ ↦ x + 1) := by
  sorry

/- A4. Fill in the argument you already have, and leave a hole for the other one. -/
#check add_le_add
#check le_trans

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hd : d ≤ 5) : a + c ≤ b + 5 := by
  sorry

/-! ## Part B: Golfing

Each proof below works. Make it as short as you can: ideally one `exact`, or a term directly
after `:=` (no `by` at the start; a `by` inside `⟨…⟩` is fine). -/

/- B1. Bonus: can you avoid `.1` and `.2` by taking `h` apart right in the `fun`? -/
example (p q r : Prop) : p ∧ q ∧ r → r ∧ p := by
  intro h
  constructor
  · exact h.2.2
  · exact h.1

/- B2. `Monotone f` means `∀ ⦃a b⦄, a ≤ b → f a ≤ f b`. The braces `⦃ ⦄` make `a` and `b`
implicit: you don't pass them, Lean reads them off. So `hf hab : f a ≤ f b` for `hab : a ≤ b`.
(If Lean warns about unused variables in your answer, name them `_`.) -/
example (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) := by
  intro a b hab
  apply hg
  apply hf
  exact hab

/- B3 -/
example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r := by
  constructor
  · intro hp
    apply hqr.1
    apply hpq.1
    exact hp
  · intro hr
    apply hpq.2
    apply hqr.2
    exact hr

/-! ## Part C: `convert` -/

/- C1. The right-hand side is a square in disguise. -/
#check sq_nonneg

example (x : ℝ) : 0 ≤ x ^ 2 - 2 * x + 1 := by
  sorry

/- C2. Try `convert h` first. Which goals are left? Can you prove them?
Then find a `using n` that leaves goals you can prove. -/
example (a b c d : ℝ) (h : a * b ≤ c + d) : b * a ≤ d + c := by
  sorry

/- C3. Why does `rw [add_comm]` fail here? Use `convert`, without `intro`.
Lean may call the variable `a✝`: you can't refer to it by name, but `ring` doesn't need to. -/
example (f : ℝ → ℝ) (h : ∀ x, f (x + 1) = 0) : ∀ x, f (1 + x) = 0 := by
  sorry

/-! ## Part D (bonus): ε-δ

The definition from the tutorial. Start each proof with a single `refine` that introduces `ε`,
chooses `δ` and introduces `y`. -/

def EpsDeltaContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

/- D1. A constant function: any `δ` works. In the goal, `(fun x ↦ 7) y` is just `7`,
and `rw [sub_self]` sees that. -/
#check one_pos
#check sub_self
#check abs_zero

example (x : ℝ) : EpsDeltaContinuousAt (fun _ ↦ 7) x := by
  sorry

/- D2. Careful: here `convert hy using 2` leaves a goal you can't prove. Why?
Use `abs_sub_comm` to turn `hy` around first. -/
#check abs_sub_comm

example (x : ℝ) : EpsDeltaContinuousAt (fun t ↦ 5 - t) x := by
  sorry

end Sheet02
