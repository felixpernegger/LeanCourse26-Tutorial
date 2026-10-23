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

/- A1. -/
example : ∃ x : ℝ, x * x = 4 ∧ x + 2 = 0 := by
  sorry

/- A2. -/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  sorry

/- A3. Hint: `Function.Surjective f` means `∀ y, ∃ x, f x = y`. -/
example : Function.Surjective (fun x : ℝ ↦ x + 1) := by
  sorry

/- A4. Fill in the argument you already have, and leave a hole for the other one. -/
#check add_le_add
#check le_trans

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hd : d ≤ 5) : a + c ≤ b + 5 := by
  sorry

/-! ## Part B: Golfing

Each proof below works. Try to golf them, ideally bring them down to 1 line. -/

/- B1. -/
example (p q r : Prop) : p ∧ q ∧ r → r ∧ p := by
  intro h
  constructor
  · exact h.2.2
  · exact h.1

/- B2. Hint: `Monotone f` means `∀ ⦃a b⦄, a ≤ b → f a ≤ f b`.
The braces `⦃ ⦄` make `a` and `b` semi-implicit: you don't pass them, Lean reads them off. -/
example (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) := by
  intro a b hab
  apply hg
  apply hf
  exact hab

/- B3. -/
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

-- Use `convert` in all of the following exercises.

/- C1. -/
#check sq_nonneg

example (x : ℝ) : 0 ≤ x ^ 2 - 2 * x + 1 := by
  sorry

/- C2. Try `convert h` first. What is the problem? How to fix? -/
example (a b c d : ℝ) (h : a * b ≤ c + d) : b * a ≤ d + c := by
  sorry

/- C3. Note that `rw [add_comm]` fails here, as `rw` can't look inside the `∀`. -/
example (f : ℝ → ℝ) (h : ∀ x, f (x + 1) = 0) : ∀ x, f (1 + x) = 0 := by
  sorry

/-! ## Part D (bonus): Mega golf

Each proof below works. Golf it down to a single term after `:=`, with no `by` anywhere.
Each one needs one small idea. -/

/- D1 -/
example (p q r : Prop) : (p → q → r) ↔ (p ∧ q → r) := by
  constructor
  · intro h hpq
    apply h
    · exact hpq.1
    · exact hpq.2
  · intro h hp hq
    apply h
    constructor
    · exact hp
    · exact hq

/- D2 -/
example (P : ℝ → Prop) (h : ∀ x, P x) : ∃ x, P x ∧ P (x + 1) := by
  use 0
  constructor
  · exact h 0
  · exact h (0 + 1)

/- D3 -/
example (P Q : ℝ → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).1
    · intro x
      exact (h x).2
  · intro h x
    constructor
    · exact h.1 x
    · exact h.2 x

/- D4. What does `h` need as input? -/
#check congrArg

example (f g : ℝ → ℝ) (h : Function.Injective (g ∘ f)) : Function.Injective f := by
  intro a b hab
  apply h
  unfold Function.comp
  rw [hab]

end Sheet02
