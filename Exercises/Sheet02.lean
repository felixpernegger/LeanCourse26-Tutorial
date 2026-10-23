import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exercise sheet 2: `refine`, `⟨…⟩` and `convert`

Replace every `sorry` by a proof. Besides the tactics from the lectures
(`rfl`, `ring`, `rw`, `intro`, `exact`, `apply`, `constructor`, `use`, `obtain`, …)
you need `refine`, anonymous constructors `⟨…⟩` and `convert` from the tutorial.
You don't need `norm_num`, `linarith` or `simp`.

* Part A: `refine` and `⟨…⟩`
* Part B: golfing
* Part C: `convert`
* Part D: bonus, ε-δ

Use `#check` (or hover) to see what a lemma says.
-/

namespace Sheet02

/-! ## Part A: `refine` and `⟨…⟩`

In this part, don't use `constructor`, `use` or `intro`: do it with `refine` instead. -/

/- A1 -/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  sorry

/- A2. One `refine` can split the `↔` *and* introduce the hypotheses of both directions. -/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  sorry

/- A3 -/
example : ∃ x : ℝ, 3 * x + 1 = 7 ∧ x * x = 4 := by
  sorry

/- A4. Try `apply le_trans` first and look at the goals. Then do it with `refine` instead. -/
#check le_trans

example (a b c d : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  sorry

/- A5. Take `h` apart with `obtain`, then finish with a single `exact ⟨…⟩`. -/
example (f : ℝ → ℝ) (h : ∃ x, f x = 0 ∧ 0 < x) : ∃ y, 0 < y ∧ f y = 0 := by
  sorry

/-! ## Part B: Golfing

Each proof below works. Make it as short as you can: ideally a single `exact` (or `refine`),
or a term after `:=` without `by`. -/

/- B1 -/
example (p q r : Prop) (h : p → q) (h' : q → r) : p → r := by
  intro hp
  apply h'
  apply h
  exact hp

/- B2 -/
example (p q r : Prop) (h : p ∧ q ∧ r) : r ∧ p := by
  obtain ⟨hp, hq, hr⟩ := h
  constructor
  · exact hr
  · exact hp

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

/- C1 -/
example (x y : ℝ) (h : x * y + 1 ≤ 5) : 1 + y * x ≤ 5 := by
  sorry

/- C2. Which square is this? -/
#check sq_nonneg

example (x : ℝ) : 0 ≤ x ^ 2 - 2 * x + 1 := by
  sorry

/- C3. First try `convert h` without `using`. Which goals are left, and can you prove them?
Then find a `using n` that works. -/
example (f : ℝ → ℝ) (a b : ℝ) (h : f (a + b) = 0) : f (b + a) = 0 := by
  sorry

/- C4. Why does `rw [add_comm]` not work here? Use `convert` instead. -/
example (f : ℝ → ℝ) (h : ∀ x, f (x + 1) = 0) : ∀ x, f (1 + x) = 0 := by
  sorry

/-! ## Part D (bonus): ε-δ

The definition from the tutorial. Start each proof with one `refine` that introduces `ε`,
chooses `δ` and introduces `y`. -/

def EpsDeltaContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

/- D1. A constant function. -/
#check one_pos
#check sub_self
#check abs_zero

example (x : ℝ) : EpsDeltaContinuousAt (fun _ ↦ 7) x := by
  sorry

/- D2. Careful: a direct `convert` leaves a goal that is false. Why? How does `abs_sub_comm` help? -/
#check abs_sub_comm

example (x : ℝ) : EpsDeltaContinuousAt (fun x ↦ 5 - x) x := by
  sorry

end Sheet02
