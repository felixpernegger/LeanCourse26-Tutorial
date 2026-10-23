import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exercise sheet 2: `refine`, `⟨…⟩` and `convert` (solutions)
-/

namespace Sheet02Solutions

/-! ## Part A: `refine` and `⟨…⟩` -/

/- A1. Not `x = 2`: that fails the second equation. -/
example : ∃ x : ℝ, x * x = 4 ∧ x + 2 = 0 := by
  refine ⟨-2, ?_, ?_⟩
  · ring
  · ring

/- A2. -/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.2, h.1⟩

/- A3. Also fine: `intro y` first. -/
example : Function.Surjective (fun x : ℝ ↦ x + 1) := by
  refine fun y ↦ ⟨y - 1, ?_⟩
  ring

/- A4. Dead end: `le_trans (add_le_add hab hcd) ?_` leaves `b + d ≤ b + 5`. -/
example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hd : d ≤ 5) : a + c ≤ b + 5 := by
  refine add_le_add hab ?_
  exact le_trans hcd hd

/-! ## Part B: Golfing -/

/- B1. Also fine: `fun h ↦ ⟨h.2.2, h.1⟩`. -/
example (p q r : Prop) : p ∧ q ∧ r → r ∧ p :=
  fun ⟨hp, _, hr⟩ ↦ ⟨hr, hp⟩

/- B2. Common mistake: `hg (hf a b hab)`; `a` and `b` are implicit. -/
example (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) :=
  fun _ _ hab ↦ hg (hf hab)

/- B3. Also fine: `by rw [hpq, hqr]` or `hpq.trans hqr`. -/
example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r :=
  ⟨fun hp ↦ hqr.1 (hpq.1 hp), fun hr ↦ hpq.2 (hqr.2 hr)⟩

/-! ## Part C: `convert` -/

/- C1. -/
example (x : ℝ) : 0 ≤ x ^ 2 - 2 * x + 1 := by
  convert sq_nonneg (x - 1)
  ring

/- C2. `convert h` (and `using 2`) leaves `b = a`, `a = b`, `d = c`, `c = d`: too deep. -/
example (a b c d : ℝ) (h : a * b ≤ c + d) : b * a ≤ d + c := by
  convert h using 1
  · ring
  · ring

/- C3. `using 3` leaves `1 + a✝ = a✝ + 1`. Plain `convert` goes too deep (`1 = a✝`). -/
example (f : ℝ → ℝ) (h : ∀ x, f (x + 1) = 0) : ∀ x, f (1 + x) = 0 := by
  convert h using 3
  ring

/-! ## Part D (bonus): Mega golf

One term, five pieces. The last three entries `3, by ring, by ring` are the `∃` and its `∧`,
flattened into the outer `⟨…⟩`. Injectivity: `h` needs `g (f a) = g (f b)`, i.e. `congrArg g hab`. -/

example (p q r : Prop) (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (h : Function.Injective (g ∘ f)) :
    ((p → q → r) ↔ (p ∧ q → r)) ∧ Monotone (g ∘ f) ∧ Function.Injective f ∧
      (∀ a b, a ≤ b → f a + f a ≤ f b + f b) ∧ ∃ x : ℝ, 2 * x = 6 ∧ x * x = 9 :=
  ⟨⟨fun hpqr ⟨hp, hq⟩ ↦ hpqr hp hq, fun hpqr hp hq ↦ hpqr ⟨hp, hq⟩⟩,
    fun _ _ hab ↦ hg (hf hab), fun _ _ hab ↦ h (congrArg g hab),
    fun _ _ hab ↦ add_le_add (hf hab) (hf hab), 3, by ring, by ring⟩

end Sheet02Solutions
