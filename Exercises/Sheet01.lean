import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Defs

/-!
# Exercise sheet 1: Reading Lean statements

No proofs today: every `sorry` in parts A and B stays where it is.

* Part A: say in words what the statement or definition means.
* Part B: each declaration is *supposed* to say what its comment claims, but something is wrong.
  Find the problem and fix the statement.
* Part C: formalise the statement yourself by replacing the `sorry` after `Prop :=`.

Write your answers in the `/- Answer: -/` comments. Hover over names you don't know
(or use `#check`) to see what they are.
-/

open Function

-- The `sorry` proofs leave hypotheses unused; don't warn about that.
set_option linter.unusedVariables false

namespace Sheet01

/-! ## Part A: What does it say? -/

/- A1 -/
theorem a1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := sorry

/- Answer:

-/

/- A2 -/
theorem a2 : ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p := sorry

/- Answer:

-/

/- A3 -/
def a3 (f : ℝ → ℝ) : Prop := ∀ x y, x ≤ y → f x ≤ f y

/- Answer:

-/

/- A4 -/
def a4 (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

/- Answer:

-/

/- A5. Also: which parameters are explicit, which implicit, which instance parameters? -/
theorem a5 {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) : a * b = b * a := sorry

/- Answer:

-/

/- A6 -/
theorem a6 : ¬ ∃ q : ℚ, q ^ 2 = 2 := sorry

/- Answer:

-/

/-! ## Part B: What is wrong and how to fix it? -/

/-- B1. Supposed to define: `p` is a prime number. -/
def IsPrime (p : ℕ) : Prop := ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p

/- Answer:

-/

/-- B2. Supposed to say: `(a - b) + b = a`. -/
theorem b2 (a b : ℕ) : a - b + b = a := sorry

/- Answer:

-/

/-- B3. Supposed to define: the sequence `a` converges to `L`. -/
def b3 (a : ℕ → ℝ) (L : ℝ) : Prop := ∃ N, ∀ ε > 0, ∀ n ≥ N, |a n - L| < ε

/- Answer:

-/

/-- B4. Supposed to say: `√(x²) = x`. -/
theorem b4 (x : ℝ) : √(x ^ 2) = x := sorry

/- Answer:

-/

/-- B5. Supposed to say: if `a` divides `b`, then `a ≤ b`. -/
theorem b5 (a b : ℕ) (h : a ∣ b) : a ≤ b := sorry

/- Answer:

-/

/-- B6. Supposed to define: the average of `a` and `b`. -/
def average (a b : ℕ) : ℕ := (a + b) / 2

/- Answer:

-/

/-! ## Part C: Formalise it

Replace each `sorry` by a statement. Everything goes after the colon,
so use `∀`, `∃`, `→`, `∧`, `∨`, `¬` where needed. -/

/- C1. The sum of two odd integers is even. -/
#check Odd
#check Even

--theorem ...

/- C2. Twin prime conjecture: there are infinitely many primes `p` such that `p + 2` is prime too.
Hint: "infinitely many" can be written like in A2. -/
#check Nat.Prime

-- theorem ..

/- C3. Goldbach's conjecture: every even natural number greater than 2 is the sum of two primes. -/
-- theorem ...

/- C4. The function `f` is injective. -/
def MyInjective (f : ℝ → ℝ) : Prop := sorry

/- C5. The function `f` is bounded. -/
-- def ...

/- C6. For natural numbers: if `a` divides `b` and `b` divides `c`, then `a` divides `c`.
Note: "divides" is `∣`, typed `\mid`. It is not the `|` on your keyboard! -/
-- theorem ...

/- C7. Lagrange: every natural number is the sum of four squares. -/
-- theorem ---

end Sheet01
