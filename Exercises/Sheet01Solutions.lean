import Mathlib

/-!
# Exercise sheet 1: Reading Lean statements (solutions)
-/

open Function

-- The `sorry` proofs leave hypotheses unused; don't warn about that.
set_option linter.unusedVariables false

namespace Sheet01Solutions

/-! ## Part A: What does it say? -/

/- A1 -/
theorem a1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := sorry

/- Answer: The product of two positive real numbers is positive. -/

/- A2 -/
theorem a2 : ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p := sorry

/- Answer: For every `n` there is a prime `p ≥ n`, i.e. there are infinitely many primes.
(In Mathlib: `Nat.exists_infinite_primes`.) -/

/- A3 -/
def a3 (f : ℝ → ℝ) : Prop := ∀ x y, x ≤ y → f x ≤ f y

/- Answer: `f` is monotone (non-decreasing). (In Mathlib: `Monotone f`.) -/

/- A4 -/
def a4 (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

/- Answer: The sequence `a` converges to `L`: for every `ε > 0` there is an `N` such that
`|aₙ - L| < ε` for all `n ≥ N`. -/

/- A5. Also: which parameters are explicit, which implicit, which instance parameters? -/
theorem a5 {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) : a * b = b * a := sorry

/- Answer: If every element of a group `G` squares to the identity, then `G` is abelian.
Implicit: `G`. Instance: `[Group G]`. Explicit: `h`, `a`, `b`. -/

/- A6 -/
theorem a6 : ¬ ∃ q : ℚ, q ^ 2 = 2 := sorry

/- Answer: There is no rational number whose square is 2, i.e. `√2` is irrational. -/

/-! ## Part B: What is wrong? -/

/-- B1. Supposed to define: `p` is a prime number. -/
def IsPrime (p : ℕ) : Prop := ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p

/- Answer: `1` satisfies this definition (its only divisor is `1`), but `1` is not prime.
Fix: also require `2 ≤ p`. -/
def IsPrime' (p : ℕ) : Prop := 2 ≤ p ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p

/-- B2. Supposed to say: `(a - b) + b = a`. -/
theorem b2 (a b : ℕ) : a - b + b = a := sorry

/- Answer: False if `a < b`: then `a - b = 0` (junk value), e.g. `1 - 2 + 2 = 2 ≠ 1`.
Fix: add the hypothesis `b ≤ a`. -/
theorem b2' (a b : ℕ) (h : b ≤ a) : a - b + b = a := sorry

/-- B3. Supposed to define: the sequence `a` converges to `L`. -/
def b3 (a : ℕ → ℝ) (L : ℝ) : Prop := ∃ N, ∀ ε > 0, ∀ n ≥ N, |a n - L| < ε

/- Answer: The quantifiers are in the wrong order: here `N` may not depend on `ε`.
This says that `aₙ = L` for all `n ≥ N` (the sequence is eventually constant).
Fix: `∀ ε > 0, ∃ N, …` as in A4. -/
def b3' (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

/-- B4. Supposed to say: `√(x²) = x`. -/
theorem b4 (x : ℝ) : √(x ^ 2) = x := sorry

/- Answer: False for negative `x`: `√((-1)²) = 1 ≠ -1`.
Fix: assume `0 ≤ x` (or conclude `√(x ^ 2) = |x|`). -/
theorem b4' (x : ℝ) (hx : 0 ≤ x) : √(x ^ 2) = x := sorry

/-- B5. Supposed to say: if `a` divides `b`, then `a ≤ b`. -/
theorem b5 (a b : ℕ) (h : a ∣ b) : a ≤ b := sorry

/- Answer: False for `b = 0`: every number divides `0`, e.g. `5 ∣ 0` but `5 > 0`.
Fix: assume `0 < b`. -/
theorem b5' (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b := sorry

/-- B6. Supposed to define: the average of `a` and `b`. -/
def average (a b : ℕ) : ℕ := (a + b) / 2

/- Answer: Division on `ℕ` rounds down: `average 1 2 = 1`, not `1.5`.
Fix: return a rational (or real) number. -/
def average' (a b : ℕ) : ℚ := (a + b) / 2

/-! ## Part C: Formalise it -/

/- C1. The sum of two odd integers is even. -/
theorem SumOfOddsIsEven (a b : ℤ) (ha : Odd a) (hb : Odd b) : Even (a + b) := sorry

/- C2. Twin prime conjecture. -/
theorem TwinPrimeConjecture (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) := sorry

/- C3. Goldbach's conjecture. -/
theorem Goldbach (n : ℕ) (even : Even n) (tn : 2 < n) : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := sorry

/- C4. The function `f` is injective. (In Mathlib: `Function.Injective f`.) -/
def MyInjective (f : ℝ → ℝ) : Prop := ∀ x y, f x = f y → x = y

/- C5. The function `f` is bounded. -/
def MyBounded (f : ℝ → ℝ) : Prop := ∃ M, ∀ x, |f x| ≤ M

/- C6. Divisibility is transitive. -/
theorem Dvd_trans (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := sorry

/- C7. Lagrange's four-square theorem. -/
theorem FourSquares (n : ℕ) : ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := sorry

end Sheet01Solutions
