import VersoSlides
import Mathlib

/-!
Tutorial, week 1. Render with `./slides build 1`.

Syntax reference: https://github.com/leanprover/verso-slides#writing-a-presentation
-/

open VersoSlides

-- The `/- !fragment … -/` markers make code lines look longer than they are.
set_option verso.code.warnLineLength 0

#doc (Slides) "Tutorial 1: Welcome" =>

# Welcome to the Lean tutorial!

Bonn Lean Course WiSe 26/27 · Tutorial 1

Felix Pernegger

Friday, October 16 · S0.006

:::notes
Target: 20–30 minutes in total.
:::

# Organization

* Course repository: [github.com/fpvandoorn/LeanCourse26](https://github.com/fpvandoorn/LeanCourse26)
  * `Lectures`: lecture files, posted before and after class
  * `Assignments`: hand in via eCampus

* Contact me:
  * Email: [s59fpern@uni-bonn.de](mailto:s59fpern@uni-bonn.de)
  * More convenient: [direct message on Zulip](https://leanprover.zulipchat.com/#narrow/dm/780789-Felix-Pernegger)

* Lean seminar directly after this Tutorial

* More tutorials soon

:::notes
Zulip is introduced in more detail later (online communities).
:::

# Literature

::::class "compact"
:::table +colHeaders +rowSeps (cellGap := "0.35em 0.8em")
*
  * Where
  * What
*
  * [*Natural Number Game*](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
  * Start here! Basic tactics, in your browser
*
  * [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/)
  * The course roughly follows it: read it alongside
*
  * [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
  * Lean itself rather than mathematics; after Mathematics in Lean
*
  * [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
  * Lean as a programming language
*
  * [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
  * Writing your own tactics and syntax
*
  * [Lean Language Reference](https://lean-lang.org/doc/reference/latest/)
  * The full reference; little use for beginners
*
  * [The Proof in the Code](https://www.quantabooks.org/books/the-proof-in-the-code/)
  * Pop-science history of Lean (mixed reception)
:::
::::

:::notes
* Mathematics in Lean: work through the chapters alongside the course, you will learn a lot
  (this is what I did two years ago). You learn how mathematics is formalised in Lean and Mathlib.
  Some of the later chapters can be skipped.
* Theorem Proving in Lean 4 overlaps somewhat with Mathematics in Lean, but focuses on Lean's infrastructure.
* I haven't read the programming and metaprogramming books myself.
* The Proof in the Code: if the library doesn't have it, ask me if you want to read it.
:::

# Online communities

::::hstack
:::vstack
*Zulip*: [leanprover.zulipchat.com](https://leanprover.zulipchat.com/)

{image "../assets/qr/zulip.svg" (width := "220px")}[QR code for leanprover.zulipchat.com]

The main Lean community, research forum.
:::

:::vstack
*Discord*: Lean 4 anarchy

{image "../assets/qr/discord.svg" (width := "220px")}[QR code for the Lean 4 anarchy Discord]

“everything goes”.
:::
::::

:::notes
There are also some Chinese-language communities online, but I don't know about them.
:::

# AI and Lean

* AI can do everything we do in this course better and faster
* (Mostly) Not recommended for learning
* Small things: Web (chatgpt.com) should be enough
* Claude Code and Codex for projects are best (20€ sub suffices), Aristotle by Harmonic decent free alternative

# Finding lemmas in Mathlib

::::hstack
:::vstack
[*LeanSearch*](https://leansearch.net/)

Search in natural language:

“product of two nonnegative reals is nonnegative”

Best when starting out.
:::

:::vstack
[*Loogle*](https://loogle.lean-lang.org/)

Search by names and patterns:

`0 ≤ ?a * ?b`

Often more accurate and quicker once you know the Mathlib naming conventions.
:::
::::

:::notes
TODO: add more tools.
:::

# Anatomy of a theorem

```lean -panel -stretch
/- !fragment partKeyword 1 -/theorem/- !end fragment -/ /- !fragment partName 2 -/my_add_sq/- !end fragment -/ /- !fragment partParams 3 -/(a b : ℝ)/- !end fragment -/ :
    /- !fragment partStatement 4 -/(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2/- !end fragment -/ := /- !fragment partProof 5 -/by ring/- !end fragment -/
```

1. {fragment (style := partKeyword) (index := 1)}[*Keyword*]: `theorem` or `lemma` (`example` has no name)
2. {fragment (style := partName) (index := 2)}[*Name*]: to use it later, e.g. `rw [my_add_sq]`
3. {fragment (style := partParams) (index := 3)}[*Parameters*]: what the theorem is about
4. {fragment (style := partStatement) (index := 4)}[*Statement*]: after the `:`, what is claimed
5. {fragment (style := partProof) (index := 5)}[*Proof*]: after the `:=`

# Definitions have the same shape

```lean -panel -stretch
/- !fragment partKeyword 1 -/def/- !end fragment -/ /- !fragment partName 1 -/f/- !end fragment -/ /- !fragment partParams 1 -/(x : ℝ)/- !end fragment -/ : /- !fragment partStatement 1 -/ℝ/- !end fragment -/ := /- !fragment partProof 1 -/x ^ 2 + 1/- !end fragment -/

theorem f_pos (x : ℝ) : 0 < f x := by
  unfold f
  positivity
```

* {fragment (style := partStatement) (index := 1)}[*Type*] instead of statement: what kind of object `f x` is
* {fragment (style := partProof) (index := 1)}[*Value*] instead of proof: what `f x` is

:::fragment
A theorem is a definition whose type is a statement, and whose value is a proof!
:::

# Parameters

```lean -panel -stretch
theorem my_mul_comm {G : Type*} [CommMagma G] (a b : G) :
    a * b = b * a :=
  mul_comm a b
```

* `(a b : G)` *explicit*: you provide them, e.g. `my_mul_comm x y` proves `x * y = y * x`
* `{G : Type*}` *implicit*: Lean figures it out (from the type of `a` and `b`)
* `[CommMagma G]` *instance*: “`G` has a commutative multiplication”, found automatically

:::notes
Hover over `mul_comm` on the previous slides: Mathlib's `mul_comm` has exactly this signature.
:::

# Hypotheses are parameters too

```lean -panel -stretch
theorem my_mul_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a * b :=
  mul_nonneg ha hb
```

`ha` and `hb` are parameters whose types are statements. To use the theorem,
you pass proofs of them: `my_mul_nonneg (sq_nonneg x) h`.

:::fragment (index := 1)
The same statement, with everything after the colon:

```lean -panel -stretch
theorem my_mul_nonneg' : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  fun _ _ ha hb ↦ mul_nonneg ha hb
```
:::

# Reading a real theorem: Feit–Thompson

```lean -show
-- The `sorry` proofs below leave hypotheses unused; don't underline them.
set_option linter.unusedVariables false
```

```lean -panel -stretch
theorem feit_thompson /- !fragment partParams 1 -/(G : Type*) [Group G] [Finite G]/- !end fragment -/
    /- !fragment partParams 2 -/(hG : Odd (Nat.card G))/- !end fragment -/ :
    /- !fragment partStatement 3 -/IsSolvable G/- !end fragment -/ := by
  sorry
```

1. {fragment (style := partParams) (index := 1)}[Let $`G` be a finite group]
2. {fragment (style := partParams) (index := 2)}[of odd order.]
3. {fragment (style := partStatement) (index := 3)}[Then $`G` is solvable.]

:::fragment (index := 4)
The proof is 255 pages long. It was formalized in Rocq (Gonthier et al., 2012), but it is not in Mathlib: hence `sorry`.
:::

# A definition and a classic

```lean -panel -stretch
def EpsDeltaContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

theorem fundamental_theorem_of_algebra (f : Polynomial ℂ)
    (hf : 0 < f.degree) :
    ∃ z : ℂ, f.IsRoot z :=
  Complex.exists_root hf
```

* A definition of type `Prop`: its value is a statement. (`∀ ε > 0, …` means `∀ ε, ε > 0 → …`)
* Fundamental theorem of algebra: in Mathlib as `Complex.exists_root`.

:::notes
Ask the audience to read the statements aloud before explaining them.
For the definition: ask what `EpsDeltaContinuousAt f x` means in words.
Mathlib's `ContinuousAt` is defined with filters instead; `Metric.continuousAt_iff` says it agrees with ε-δ.
:::

# Lean is strict: every term has a type

```lean -panel -stretch
example (a b : ℕ) : ℕ := a - b  -- subtraction of natural numbers
example (a b : ℕ) : ℤ := a - b  -- subtraction of integers: ↑a - ↑b
```

* If `a b : ℕ`, then `a - b` is a natural number. Always.
* So `-` on `ℕ` must return *some* natural number, even if `a < b`. Same for `/` on `ℕ`, and for division by `0`.
* Such values are called *junk values*. Theorems about `a - b` on `ℕ` usually need a hypothesis like `b ≤ a`.

:::notes
Hover over `-` in both lines: the first is subtraction on ℕ, the second on ℤ (with coercions `↑`).
Don't give away any values yet: the next slide is the quiz.
:::

# Quiz

What does Lean say?

:::class "quiz"
```lean -panel -stretch
#eval 2 - 1
#eval 1 - 2
#eval 4 / 3
```
:::

:::fragment
And what changes with `(1 - 2 : ℤ)` and `(4 / 3 : ℝ)`?
:::

:::notes
Let them vote/guess first. Then click each (empty-looking) answer box to reveal it.
Point out: without a type annotation, numerals default to `ℕ`.
:::

# Fermat's Last Theorem

```lean -panel -stretch
theorem FLT (a b c n : ℕ) (hn : 2 < n) :
    a ^ n + b ^ n ≠ c ^ n := by
  sorry
```

Is this statement sound?

:::fragment
Take `a = 0` and `b = c`: then `0 ^ n + b ^ n = b ^ n`. The statement is false!
:::

:::fragment
```lean -panel -stretch
theorem fermat_last_theorem (a b c n : ℕ) (hn : 2 < n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ n + b ^ n ≠ c ^ n := by
  sorry
```
:::

:::notes
Ask orally first, reveal only afterwards. Moral: Lean takes the statement literally,
so "the obvious assumptions" (here: positive integers) have to be written down.
FLT itself is not in Mathlib yet; a large project is working on it.
:::

# To do this week

* Install VSCode, join GitHub
* Install Lean and the course repository; check that `LeanCourse26/Test.lean` works
* Do tutorial exercices
* Play the Natural Number Game / do first assignment
