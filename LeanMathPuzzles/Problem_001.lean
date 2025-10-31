/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations
import Mathlib.Order.Defs.LinearOrder

import VersoManual
import Verso.Output.Html

open Real

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.style.longLine false

#doc (Manual) "Quartic Equation" =>

This problem is stated in [this youtube-video](https://youtu.be/8CJ8n_hLoFI?si=0rceDrGyQ3wKPxSa).

# Problem Statement

Find $`x \in \R` that solves the [quartic equation](https://en.wikipedia.org/wiki/Quartic_equation)
$$`
  (x + 3) \cdot (x + 5) \cdot (x + 7) \cdot (x + 9)  = 9
`

What immediately catches the eye is that the four factors on the left-hand side are evenly spaced
around the midpoint $`x + 6`. This symmetry suggests a substitution that can simplify the equation.

# Proof by Hand

This is actually the main idea behind the following proof.

$$`
\begin{align*}
   (x + 3) \cdot (x + 5) \cdot (x + 7) \cdot (x + 9) = 9 &\Longleftrightarrow \\
   (t - 3) \cdot (t - 1) \cdot (t + 1) \cdot (t + 3) = 9
                          \;\; \text{by} \;\; t := x + 6 & \Longleftrightarrow \\
   (t^2 - 3^2) \cdot (t^2 - 1^2) = 9 & \Longleftrightarrow \\
   u^2 - 10 \cdot u + 9 = 9 \;\; \text{by} \;\; u := t^2 & \Longleftrightarrow \\
   u \cdot (u - 10) = 0 & \Longleftrightarrow \\
   u = 0 \, \lor \, u = 10 & \Longleftrightarrow \\
   t = 0 \, \lor \, t = -\sqrt{10} \, \lor \, t = \sqrt{10} & \Longleftrightarrow \\
   x = -6 \, \lor \, x = -6 -\sqrt{10} \, \lor \, t = -6 + \sqrt{10} & \\
\end{align*}
`

# Formal Proof in Lean

The proof is split into two parts. In the first part, it is shown that
$`-6`, $`-6 -\sqrt{10}` and $`-6 +\sqrt{10}` are solutions.

In the second part, it is shown that these are the only solutions.

This also follows from the fact that a quartic equation
has at most four solutions and that the multiplicity of $`-6`
as solution is two.

However, we rather go the _hard_ way using only basic facts
about real numbers.

## Part 1: Verifying the Solutions

Show that $`{\sqrt{10}}^2 = 10`.

```lean
lemma sqrt_10_2 : (sqrt 10) ^ 2 = 10 := by
  rw [sq]
  let x := 10
  rw [mul_self_sqrt]
  simp
```

Show that $`{\sqrt{10}}^4 = {\sqrt{10}}^2 \cdot {\sqrt{10}}^2`.

```lean
lemma sqrt_10_4_sqrt_10_2_2 : (√ 10) ^ 4 =
  (√ 10) ^ 2 * (√ 10) ^ 2 := by ring
```

Show that $`{\sqrt{10}}^4 = 100`.

```lean
lemma sqrt_10_4 : (√ 10) ^ 4 = 100 := by
  rw [sqrt_10_4_sqrt_10_2_2, sqrt_10_2]
  ring
```

The following three examples show that $`-6`,
$`-6 - \sqrt{10}`, $`-6 + \sqrt{10}`
are solving the quartic equation.

Show that $`x = -6` is a solution.

```lean
example (x : ℝ) (h : x = -6) :
  (x + 3) * (x + 5) * (x + 7) * (x + 9) = 9 := by
  rw [h]
  ring
```

Show that $`x = -6 -\sqrt{10}` is a solution.

```lean
example (x : ℝ) (h : x = -6 - √10) :
  (x + 3) * (x + 5) * (x + 7) * (x + 9) = 9 := by
  rw [h]
  ring_nf
  rw [sqrt_10_2, sqrt_10_4]
  ring
```

Show that $`x = -6 +\sqrt{10}` is a solution.

```lean
example (x : ℝ) (h : x = -6 + √10) :
  (x + 3) * (x + 5) * (x + 7) * (x + 9) = 9 := by
  rw [h]
  ring_nf
  rw [sqrt_10_2, sqrt_10_4]
  ring
```

## Part 2: Proving that there are no other Solutions

Show that $`t^2 = t \cdot t`.

```lean
lemma sq_eq_mul_self (t : ℝ) :
  t ^ 2 = t * t := by ring
```

Show that $`0 \leq t^2`.

```lean
lemma zero_le_sq (t : ℝ) : 0 ≤ t ^ 2 := by
  have g : 0 ≤ t ∨ t ≤ 0 := by apply le_total
  rw [sq_eq_mul_self]
  rw [mul_nonneg_iff]
  simp
  assumption
```

Show that $`\lvert x \rvert = y` implies $`x = -y \lor x = y`.

```lean
lemma abs_eq_iff_pos_or_neg_eq' (x y : ℝ) (h : |x| = y):
  x = -y ∨ x = y := by
  if hx: x ≤ 0 then
    unfold abs at h
    simp [hx] at h
    rw [neg_eq_iff_eq_neg] at h
    exact Or.inl h
  else
    unfold abs at h
    apply not_le.mp at hx
    have hnx : -x < x := by simp; exact hx
    rw [max_eq_left_of_lt hnx] at h
    exact Or.inr h
```

Show that $`t^2 = 10` implies $`\lvert t \rvert = \sqrt{10}`.

```lean
lemma quadratic_equation_solutions_1 (t : ℝ)
  (h : t ^ 2 = 10) : |t| = √10 := by
  rw [←sqrt_inj (by apply zero_le_sq) (by simp)] at h
  rw [sqrt_sq_eq_abs] at h
  exact h
```

Show that for $`t \in \R`, the values of expressions
$`(t - 3) \cdot (t - 1) \cdot (t + 1) \cdot (t + 3)`
and
$`t^2 \cdot (t^2 - 10) + 9` are equal.

```lean
lemma quartic_equation_simp (t : ℝ) :
  (t - 3) * (t - 1) * (t + 1) * (t + 3)
    = t ^ 2 * (t ^ 2 - 10) + 9 :=
  calc
    (t - 3) * (t - 1) * (t + 1) * (t + 3)
      = (t - 3) * (t + 3) * (t - 1) * (t + 1)  := by ring
    _ = (t ^ 2 - 3 ^ 2) * (t ^ 2 - 1 ^ 2)  := by ring
    _ = (t ^ 2 - 9) * (t ^ 2 - 1) := by ring
    _ = t ^ 4 - 9 * t ^ 2 - 1 * t ^ 2 + 9  := by ring
    _ = t ^ 4 - 10 * t ^ 2 + 9  := by ring
    _ = t ^ 4 - 10 * t ^ 2 + 9 := by simp
    _ = t ^ 2 * t ^ 2 - 10 * t ^ 2 + 9 := by ring
    _ = t ^ 2 * t ^ 2 - t ^ 2 * 10 + 9 := by ring
    _ = t ^ 2 * (t ^ 2 - 10) + 9:= by ring
```

Show that for $`t \in \R` with
$`(t - 3) \cdot (t - 1) \cdot (t + 1) \cdot (t + 3) = 9`,
$`t = 0 \lor t = - \sqrt{10} \lor t = \sqrt{10}` holds true.

```lean
lemma quartic_equation_solutions (t : ℝ)
  (h : (t - 3) * (t - 1) * (t + 1) * (t + 3) = 9) :
  (t = 0 ∨ t = - √10 ∨ t = √10) := by
  rw [quartic_equation_simp] at h
  simp only [
    add_eq_right,
    mul_eq_zero,
    ne_eq,
    OfNat.ofNat_ne_zero,
    not_false_eq_true,
    pow_eq_zero_iff
  ] at h
  cases h with
  | inl h0 => exact Or.inl h0
  | inr h1 =>
    apply eq_add_of_sub_eq at h1
    simp at h1
    apply quadratic_equation_solutions_1 at h1
    apply abs_eq_iff_pos_or_neg_eq' at h1
    exact Or.inr h1
```

Show that for real numbers $`x, a, b`,
$`x + a = b` implies $`x = -a + b`.

```lean
lemma eq_add_of_neg_add_left (x a b : ℝ)
  (h : x + a = b) : x = -a + b := by
  linarith
```

Show that if $`(x + 3) \cdot (x + 5) \cdot (x + 7) \cdot (x + 9) = 9`
is true for a real number $`x`,
then
$$`
  x = -6 \lor x = -6 - \sqrt{10} \lor x = -6 + \sqrt{10}
`
is also true.

```lean
example (x : ℝ)
  (h : (x + 3) * (x + 5) * (x + 7) * (x + 9) = 9) :
  (x = -6 ∨ x = - 6 - √ 10 ∨ x = -6 + √ 10) := by
  let t := x + 6
  have ht : x = t - 6 := by linarith
  rw [ht] at h
  have hs :
    (t - 6 + 3) * (t - 6 + 5) * (t - 6 + 7) * (t - 6 + 9)
    = (t - 3) * (t - 1) * (t + 1) * (t + 3) := by linarith
  rw [hs] at h
  apply quartic_equation_solutions at h
  have ht' : t = x + 6 := by linarith
  rw [ht'] at h
  cases h with
  | inl hr =>
    apply eq_neg_of_add_eq_zero_left at hr
    exact Or.inl hr
  | inr hl =>
    cases hl with
    | inl hll =>
      apply eq_add_of_neg_add_left at hll
      exact Or.inr (Or.inl hll)
    | inr hlr =>
      apply eq_add_of_neg_add_left at hlr
      exact Or.inr (Or.inr hlr)
```

This completes the proof that the only solutions to the quartic equation
$`(x + 3) \cdot (x + 5) \cdot (x + 7) \cdot (x + 9) = 9`
are $`x = -6`, $`x = -6 - \sqrt{10}` and $`x = -6 + \sqrt{10}`.
