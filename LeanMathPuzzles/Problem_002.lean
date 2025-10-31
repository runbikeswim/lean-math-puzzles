/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic

import VersoManual
import Verso.Output.Html

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Linear Equation" =>

This problem is stated in [this youtube-video](https://youtu.be/TECF-oqusE0?si=_druK99cn6aWqWMt).

# Problem Statement

Find all $`a \in \R` that solves the equation $`a / 19 = -a`.

# Proof by Hand

First assume that $`a = 0`. Then the equation simplifies to $`0 / 19 = -0`, which is obviously true.

Now assume that $`a \neq 0`.
Then, we can simplify as follows:
$$`
\begin{align*}
   a / 19 = -a &\Longleftrightarrow \\
   1 / 19 = -1 &\Longleftrightarrow \\
   1 = -19 &\Longleftrightarrow \\
   \text{contradiction} & \\
\end{align*}
`
Thus, the only solution is $`a = 0`.

# Formal Proof in Lean

This Lean proof closely follows the proof by hand.

```lean
example (a : ℝ) (h : a / 19 = -a) : a = 0 := by
  by_contra g -- assume g : a ≠ 0
  field_simp [g] at h
  linarith
```
