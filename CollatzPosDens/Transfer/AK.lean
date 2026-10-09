/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.K
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The growth factor `a_*`

The growth factor is the natural number `a_* = ⌈4 K_* / 35⌉ + 11`, where `K_*` is the scale
multiplier. It bounds the one-step growth of the initial recipe scales, and its numerical value
is `a_* = 1127203218 + 11 = 1127203229`, since `35 · 1127203217 < 4 K_* ≤ 35 · 1127203218`.

## Main definitions

* `CollatzPosDens.aK`: the growth factor `a_* = ⌈4 K_* / 35⌉ + 11 : ℕ`.

## Main results

* `CollatzPosDens.aK_eq_ceil`: `a_* = ⌈(4 K_* : ℝ) / 35⌉₊ + 11`, with the ceiling taken in the
  reals.
* `CollatzPosDens.aK_eq`: the value `a_* = 1127203229`.
* `CollatzPosDens.le_aK`: `4 K_* / 35 + 11 ≤ a_*` in the reals.
* `CollatzPosDens.aK_pos`: `0 < a_*`.

## Implementation notes

The ceiling `⌈4 K_* / 35⌉` is written as the natural-number ceiling division
`(4 K_* + 34) / 35`, so that the value of `a_*` is computable by `decide`/`norm_num`;
`aK_eq_ceil` identifies it with the real ceiling `⌈4 K_* / 35⌉₊`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The growth factor `a_* := ⌈4 K_* / 35⌉ + 11 ∈ ℕ`, with the ceiling written as the
natural-number ceiling division `(4 K_* + 34) / 35`. -/
@[collatz_pos_dens "def_s02_aK"]
def aK : ℕ := (4 * Kstar + 34) / 35 + 11

/-- The growth factor equals `(4 K_* + 34) / 35 + 11`, with natural-number division. -/
theorem aK_def : aK = (4 * Kstar + 34) / 35 + 11 := rfl

/-- The value of the growth factor. -/
@[simp]
theorem aK_eq : aK = 1127203229 := by
  rw [aK_def, Kstar_eq]

/-- The growth factor equals `⌈4 K_* / 35⌉ + 11`, with the ceiling taken in the reals. -/
theorem aK_eq_ceil : aK = ⌈(4 * Kstar : ℝ) / 35⌉₊ + 11 := by
  have h : ⌈(4 * Kstar : ℝ) / 35⌉₊ = 1127203218 := by
    rw [Nat.ceil_eq_iff (by norm_num), Kstar_cast]
    norm_num
  rw [h, aK_eq]

/-- The growth factor dominates `4 K_* / 35 + 11`. -/
theorem le_aK : (4 * Kstar : ℝ) / 35 + 11 ≤ aK := by
  rw [aK_eq_ceil]; push_cast
  gcongr; exact Nat.le_ceil _

/-- The growth factor is positive. -/
theorem aK_pos : 0 < aK := by
  rw [aK_eq]; decide

end CollatzPosDens
