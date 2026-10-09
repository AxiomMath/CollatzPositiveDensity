/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Monotone.Basic
public import CollatzPosDens.Attr

/-!
# The exponent function `t`

This file defines the arithmetic function
$$\mathrm t(u) = 2u - \lfloor 19u/12 \rfloor \qquad (u \in \mathbb{N}).$$
Since `⌊19u/12⌋ ≤ 2u` the difference is a genuine natural number, and `t(u) = ⌈5u/12⌉`.

## Main definitions

* `CollatzPosDens.texp`: the function `t(u) = 2u - ⌊19u/12⌋`.

## Main results

* `CollatzPosDens.texp_add_div`: `t(u) + ⌊19u/12⌋ = 2u`, i.e. the subtraction does not truncate.
* `CollatzPosDens.texp_eq_ceil`: the closed form `t(u) = ⌈5u/12⌉ = (5u + 11) / 12`.

## Implementation notes

The floor `⌊19u/12⌋` is the natural-number division `19 * u / 12`, and the difference is the
truncated subtraction of `ℕ`; by `texp_add_div` the truncation never occurs.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exponent function `t(u) = 2u - ⌊19u/12⌋`, for `u ∈ ℕ`. -/
@[collatz_pos_dens "def_texp"]
def texp (u : ℕ) : ℕ := 2 * u - 19 * u / 12

/-- The defining formula of `texp`. -/
theorem texp_def (u : ℕ) : texp u = 2 * u - 19 * u / 12 := rfl

/-- The subtraction defining `texp` does not truncate: `t(u) + ⌊19u/12⌋ = 2u`. -/
theorem texp_add_div (u : ℕ) : texp u + 19 * u / 12 = 2 * u := by
  unfold texp; omega

/-- Closed form: `t(u) = ⌈5u/12⌉ = (5u + 11) / 12`. -/
theorem texp_eq_ceil (u : ℕ) : texp u = (5 * u + 11) / 12 := by
  unfold texp; omega

/-- `t(0) = 0`. -/
@[simp] theorem texp_zero : texp 0 = 0 := rfl

/-- `t(u) ≤ u`. -/
theorem texp_le_self (u : ℕ) : texp u ≤ u := by
  rw [texp_eq_ceil]; omega

/-- `t` is monotone. -/
theorem texp_mono : Monotone texp := fun a b h => by
  simp only [texp_eq_ceil]; omega

end CollatzPosDens
