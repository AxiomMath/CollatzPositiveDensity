/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Wb

/-!
# The scale parameter `ℓ_b`

For a natural number `b` this file defines the scale parameter
$$\ell_b = b - w_b, \qquad w_b = \lfloor 3b/5 \rfloor,$$
one of the rounded logarithmic scale parameters of the first-crossing argument.

## Main definitions

* `CollatzPosDens.lb`: the parameter `ℓ_b = b - w_b`.

## Main results

* `CollatzPosDens.lb_def`: the unfolding `ℓ_b = b - w_b`.
* `CollatzPosDens.lb_add_wb`: `ℓ_b + w_b = b`, so the subtraction is exact.
* `CollatzPosDens.lb_eq`: the closed form `ℓ_b = b - 3b/5` (natural-number division).
* `CollatzPosDens.lb_le_self`: `ℓ_b ≤ b`.
* `CollatzPosDens.cast_lb`: the cast of `ℓ_b` is the difference of the casts of `b` and `w_b`.

## Implementation notes

The subtraction is in `ℕ`; since `w_b ≤ b` it is never truncated (`lb_add_wb`), and the
cast to any additive group with one agrees with the integer difference (`cast_lb`).

## References

* [Mazur, *Collatz positive density*], §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale parameter `ℓ_b = b - w_b`, for `b : ℕ`. -/
@[collatz_pos_dens "def_lb"]
def lb (b : ℕ) : ℕ := b - wb b

/-- Unfolding lemma for `lb`. -/
theorem lb_def (b : ℕ) : lb b = b - wb b := rfl

/-- The subtraction defining `ℓ_b` is exact: `ℓ_b + w_b = b`. -/
theorem lb_add_wb (b : ℕ) : lb b + wb b = b := Nat.sub_add_cancel (wb_le_self b)

/-- Closed form `ℓ_b = b - ⌊3b/5⌋`, with natural-number division. -/
theorem lb_eq (b : ℕ) : lb b = b - 3 * b / 5 := rfl

/-- `ℓ_b ≤ b`. -/
theorem lb_le_self (b : ℕ) : lb b ≤ b := Nat.sub_le _ _

/-- The cast of `ℓ_b` is the difference of the casts of `b` and `w_b`. -/
theorem cast_lb {R : Type*} [AddGroupWithOne R] (b : ℕ) : (lb b : R) = b - wb b :=
  Nat.cast_sub (wb_le_self b)

end CollatzPosDens
