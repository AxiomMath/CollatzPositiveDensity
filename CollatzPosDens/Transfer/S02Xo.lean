/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Tactic.NormNum

/-!
# The overshoot allowance

For each Fourier index `ι : FIndex`, the overshoot allowance is a natural number `X_o(ι)`, with
`X_o(o) = 194` and `X_o(b) = 182`.

## Main definitions

* `CollatzPosDens.overshootAllowance`: the natural number `X_o(ι)`.

## Main results

* `CollatzPosDens.overshootAllowance_o`, `CollatzPosDens.overshootAllowance_b`: `X_o(o) = 194`
  and `X_o(b) = 182`.
* `CollatzPosDens.cast_overshootAllowance_o`, `CollatzPosDens.cast_overshootAllowance_b`: the two
  values cast into an additive monoid with one, e.g. `ℤ`, `ℚ` or `ℝ`.
* `CollatzPosDens.overshootAllowance_pos`: `0 < X_o(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The overshoot allowance `X_o(ι) ∈ ℕ`: `X_o(o) := 194` and `X_o(b) := 182`. -/
@[collatz_pos_dens "def_s02_Xo"]
def overshootAllowance : FIndex → ℕ
  | .o => 194
  | .b => 182

/-- The overshoot allowance at the original index equals `194`. -/
@[simp]
theorem overshootAllowance_o : overshootAllowance .o = 194 := rfl

/-- The overshoot allowance at the bootstrap index equals `182`. -/
@[simp]
theorem overshootAllowance_b : overshootAllowance .b = 182 := rfl

/-- The overshoot allowance `X_o(o)`, cast into an additive monoid with one, equals `194`. -/
@[simp, norm_cast]
theorem cast_overshootAllowance_o {R : Type*} [AddMonoidWithOne R] :
    (overshootAllowance .o : R) = 194 := by
  rw [overshootAllowance_o, Nat.cast_ofNat]

/-- The overshoot allowance `X_o(b)`, cast into an additive monoid with one, equals `182`. -/
@[simp, norm_cast]
theorem cast_overshootAllowance_b {R : Type*} [AddMonoidWithOne R] :
    (overshootAllowance .b : R) = 182 := by
  rw [overshootAllowance_b, Nat.cast_ofNat]

/-- The overshoot allowance `X_o(ι)` is positive. -/
theorem overshootAllowance_pos (ι : FIndex) : 0 < overshootAllowance ι := by
  cases ι <;> decide

end CollatzPosDens
