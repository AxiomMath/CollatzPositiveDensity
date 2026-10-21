/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The offset cap

This file defines the *offset cap* `CollatzPosDens.offsetCap`, the natural number `2^600`, which
serves as a uniform upper bound on word offsets, and records its value, its positivity and its
cast into an arbitrary semiring.

## Main definitions

* `CollatzPosDens.offsetCap`: the natural number `2^600`.

## Main results

* `CollatzPosDens.offsetCap_eq`: `offsetCap = 2^600`.
* `CollatzPosDens.offsetCap_pos`: `0 < offsetCap`.
* `CollatzPosDens.cast_offsetCap`: the cast of `offsetCap` into any semiring is `2^600`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset cap, the natural number `2^600`. -/
@[collatz_pos_dens "def_s05_offset_cap"]
def offsetCap : ℕ := 2 ^ 600

/-- The offset cap equals `2^600`. -/
theorem offsetCap_eq : offsetCap = 2 ^ 600 := rfl

/-- The offset cap is positive. -/
theorem offsetCap_pos : 0 < offsetCap := by
  rw [offsetCap_eq]
  exact pow_pos two_pos 600

/-- The offset cap is nonzero. -/
theorem offsetCap_ne_zero : offsetCap ≠ 0 :=
  offsetCap_pos.ne'

/-- The cast of the offset cap into any semiring is `2^600`. -/
@[simp, norm_cast] theorem cast_offsetCap {R : Type*} [Semiring R] :
    (offsetCap : R) = 2 ^ 600 := by
  rw [offsetCap_eq, Nat.cast_pow, Nat.cast_ofNat]

/-- The cast of the offset cap into an ordered semiring is positive. -/
theorem cast_offsetCap_pos {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    (0 : R) < offsetCap :=
  Nat.cast_pos.2 offsetCap_pos

/-- The cast of the offset cap into an ordered semiring is nonnegative. -/
theorem cast_offsetCap_nonneg {R : Type*} [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] : (0 : R) ≤ offsetCap :=
  cast_offsetCap_pos.le

end CollatzPosDens
