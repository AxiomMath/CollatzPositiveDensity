/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import CollatzPosDens.Attr

/-!
# The scale increment `e_b`

For `b ∈ ℕ` the scale increment is `e_b := ⌈b/100⌉ ∈ ℕ`.

## Main definitions

* `CollatzPosDens.eb`: the scale increment `e_b = ⌈b/100⌉`.

## Main results

* `CollatzPosDens.eb_eq`: `e_b = (b + 99) / 100` in natural division.
* `CollatzPosDens.natCeil_div_hundred`: `⌈b/100⌉₊ = (b + 99) / 100` in any linearly ordered
  semifield with a floor.
* `CollatzPosDens.eb_eq_natCeil`: `e_b = ⌈b/100⌉₊` in any linearly ordered semifield with a floor.
* `CollatzPosDens.one_le_eb_of_pos`: `1 ≤ e_b` for `b ≥ 1`.

## Implementation notes

The ceiling `⌈b/100⌉` of the natural number `b` is written `(b + 99) / 100` with natural
division, which agrees with `⌈(b : K) / 100⌉₊` (`natCeil_div_hundred`); this keeps `eb`
computable. Note that `e_0 = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The ceiling `⌈b/100⌉` agrees with natural division `(b + 99) / 100`. -/
theorem natCeil_div_hundred {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] (b : ℕ) : ⌈(b : K) / 100⌉₊ = (b + 99) / 100 := by
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ (by norm_num)]
    exact_mod_cast (by omega : b ≤ (b + 99) / 100 * 100)
  · rcases Nat.eq_zero_or_pos ((b + 99) / 100) with h | h
    · omega
    · have : (b + 99) / 100 - 1 < ⌈(b : K) / 100⌉₊ := by
        rw [Nat.lt_ceil, lt_div_iff₀ (by norm_num)]
        exact_mod_cast (by omega : ((b + 99) / 100 - 1) * 100 < b)
      omega

/-- The scale increment `e_b := ⌈b/100⌉`, written `(b + 99) / 100` in natural division. -/
@[collatz_pos_dens "def_eb"]
def eb (b : ℕ) : ℕ := (b + 99) / 100

/-- The scale increment in natural division: `e_b = (b + 99) / 100`. -/
theorem eb_eq (b : ℕ) : eb b = (b + 99) / 100 := rfl

/-- The scale increment is the real ceiling: `e_b = ⌈b/100⌉₊`. -/
theorem eb_eq_natCeil {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] (b : ℕ) : eb b = ⌈(b : K) / 100⌉₊ :=
  (natCeil_div_hundred b).symm

/-- `1 ≤ e_b` for every `b ≥ 1`. -/
theorem one_le_eb_of_pos {b : ℕ} (hb : 0 < b) : 1 ≤ eb b := by
  rw [eb_eq]; omega

end CollatzPosDens
