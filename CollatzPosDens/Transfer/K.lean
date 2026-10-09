/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Cast.Defs

/-!
# The scale multiplier `K_*`

The scale multiplier is the natural-number constant `K_* = 9863028149`. It multiplies the scale
`q + 1` in the stopping-time budget `CollatzPosDens.betaStar q`, equal to
`K_* (q + 1) 2^(bitLength (q + 1) - Hstar)` with truncated subtraction, and it enters the
constant `CollatzPosDens.aK = ⌈4 K_* / 35⌉ + 11`. It satisfies `K_* > 4096 · 272 = 1114112`.

## Main definitions

* `CollatzPosDens.Kstar`: the scale multiplier `K_* = 9863028149 : ℕ`.

## Main results

* `CollatzPosDens.Kstar_eq`: the value `K_* = 9863028149`.
* `CollatzPosDens.Kstar_pos`: `0 < K_*`.
* `CollatzPosDens.Kstar_cast`: the value of `(K_* : R)` in any additive monoid with one.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale multiplier `K_* := 9863028149 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_K"]
def Kstar : ℕ := 9863028149

/-- The value of the scale multiplier. -/
theorem Kstar_eq : Kstar = 9863028149 := rfl

/-- The scale multiplier is positive. -/
theorem Kstar_pos : 0 < Kstar := by
  rw [Kstar_eq]; decide

/-- The value of the scale multiplier cast into any additive monoid with one. -/
@[simp, norm_cast]
theorem Kstar_cast {R : Type*} [AddMonoidWithOne R] : (Kstar : R) = 9863028149 := by
  rw [Kstar_eq]; exact Nat.cast_ofNat

end CollatzPosDens
