/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.K
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The clearing constant

The scale multiplier `K_* = 9863028149` is large enough that `11 K_* ≥ 32 · 1575 · 4096`.
Indeed `11 K_* = 108493309639` while `32 · 1575 · 4096 = 206438400`.

## Main results

* `CollatzPosDens.Kstar_clear_numeric`: `32 · 1575 · 4096 ≤ 11 K_*` in `ℕ`.
* `CollatzPosDens.Kstar_clear_numeric_cast`: the same inequality cast into any ordered
  semiring.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clearing constant: `11 K_* ≥ 32 · 1575 · 4096`. -/
@[collatz_pos_dens "lem_tr_clear_numeric"]
theorem Kstar_clear_numeric : 32 * 1575 * 4096 ≤ 11 * Kstar := by
  rw [Kstar_eq]; decide

/-- The clearing constant inequality `11 K_* ≥ 32 · 1575 · 4096`, cast into any ordered
semiring. -/
theorem Kstar_clear_numeric_cast {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : (32 * 1575 * 4096 : R) ≤ 11 * (Kstar : R) := by
  have h := Nat.mono_cast (α := R) Kstar_clear_numeric
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end CollatzPosDens
