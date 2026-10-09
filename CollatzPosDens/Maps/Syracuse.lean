/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions

/-!
# The Syracuse map

For an odd positive integer `x`, the Syracuse map is
`S(x) = (3x + 1) / 2 ^ v₂(3x + 1)`, where `v₂` is the `2`-adic valuation: it strips every
factor of `2` from `3x + 1`, so its value is again an odd positive integer.

The Syracuse map is the accelerated Collatz map `CollatzPosDens.collatzAccel`; this file
records its defining formula and its basic properties.

## Main results

* `CollatzPosDens.collatzAccel_def`: `S(x) = (3x + 1) / 2 ^ v₂(3x + 1)`.
* `CollatzPosDens.two_pow_mul_collatzAccel`: `2 ^ v₂(3x + 1) * S(x) = 3x + 1`.
* `CollatzPosDens.odd_collatzAccel`: `S(x)` is odd.
* `CollatzPosDens.collatzAccel_pos`: `S(x)` is positive.

## Implementation notes

The map is a total function `ℕ → ℕ` given by the same formula. The restriction to odd
positive `x` is not needed for the formula to make sense, since `3x + 1 ≠ 0` for every
natural `x`, and every result here holds for all `x : ℕ`; oddness of `x` is imposed through
hypotheses rather than a subtype.
-/

@[expose] public section

namespace CollatzPosDens

/-- The Syracuse map is `S(x) = (3x + 1) / 2 ^ v₂(3x + 1)`, with `v₂` the `2`-adic valuation;
it is the accelerated Collatz map `collatzAccel`. -/
@[collatz_pos_dens "def_syracuse"]
theorem collatzAccel_def (x : ℕ) :
    collatzAccel x = (3 * x + 1) / 2 ^ padicValNat 2 (3 * x + 1) := rfl

/-- Multiplying `S(x)` back by the stripped power of two recovers `3x + 1`. -/
theorem two_pow_mul_collatzAccel (x : ℕ) :
    2 ^ padicValNat 2 (3 * x + 1) * collatzAccel x = 3 * x + 1 :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

/-- The Syracuse map takes odd values. -/
theorem odd_collatzAccel (x : ℕ) : Odd (collatzAccel x) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, collatzAccel_def,
    ← Nat.factorization_def _ Nat.prime_two]
  exact Nat.not_dvd_ordCompl Nat.prime_two (Nat.succ_ne_zero _)

/-- The Syracuse map takes positive values. -/
theorem collatzAccel_pos (x : ℕ) : 0 < collatzAccel x :=
  (odd_collatzAccel x).pos

end CollatzPosDens
