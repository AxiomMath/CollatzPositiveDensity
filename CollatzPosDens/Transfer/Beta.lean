/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.H
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.Bitlength
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# The scale schedule `β_*`

For `q ∈ ℕ` the scale schedule is the natural number
`β_*(q) := K_* (q + 1) 2^{max(0, bl(q+1) - H_*)}`, where `K_*` is the scale multiplier, `H_*` the
plateau height and `bl` the bit length. While `bl(q + 1) ≤ H_*` it is linear,
`β_*(q) = K_* (q + 1)`; beyond the plateau it gains one extra factor of `2` for every bit of
`q + 1` above `H_*`.

## Main definitions

* `CollatzPosDens.betaStar`: the scale schedule `β_*(q)`.

## Main results

* `CollatzPosDens.betaStar_eq_max`: the defining formula with the exponent `max(0, bl(q+1) - H_*)`
  taken in `ℤ`.
* `CollatzPosDens.betaStar_pos`: `0 < β_*(q)`.
* `CollatzPosDens.betaStar_strictMono`: `β_*` is strictly monotone.
* `CollatzPosDens.betaStar_monotone`: `β_*` is monotone.
* `CollatzPosDens.Kstar_mul_le_betaStar`: `K_* (q + 1) ≤ β_*(q)`.
* `CollatzPosDens.betaStar_of_bitLength_le`: `β_*(q) = K_* (q + 1)` when `bl(q + 1) ≤ H_*`.

## Implementation notes

The exponent `max(0, bl(q+1) - H_*)`, read with integer subtraction, is exactly the truncated
subtraction `bl(q+1) - H_*` of `ℕ`; the definition uses the latter, and `betaStar_eq_max`
recovers the former.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale schedule `β_*(q) := K_* (q + 1) 2^{max(0, bl(q+1) - H_*)} ∈ ℕ`; the exponent
`max(0, bl(q+1) - H_*)` is the truncated subtraction `bl(q+1) - H_*` of `ℕ`. -/
@[collatz_pos_dens "def_s02_beta"]
def betaStar (q : ℕ) : ℕ := Kstar * (q + 1) * 2 ^ (bitLength (q + 1) - Hstar)

/-- The defining formula `β_*(q) = K_* (q + 1) 2^{bl(q+1) - H_*}`, with truncated subtraction. -/
theorem betaStar_def (q : ℕ) :
    betaStar q = Kstar * (q + 1) * 2 ^ (bitLength (q + 1) - Hstar) := rfl

/-- The defining formula of `β_*(q)` with the exponent written as `max(0, bl(q+1) - H_*)` in
`ℤ`. -/
theorem betaStar_eq_max (q : ℕ) :
    betaStar q = Kstar * (q + 1) * 2 ^ (max 0 ((bitLength (q + 1) : ℤ) - Hstar)).toNat := by
  have h : ∀ a b : ℕ, (max 0 ((a : ℤ) - b)).toNat = a - b := fun a b => by omega
  rw [betaStar_def, h]

/-- The scale schedule is positive: `0 < β_*(q)` for every `q ∈ ℕ`. -/
theorem betaStar_pos (q : ℕ) : 0 < betaStar q := by
  rw [betaStar_def]
  have := Kstar_pos
  positivity

/-- The scale schedule dominates its linear part: `K_* (q + 1) ≤ β_*(q)` for every `q ∈ ℕ`. -/
@[collatz_pos_dens "lem_s02_beta_lower"]
theorem Kstar_mul_le_betaStar (q : ℕ) : Kstar * (q + 1) ≤ betaStar q :=
  Nat.le_mul_of_pos_right _ (by positivity)

/-- On the plateau the scale schedule is linear: `β_*(q) = K_* (q + 1)` when `bl(q + 1) ≤ H_*`. -/
theorem betaStar_of_bitLength_le {q : ℕ} (h : bitLength (q + 1) ≤ Hstar) :
    betaStar q = Kstar * (q + 1) := by
  rw [betaStar_def, Nat.sub_eq_zero_of_le h, pow_zero, mul_one]

/-- The scale schedule is strictly monotone: `β_*(q) < β_*(q')` whenever `q < q'`. -/
theorem betaStar_strictMono : StrictMono betaStar := by
  intro p q hpq
  rw [betaStar_def, betaStar_def]
  have hs : bitLength (p + 1) ≤ bitLength (q + 1) := Nat.size_le_size (by omega)
  have := Kstar_pos
  calc Kstar * (p + 1) * 2 ^ (bitLength (p + 1) - Hstar)
      < Kstar * (q + 1) * 2 ^ (bitLength (p + 1) - Hstar) := by gcongr
    _ ≤ Kstar * (q + 1) * 2 ^ (bitLength (q + 1) - Hstar) := by gcongr

/-- The scale schedule is monotone: `β_*(q) ≤ β_*(q')` whenever `q ≤ q'`. -/
@[collatz_pos_dens "lem_s02_beta_mono"]
theorem betaStar_monotone : Monotone betaStar :=
  betaStar_strictMono.monotone

end CollatzPosDens
