/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Lb
public import CollatzPosDens.Transfer.Plateau
public import CollatzPosDens.Transfer.PBits

/-!
# The value of the bit length of the largest scale

We show `L_B = 17484`. By `CollatzPosDens.betaStar_schedule` every schedule scale is linear,
`β_*(p_i) = K_*(p_i + 1)` for `i ≤ r_*`, so `B_* = K_* P_*` with `P_* = p_{r_*} + 1`, and the
shifted positions `y_i = p_i + 1` obey the integer recurrence
`y_{i+1} = y_i + ⌈4 K_* y_i / 35⌉ + 8294`, `y_0 = 1025`. Iterating this recurrence `r_* = 580`
times gives `P_*` exactly, and an exact evaluation shows `2^17483 ≤ K_* P_* < 2^17484`, whence
`L_B = bl(B_*) = 17484`.

## Main results

* `CollatzPosDens.LB_eq`: `L_B = 17484`.
* `CollatzPosDens.Bstar_eq_Kstar_mul_pStar`: `B_* = K_* P_*`.

## Implementation notes

The constants `P_*`, `B_*` and `L_B` are irreducible and are never evaluated directly. Instead
`P_*` is identified with the `r_*`-th value of a computable recurrence on natural numbers, with the
real ceiling of the window length replaced by ceiling division of natural numbers; the two bounds
on `K_*` times that value are then checked by the kernel's arithmetic on numerals.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `B_* = K_* P_*`. -/
theorem Bstar_eq_Kstar_mul_pStar : Bstar = Kstar * pStar := by
  rw [Bstar_def, betaStar_schedule le_rfl, pStar_def]

/-- **Bit length of the largest scale.** `L_B = 17484`. -/
@[collatz_pos_dens "lem_s02_Lb_value"]
theorem LB_eq : LB = 17484 := by
  have h : 2 ^ 17483 ≤ 9863028149 * scheduleStep^[580] 1025 ∧
      9863028149 * scheduleStep^[580] 1025 < 2 ^ 17484 := by decide +kernel
  have hB : Bstar = 9863028149 * scheduleStep^[580] 1025 := by
    rw [Bstar_eq_Kstar_mul_pStar, pStar_eq_scheduleStep_iterate, Kstar_eq]
  exact le_antisymm (LB_le_iff.2 (hB ▸ h.2)) (lt_LB_iff.2 (hB ▸ h.1))

end CollatzPosDens
