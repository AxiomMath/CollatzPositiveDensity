/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Plateau
public import CollatzPosDens.Transfer.LbValue
public import CollatzPosDens.Transfer.PBits
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.Dcap
public import CollatzPosDens.Transfer.S
public import CollatzPosDens.Transfer.X
public import CollatzPosDens.Transfer.DstarEq

/-!
# The leading binary digits of the scaled threshold

We show `886085405399619011114762 · 2^34928 ≤ X_* < 886085405399619011114763 · 2^34928`.
Since `X_* = 3200 D_*` and `D_* = D_sc`, we have
`X_* = 3200 (2 + P_* + (B_* L_B)^2 + (100 · 2^36 P_*)^2)`, where `B_* = K_* P_*` and
`L_B = 17484`. The integer `P_* = p_{r_*} + 1` is obtained exactly by iterating the shifted
plateau recurrence `y_{i+1} = y_i + ⌈4 K_* y_i / 35⌉ + 8294` from `y_0 = 1025` for `r_* = 580`
steps; evaluating `X_*` exactly from it gives the two bounds.

## Main results

* `CollatzPosDens.Xstar_head`: the leading-digit enclosure of `X_*`.
* `CollatzPosDens.Xstar_head_cast`: `X_* = 3200 D_sc` as an identity in `ℚ`, written out in
  terms of `P_*`, `K_*` and `L_B`.

## Implementation notes

The constants `P_*`, `B_*`, `D_sc` are irreducible and are never evaluated directly. `P_*` is
identified with the `580`-th value of a computable recurrence on natural numbers (ceiling of the
real window length replaced by ceiling division), and the resulting natural-number inequalities
are checked by the kernel's arithmetic on numerals.
-/

@[expose] public section

namespace CollatzPosDens

/-- `X_* = 3200 (2 + P_* + (K_* P_* L_B)^2 + (100 · 2^36 P_*)^2)` with `L_B = 17484`, in `ℕ`
cast to `ℚ`. -/
theorem Xstar_head_cast :
    Xstar = ((3200 * (2 + pStar + (Kstar * pStar * 17484) ^ 2 + (100 * (2 ^ 36 * pStar)) ^ 2) :
      ℕ) : ℚ) := by
  rw [Xstar_def, Dstar_eq_Dsc, Dsc_def, Dcap_def, Bstar_eq_Kstar_mul_pStar, LB_eq, sStar_def]
  push_cast; ring

/-- **Leading digits of `X_*`.**
`886085405399619011114762 · 2^34928 ≤ X_* < 886085405399619011114763 · 2^34928`. -/
@[collatz_pos_dens "lem_s02_X_head"]
theorem Xstar_head :
    886085405399619011114762 * 2 ^ 34928 ≤ Xstar ∧
      Xstar < 886085405399619011114763 * 2 ^ 34928 := by
  have h : 886085405399619011114762 * 2 ^ 34928 ≤
        3200 * (2 + scheduleStep^[580] 1025 +
          (9863028149 * scheduleStep^[580] 1025 * 17484) ^ 2 +
          (100 * (2 ^ 36 * scheduleStep^[580] 1025)) ^ 2) ∧
      3200 * (2 + scheduleStep^[580] 1025 +
          (9863028149 * scheduleStep^[580] 1025 * 17484) ^ 2 +
          (100 * (2 ^ 36 * scheduleStep^[580] 1025)) ^ 2) <
        886085405399619011114763 * 2 ^ 34928 := by
    decide +kernel
  rw [← pStar_eq_scheduleStep_iterate, ← Kstar_eq] at h
  rw [Xstar_head_cast]
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

end CollatzPosDens
