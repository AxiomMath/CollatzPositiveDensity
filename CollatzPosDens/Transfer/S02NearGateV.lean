/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Xd
public import CollatzPosDens.Transfer.S02Wtot
public import CollatzPosDens.Transfer.S02VLower

/-!
# The near gate at the packing bound

For each Fourier index `ι`, the drift-free allowance `X_d(ι, ·)`, the vertical allowance
`X_l(ι, ·)` and the total allowance `W(ι, ·)` are affine in `v`, and
$$X_d(o, v) + \frac{X_l(o, v)}{4} + \frac{8}{25} W(o, v) + 1
  = \frac{105079}{100} + \frac{1506437}{200000}\,v,$$
$$X_d(b, v) + \frac{X_l(b, v)}{4} + \frac{8}{25} W(b, v) + 1
  = \frac{41521}{50} + \frac{378799}{50000}\,v.$$
Both slopes are below `8`, so the left side is at most `8 v` as soon as `210158000 ≤ 93563 v`
(for `o`), resp. `41521000 ≤ 21201 v` (for `b`); in particular for every `v ≥ 2247` at both
indices. This applies to the active packing bound, since `V_*(ι) ≥ 2^18 = 262144`
(`V_*(b) = 514218`).

## Main results

* `CollatzPosDens.Xd_add_Xl_div_four_add_totalAllowance_add_one_eq_o`,
  `CollatzPosDens.Xd_add_Xl_div_four_add_totalAllowance_add_one_eq_b`: the affine formulas.
* `CollatzPosDens.Xd_add_Xl_div_four_add_totalAllowance_add_one_le`: the near gate
  `X_d(ι, v) + X_l(ι, v)/4 + (8/25) W(ι, v) + 1 ≤ 8 v` for `v ≥ 2247`.
* `CollatzPosDens.Xd_add_Xl_div_four_add_totalAllowance_add_one_le_Vstar`: the near gate at the
  active packing bound, `X_d(ι, V_*(ι)) + X_l(ι, V_*(ι))/4 + (8/25) W(ι, V_*(ι)) + 1 ≤ 8 V_*(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The near-gate quantity at the original index is affine in the horizon:
`X_d(o, v) + X_l(o, v)/4 + (8/25) W(o, v) + 1 = 105079/100 + (1506437/200000) v`. -/
theorem Xd_add_Xl_div_four_add_totalAllowance_add_one_eq_o (v : ℕ) :
    Xd .o v + Xl .o v / 4 + 8 / 25 * totalAllowance .o v + 1 =
      105079 / 100 + 1506437 / 200000 * (v : ℚ) := by
  rw [Xd_eq_o, Xl_eq_o, totalAllowance_eq_o]
  ring

/-- The near-gate quantity at the bootstrap index is affine in the horizon:
`X_d(b, v) + X_l(b, v)/4 + (8/25) W(b, v) + 1 = 41521/50 + (378799/50000) v`. -/
theorem Xd_add_Xl_div_four_add_totalAllowance_add_one_eq_b (v : ℕ) :
    Xd .b v + Xl .b v / 4 + 8 / 25 * totalAllowance .b v + 1 =
      41521 / 50 + 378799 / 50000 * (v : ℚ) := by
  rw [Xd_eq_b, Xl_eq_b, totalAllowance_eq_b]
  ring

/-- The near gate `X_d(ι, v) + X_l(ι, v)/4 + (8/25) W(ι, v) + 1 ≤ 8 v` holds for every
`v ≥ 2247`, at both indices. -/
theorem Xd_add_Xl_div_four_add_totalAllowance_add_one_le (ι : FIndex) {v : ℕ} (hv : 2247 ≤ v) :
    Xd ι v + Xl ι v / 4 + 8 / 25 * totalAllowance ι v + 1 ≤ 8 * (v : ℚ) := by
  have : (2247 : ℚ) ≤ v := by exact_mod_cast hv
  cases ι
  · rw [Xd_add_Xl_div_four_add_totalAllowance_add_one_eq_o]; linarith
  · rw [Xd_add_Xl_div_four_add_totalAllowance_add_one_eq_b]; linarith

/-- The near gate at the active packing bound:
`X_d(ι, V_*(ι)) + X_l(ι, V_*(ι))/4 + (8/25) W(ι, V_*(ι)) + 1 ≤ 8 V_*(ι)`. -/
@[collatz_pos_dens "lem_s02_near_gate_V"]
theorem Xd_add_Xl_div_four_add_totalAllowance_add_one_le_Vstar (ι : FIndex) :
    Xd ι (Vstar ι) + Xl ι (Vstar ι) / 4 + 8 / 25 * totalAllowance ι (Vstar ι) + 1 ≤
      8 * (Vstar ι : ℚ) :=
  Xd_add_Xl_div_four_add_totalAllowance_add_one_le ι
    (le_trans (by norm_num) (two_pow_18_le_Vstar ι))

end CollatzPosDens
