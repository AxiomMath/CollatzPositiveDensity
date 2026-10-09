/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.OrdinaryTime.Bstar
public import CollatzPosDens.FirstCrossing.ScalesB42
public import Mathlib.Basic.Real.Basic

/-!
# The last scale against the scale sum

The scales satisfy `b_{42} = 256`, so `b_j ≥ 256` for `j ≥ 42`, and there the increment is
`e_{b_j} = ⌈b_j/100⌉ < b_j/100 + 1`. Summing the recursion `b_{j+1} = b_j + e_{b_j}` from
`j = 42` gives, for `n ≥ 42`,
`b_n ≤ 256 + (1/100) ∑_{j=42}^{n-1} b_j + (n - 42) ≤ 214 + B_*(n)/100 + n`,
and for `n ≥ 205` this is at most `9 + B_*(n)/100 + 2n`.

## Main results

* `CollatzPosDens.scale_le_scaleSum_div_hundred`: for `n ≥ 205`,
  `b_n ≤ 9 + B_*(n)/100 + 2n` in `ℝ`.
* `CollatzPosDens.hundred_mul_scale_le_scaleSum`: the cleared-denominator form
  `100 b_n ≤ 21400 + B_*(n) + 100 n` for `n ≥ 42`, in `ℕ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- Summed recursion from `b_{42} = 256`: `100 b_{42+k} ≤ 25600 + 100 k + ∑_{j<42+k} b_j`. -/
private theorem hundred_mul_scale_add_le (k : ℕ) :
    100 * scale (42 + k) ≤ 25600 + 100 * k + ∑ j ∈ Finset.range (42 + k), scale j := by
  induction k with
  | zero => rw [scale_42]; omega
  | succ k ih =>
    have hge : 256 ≤ scale (42 + k) := two_hundred_fifty_six_le_scale (by omega)
    have hs : scale (42 + (k + 1)) = scale (42 + k) + (scale (42 + k) + 99) / 100 := by
      rw [show 42 + (k + 1) = 42 + k + 1 by omega, scale_succ, eb_of_le hge]
    rw [hs, show 42 + (k + 1) = 42 + k + 1 by omega, Finset.sum_range_succ]
    have := Nat.div_mul_le_self (scale (42 + k) + 99) 100
    omega

/-- For `n ≥ 42`, `100 b_n ≤ 21400 + B_*(n) + 100 n`. -/
theorem hundred_mul_scale_le_scaleSum {n : ℕ} (hn : 42 ≤ n) :
    100 * scale n ≤ 21400 + scaleSum n + 100 * n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := hundred_mul_scale_add_le k
  have hsum : ∑ j ∈ Finset.range (42 + k), scale j ≤ scaleSum (42 + k) := by
    rw [scaleSum_def, Finset.sum_range_succ]; omega
  omega

/-- **The last scale against the scale sum.** For every `n ≥ 205`,
`b_n ≤ 9 + B_*(n)/100 + 2n`. -/
@[collatz_pos_dens "lem_ck_scale_last"]
theorem scale_le_scaleSum_div_hundred {n : ℕ} (hn : 205 ≤ n) :
    (scale n : ℝ) ≤ 9 + (scaleSum n : ℝ) / 100 + 2 * n := by
  have h := hundred_mul_scale_le_scaleSum (n := n) (by omega)
  have h' : (100 * scale n : ℝ) ≤ 900 + scaleSum n + 200 * n := by
    exact_mod_cast (by omega : 100 * scale n ≤ 900 + scaleSum n + 200 * n)
  linarith

end CollatzPosDens
