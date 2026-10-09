/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.BarrierNat

/-!
# The rounded logarithm `B(j) = ⌈j log₂ 3⌉`

For `j ∈ ℕ` this file defines the natural number
$$\mathsf{B}(j) = \lceil j \log_2 3 \rceil,$$
the least exponent `b` with `3 ^ j ≤ 2 ^ b`. Equivalently `B(j) = Nat.clog 2 (3 ^ j)`, and
`2 ^ B(j)` is the least power of two that is at least `3 ^ j`; in particular
`3 ^ j ≤ 2 ^ B(j) < 2 · 3 ^ j`, with `3 ^ j < 2 ^ B(j)` as soon as `j > 0`.

## Main definitions

* `CollatzPosDens.ceilLog3`: the function `B(j) = ⌈j log₂ 3⌉`.

## Main results

* `CollatzPosDens.ceilLog3_le_iff`: `B(j) ≤ n ↔ 3 ^ j ≤ 2 ^ n`.
* `CollatzPosDens.mul_logb_le_ceilLog3`, `CollatzPosDens.ceilLog3_lt_mul_logb_add_one`:
  `j log₂ 3 ≤ B(j) < j log₂ 3 + 1`.
* `CollatzPosDens.ceilLog3_eq_clog`: `B(j) = Nat.clog 2 (3 ^ j)`.
* `CollatzPosDens.three_pow_le_two_pow_ceilLog3`: `3 ^ j ≤ 2 ^ B(j)`.
* `CollatzPosDens.three_pow_lt_two_pow_ceilLog3`: `3 ^ j < 2 ^ B(j)` for `0 < j`.
* `CollatzPosDens.two_pow_ceilLog3_lt`: `2 ^ B(j) < 2 * 3 ^ j`.
* `CollatzPosDens.two_pow_nineteen_mul_div_twelve_le_three_pow`: `2 ^ ⌊19u/12⌋ ≤ 3 ^ u`.
* `CollatzPosDens.ceilLog3_eq_ceilLog3Nat`: `B(j)` equals its computable form `ceilLog3Nat j`.

## Implementation notes

Since `j log₂ 3 ≥ 0`, the ceiling is taken in `ℕ` (`Nat.ceil`), so that `B(j)` can be used
directly as an exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded logarithm `B(j) = ⌈j log₂ 3⌉`, as a natural number. -/
@[collatz_pos_dens "def_ceil_log3"]
noncomputable def ceilLog3 (j : ℕ) : ℕ :=
  ⌈(j : ℝ) * Real.logb 2 3⌉₊

/-- `j log₂ 3 ≤ n` exactly when `3 ^ j ≤ 2 ^ n`. -/
theorem mul_logb_two_three_le_iff (j n : ℕ) :
    (j : ℝ) * Real.logb 2 3 ≤ n ↔ 3 ^ j ≤ 2 ^ n := by
  rw [← Real.logb_pow, Real.logb_le_iff_le_rpow (by norm_num) (by positivity),
    Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- `B(j) ≤ n` exactly when `3 ^ j ≤ 2 ^ n`. -/
theorem ceilLog3_le_iff {j n : ℕ} : ceilLog3 j ≤ n ↔ 3 ^ j ≤ 2 ^ n := by
  rw [ceilLog3, Nat.ceil_le, mul_logb_two_three_le_iff]

/-- `j log₂ 3 ≤ B(j)`. -/
theorem mul_logb_le_ceilLog3 (j : ℕ) : (j : ℝ) * Real.logb 2 3 ≤ ceilLog3 j :=
  Nat.le_ceil _

/-- `B(j) < j log₂ 3 + 1`. -/
theorem ceilLog3_lt_mul_logb_add_one (j : ℕ) :
    (ceilLog3 j : ℝ) < j * Real.logb 2 3 + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg j.cast_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)))

/-- `B(j)` is the ceiling base-`2` logarithm of `3 ^ j`. -/
theorem ceilLog3_eq_clog (j : ℕ) : ceilLog3 j = Nat.clog 2 (3 ^ j) :=
  eq_of_forall_ge_iff fun _ => by
    rw [ceilLog3_le_iff, Nat.clog_le_iff_le_pow one_lt_two]

/-- `B(0) = 0`. -/
@[simp]
theorem ceilLog3_zero : ceilLog3 0 = 0 := by
  simp [ceilLog3]

/-- `3 ^ j ≤ 2 ^ B(j)`. -/
theorem three_pow_le_two_pow_ceilLog3 (j : ℕ) : 3 ^ j ≤ 2 ^ ceilLog3 j :=
  ceilLog3_le_iff.1 le_rfl

/-- `B(j)` is positive for positive `j`. -/
theorem ceilLog3_pos {j : ℕ} (hj : 0 < j) : 0 < ceilLog3 j := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have h1 : 1 < 3 ^ j := Nat.one_lt_pow hj.ne' (by norm_num)
  have := three_pow_le_two_pow_ceilLog3 j
  rw [h0] at this
  omega

/-- `3 ^ j < 2 ^ B(j)` for positive `j`. -/
theorem three_pow_lt_two_pow_ceilLog3 {j : ℕ} (hj : 0 < j) : 3 ^ j < 2 ^ ceilLog3 j := by
  refine lt_of_le_of_ne (three_pow_le_two_pow_ceilLog3 j) fun h => ?_
  have : Odd (3 ^ j) := Odd.pow (by decide)
  rw [h] at this
  exact Nat.not_even_iff_odd.2 this ((Nat.even_pow' (ceilLog3_pos hj).ne').2 even_two)

/-- `2 ^ B(j) < 2 * 3 ^ j`. -/
theorem two_pow_ceilLog3_lt (j : ℕ) : 2 ^ ceilLog3 j < 2 * 3 ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have h1 : 1 < 3 ^ j := Nat.one_lt_pow hj.ne' (by norm_num)
  have h := Nat.pow_pred_clog_lt_self one_lt_two h1
  rw [← ceilLog3_eq_clog, Nat.pred_eq_sub_one] at h
  calc 2 ^ ceilLog3 j = 2 * 2 ^ (ceilLog3 j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (ceilLog3_pos hj)]
    _ < 2 * 3 ^ j := by omega

/-- `2 ^ ⌊19u/12⌋ ≤ 3 ^ u` for every natural number `u`. -/
theorem two_pow_nineteen_mul_div_twelve_le_three_pow (u : ℕ) : 2 ^ (19 * u / 12) ≤ 3 ^ u := by
  refine (Nat.pow_le_pow_iff_left (show 12 ≠ 0 by norm_num)).1 ?_
  calc (2 ^ (19 * u / 12)) ^ 12 = 2 ^ (12 * (19 * u / 12)) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (19 * u) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le _ _)
    _ = (2 ^ 19) ^ u := by rw [pow_mul]
    _ ≤ (3 ^ 12) ^ u := Nat.pow_le_pow_left (by norm_num) u
    _ = (3 ^ u) ^ 12 := by rw [← pow_mul, ← pow_mul, mul_comm]

/-- `B(j)` equals its computable form `ceilLog3Nat j`, defined with `Nat.log2`. -/
theorem ceilLog3_eq_ceilLog3Nat (j : ℕ) : ceilLog3 j = ceilLog3Nat j := by
  unfold ceilLog3Nat
  split_ifs with hj
  · exact hj ▸ ceilLog3_zero
  refine le_antisymm (ceilLog3_le_iff.2 Nat.lt_log2_self.le) ?_
  have h := (Nat.log2_self_le (by positivity)).trans_lt
    (three_pow_lt_two_pow_ceilLog3 (Nat.pos_of_ne_zero hj))
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h

end CollatzPosDens
