/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrRaw3Cap
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-!
# The raw-three cap on the infinite ray

For every integer `s ≥ 512` the cap of the raw-three crossing factor satisfies `ς_s < 1/50`.

Write `s = 16k + s'` with `k ≥ 32` and `0 ≤ s' < 16`. Then the exit width is
`f_s = 5k + 1 + ⌊5s'/16⌋`, and the sixteen inequalities `9^{⌊5s'/16⌋} ≤ 2^{s'}` give
`9^{f_s} 2^{-s} ≤ 9 (9^5/2^{16})^k ≤ 9 (9^5/2^{16})^{32}`, since `9^5 = 59049 < 65536 = 2^{16}`.
An exact rational comparison gives `(99/7) ε_* (9^5/2^{16})^{32} < 1/50`, and `2^{-16} < 1/50`.

## Main results

* `CollatzPosDens.nine_pow_bkExitWidth_mul_le`: `9^{f_s} 2^{512} ≤ 9^{161} 2^s` for `s ≥ 512`.
* `CollatzPosDens.trRaw3Cap_lt_one_div_fifty`: `ς_s < 1/50` for `s ≥ 512`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `s ≥ 512`, `9^{f_s} 2^{512} ≤ 9^{161} 2^s`, i.e. `9^{f_s} 2^{-s} ≤ 9 (9^5/2^{16})^{32}`. -/
theorem nine_pow_bkExitWidth_mul_le {s : ℕ} (hs : 512 ≤ s) :
    9 ^ bkExitWidth s * 2 ^ 512 ≤ 9 ^ 161 * 2 ^ s := by
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 16 ∧ s = 16 * (32 + j) + r :=
    ⟨s / 16 - 32, s % 16, Nat.mod_lt _ (by norm_num), by omega⟩
  have hf : bkExitWidth (16 * (32 + j) + r) = 5 * j + 1 + 5 * r / 16 + 160 := by
    rw [bkExitWidth_def]; omega
  have hr' : 9 ^ (5 * r / 16) ≤ 2 ^ r := by interval_cases r <;> norm_num
  have hj : 9 ^ (5 * j) ≤ 2 ^ (16 * j) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) j
  rw [hf]
  calc 9 ^ (5 * j + 1 + 5 * r / 16 + 160) * 2 ^ 512
      = 9 ^ 161 * 2 ^ 512 * (9 ^ (5 * j) * 9 ^ (5 * r / 16)) := by
        rw [show 5 * j + 1 + 5 * r / 16 + 160 = 161 + (5 * j + 5 * r / 16) by omega, pow_add,
          pow_add, mul_comm (9 ^ 161) _, mul_assoc, mul_left_comm, mul_assoc (9 ^ 161) (2 ^ 512)]
        exact congrArg _ (mul_comm _ _)
    _ ≤ 9 ^ 161 * 2 ^ 512 * (2 ^ (16 * j) * 2 ^ r) := by gcongr
    _ = 9 ^ 161 * 2 ^ (16 * (32 + j) + r) := by
        rw [show 16 * (32 + j) + r = 512 + (16 * j + r) by omega, pow_add 2 512, pow_add 2 (16 * j),
          mul_assoc]

/-- On the infinite ray `s ≥ 512` the cap of the raw-three crossing factor is below `1/50`. -/
@[collatz_pos_dens "lem_tr_raw3_cap_ray"]
theorem trRaw3Cap_lt_one_div_fifty {s : ℕ} (hs : 512 ≤ s) : trRaw3Cap s < 1 / 50 := by
  have key : ((9 : ℚ) ^ bkExitWidth s * 2 ^ 512 ≤ 9 ^ 161 * 2 ^ s) := by
    exact_mod_cast nine_pow_bkExitWidth_mul_le hs
  have hpow : (9 : ℚ) ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ)) ≤ 9 ^ 161 / 2 ^ 512 := by
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    exact key
  refine (trRaw3Cap_le_max s).trans_lt (max_lt (by norm_num) ?_)
  calc 11 / 7 * epsStar * 9 ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ))
      = 11 / 7 * epsStar * (9 ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ))) := by ring
    _ ≤ 11 / 7 * epsStar * (9 ^ 161 / 2 ^ 512) := by
      gcongr
      exact mul_nonneg (by norm_num) epsStar_pos.le
    _ < 1 / 50 := by
      rw [epsStar_eq]
      set_option exponentiation.threshold 512 in norm_num

end CollatzPosDens
