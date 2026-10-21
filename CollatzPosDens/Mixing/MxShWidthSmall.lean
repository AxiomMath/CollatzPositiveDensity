/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Mixing.MxShWidthUpper

/-!
# The half-width of the shell window is small

For every natural number `n` with `CollatzPosDens.mxGateLevel ≤ n`, where
`CollatzPosDens.mxGateLevel = 2 ^ 80`, the half-width `h^sh_n = ⌈√(128 n log n)⌉` of the shell
window satisfies `21600 h^sh_n ≤ n`.

By `CollatzPosDens.shWidth_le_rpow`, `21600 h^sh_n ≤ 280800 n^{9/16}`, and
`280800 ≤ 2^35 = (2^80)^{7/16} ≤ n^{7/16}`, so `280800 n^{9/16} ≤ n^{9/16} n^{7/16} = n`.

## Main results

* `CollatzPosDens.mul_shWidth_le`: for `mxGateLevel ≤ n`, `21600 h^sh_n ≤ n`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every natural number `n ≥ mxGateLevel`, the half-width of the shell window satisfies
`21600 * shWidth n ≤ n`. -/
@[collatz_pos_dens "lem_mx_sh_h_small"]
theorem mul_shWidth_le {n : ℕ} (hn : mxGateLevel ≤ n) : 21600 * shWidth n ≤ n := by
  rw [mxGateLevel_def] at hn
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : (2 : ℝ) ^ 35 ≤ (n : ℝ) ^ (7 / 16 : ℝ) := by
    have h : ((2 : ℝ) ^ 80) ^ (7 / 16 : ℝ) = 2 ^ 35 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h]
    exact Real.rpow_le_rpow (by positivity) hn' (by norm_num)
  have hsplit : (n : ℝ) ^ (9 / 16 : ℝ) * (n : ℝ) ^ (7 / 16 : ℝ) = n := by
    rcases hn0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [← Real.rpow_add hpos]; norm_num
  have hy0 : 0 ≤ (n : ℝ) ^ (9 / 16 : ℝ) := by positivity
  have hup := shWidth_le_rpow hn
  have : (21600 * shWidth n : ℝ) ≤ n := by
    calc (21600 * shWidth n : ℝ) ≤ 21600 * (13 * (n : ℝ) ^ (9 / 16 : ℝ)) := by gcongr
      _ = 280800 * (n : ℝ) ^ (9 / 16 : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (9 / 16 : ℝ) * (n : ℝ) ^ (7 / 16 : ℝ) := by
        rw [mul_comm]; gcongr; linarith [show (280800 : ℝ) ≤ 2 ^ 35 by norm_num]
      _ = n := hsplit
  exact_mod_cast this

end CollatzPosDens
