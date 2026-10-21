/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Mixing.MxShWidth
public import CollatzPosDens.Mixing.MxShLogUpper

/-!
# An upper bound for the half-width of the shell window

For every integer `n ≥ n₀`, where `n₀ = mxGateLevel = 2 ^ 80` is the mixing gate level, the
half-width `h^sh_n = ⌈√(128 n log n)⌉` of the shell window satisfies `h^sh_n ≤ 13 n^{9/16}`.

Since `0 ≤ log n ≤ n^{1/8}` on this range, `128 n log n ≤ 128 n^{9/8} ≤ (12 n^{9/16})^2`, so
`√(128 n log n) ≤ 12 n^{9/16}`. As `⌈u⌉ < u + 1` and `1 ≤ n^{9/16}`,
`h^sh_n < 12 n^{9/16} + 1 ≤ 13 n^{9/16}`.

## Main results

* `CollatzPosDens.shWidth_le_rpow`: for `n₀ ≤ n`, `h^sh_n ≤ 13 n^{9/16}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `n ≥ mxGateLevel`, the half-width of the shell window satisfies
`h^sh_n ≤ 13 n^{9/16}`. -/
@[collatz_pos_dens "lem_mx_sh_h_upper"]
theorem shWidth_le_rpow {n : ℕ} (hn : mxGateLevel ≤ n) :
    (shWidth n : ℝ) ≤ 13 * (n : ℝ) ^ (9 / 16 : ℝ) := by
  rw [mxGateLevel_def] at hn
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := le_trans (one_le_pow₀ (by norm_num)) hn'
  set y : ℝ := (n : ℝ) ^ (9 / 16 : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : 1 ≤ y := Real.one_le_rpow hn1 (by norm_num)
  have hsq : y ^ 2 = n * (n : ℝ) ^ (1 / 8 : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
    rw [show (9 / 16 : ℝ) * (2 : ℕ) = 1 + 1 / 8 by norm_num, Real.rpow_add (by linarith),
      Real.rpow_one]
  have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 8 : ℝ) := log_le_rpow_one_div_eight (by exact_mod_cast hn)
  have hsqrt : Real.sqrt (128 * n * Real.log n) ≤ 12 * y := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 128 * (n : ℝ) * Real.log n ≤ 128 * (n * (n : ℝ) ^ (1 / 8 : ℝ)) := by
      rw [mul_assoc]; gcongr
    nlinarith
  have := shWidth_lt_sqrt_add_one n
  linarith

end CollatzPosDens
