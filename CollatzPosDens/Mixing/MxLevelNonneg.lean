/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLevel
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Mixing.MxLogBudget
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# The level `Lv_n` is at least `7n/10`

For large `n` the crossing level
$$\mathrm{Lv}_n = n \log_2 3 - \tfrac{9217}{4096} \log_2 n - 2$$
is bounded below by $\tfrac{7}{10} n$; in particular it is nonnegative.

Writing $L = \log n$, the bound $\log 2 > 0.693$ gives
$\tfrac{9217}{4096}\log_2 n + 2 < 4L + 2 \le 5L$ once $L \ge 2$. The logarithmic budget with
$D = 5$, $\eta = \tfrac{3}{10}$ gives $5L \le \tfrac{3}{10} n$, and
$\log_2 3 \ge \tfrac{79}{50} \ge 1$ gives $n \log_2 3 \ge n$, so
$\mathrm{Lv}_n \ge \tfrac{7}{10} n$.

## Main results

* `CollatzPosDens.seven_div_ten_mul_le_mxLevel`: `7/10 · n ≤ Lv_n` for `n ≥ 2 ^ 131072`.
* `CollatzPosDens.seven_div_ten_mul_le_mxLevel_of_two_pow_eighty_le`: the same bound under
  the weaker hypothesis `n ≥ 2 ^ 80`.
* `CollatzPosDens.mxLevel_nonneg`: `0 ≤ Lv_n` for `n ≥ 2 ^ 80`.

## Implementation notes

The argument only uses `n ≥ 2 ^ 80` (so that `log n ≥ 2` and the logarithmic budget applies);
the bound is proved under that hypothesis and specialised to `n ≥ 2 ^ 131072`.

## References

* [Mazur, *Collatz positive density*, §13.5]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `n ≥ 2 ^ 80`, `7/10 · n ≤ Lv_n`. -/
theorem seven_div_ten_mul_le_mxLevel_of_two_pow_eighty_le {n : ℕ} (hn : 2 ^ 80 ≤ n) :
    7 / 10 * (n : ℝ) ≤ mxLevel n := by
  have hlog2 := log_two_bounds.1
  have hL : 80 * Real.log 2 ≤ Real.log n := by
    simpa using Real.log_le_log (by positivity) (by exact_mod_cast hn : ((2 : ℝ) ^ 80) ≤ n)
  have hlogb : 9217 / 4096 * Real.logb 2 n ≤ 4 * Real.log n := by
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  have : 5 * Real.log n ≤ 3 / 10 * n :=
    mul_log_le_mul_of_two_pow_eighty_le hn (by norm_num) (by norm_num)
  have := logb_two_three_bounds.1
  rw [mxLevel_def]
  nlinarith

/-- For every integer `n ≥ 2 ^ 131072`, `7/10 · n ≤ Lv_n`. -/
@[collatz_pos_dens "lem_mx_level_nonneg"]
theorem seven_div_ten_mul_le_mxLevel {n : ℕ} (hn : 2 ^ 131072 ≤ n) :
    7 / 10 * (n : ℝ) ≤ mxLevel n :=
  seven_div_ten_mul_le_mxLevel_of_two_pow_eighty_le
    ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans hn)

/-- For every `n ≥ 2 ^ 80`, the level `Lv_n` is nonnegative. -/
theorem mxLevel_nonneg {n : ℕ} (hn : 2 ^ 80 ≤ n) : 0 ≤ mxLevel n :=
  le_trans (by positivity) (seven_div_ten_mul_le_mxLevel_of_two_pow_eighty_le hn)

end CollatzPosDens
