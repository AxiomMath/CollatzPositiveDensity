/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxWindowHigh
public import CollatzPosDens.Mixing.MxWindowLow

/-!
# Width of the crossing window

The window of levels around the crossing level `Lv_n = CollatzPosDens.mxLevel n` runs from
$q^-_n = \lfloor \tfrac12 \mathrm{Lv}_n - \tfrac14 n^{2049/4096} \rfloor$ to
$q^+_n = \lceil \tfrac12 \mathrm{Lv}_n + \tfrac14 n^{2049/4096} \rceil$. Since rounding moves a
real number by less than one, $q^+_n - q^-_n < \tfrac12 n^{2049/4096} + 2$, and this is at most
$n^{2049/4096}$ as soon as $n^{2049/4096} \ge 4$, which holds for every $n \ge 16$.

## Main results

* `CollatzPosDens.mxWindowHigh_sub_mxWindowLow_lt`: `q^+_n - q^-_n < n^{2049/4096} / 2 + 2`
  for every `n`.
* `CollatzPosDens.four_le_rpow_of_sixteen_le`: `4 ≤ n^{2049/4096}` for `n ≥ 16`.
* `CollatzPosDens.mxWindowHigh_sub_mxWindowLow_le_of_sixteen_le`: the width bound
  `q^+_n - q^-_n ≤ n^{2049/4096}` for `n ≥ 16`.
* `CollatzPosDens.mxWindowHigh_sub_mxWindowLow_le`: the width bound for `n ≥ 2^131072`.

## Implementation notes

The hypothesis `n ≥ 2^131072` is used only to get `n^{2049/4096} ≥ 4`; the bound is proved
under the weaker hypothesis `n ≥ 16`, and the form with `n ≥ 2^131072` is deduced from it.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The window width is less than `n^{2049/4096} / 2 + 2`, for every `n`. -/
theorem mxWindowHigh_sub_mxWindowLow_lt (n : ℕ) :
    ((mxWindowHigh n - mxWindowLow n : ℤ) : ℝ) <
      (1 / 2 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) + 2 := by
  push_cast
  linarith [mxWindowHigh_lt n, lt_mxWindowLow n]

/-- For `n ≥ 16`, `n^{2049/4096} ≥ 4`. -/
theorem four_le_rpow_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    (4 : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) := by
  calc (4 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
    _ ≤ (16 : ℝ) ^ ((2049 : ℝ) / 4096) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn) (by norm_num)

/-- Width of the window, for `n ≥ 16`: `q^+_n - q^-_n ≤ n^{2049/4096}`. -/
theorem mxWindowHigh_sub_mxWindowLow_le_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    ((mxWindowHigh n - mxWindowLow n : ℤ) : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) := by
  linarith [mxWindowHigh_sub_mxWindowLow_lt n, four_le_rpow_of_sixteen_le hn]

/-- **Width of the window.** For every integer `n ≥ 2^131072`, `q^+_n - q^-_n ≤ n^{2049/4096}`. -/
@[collatz_pos_dens "lem_mx_window_count"]
theorem mxWindowHigh_sub_mxWindowLow_le {n : ℕ} (hn : 2 ^ 131072 ≤ n) :
    ((mxWindowHigh n - mxWindowLow n : ℤ) : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) :=
  mxWindowHigh_sub_mxWindowLow_le_of_sixteen_le
    ((pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 4 ≤ 131072)).trans hn)

end CollatzPosDens
