/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnHoldVpgf
public import CollatzPosDens.Transfer.S02Ycl
public import CollatzPosDens.Transfer.S02Vcl
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The vertical generating function of a hold at the clearing point

For each Fourier index `ι ∈ 𝔍` write `y = y_cl(ι)` and `v = v_cl(ι)`, so that
`(y, v) = (8191/8192, 1279/100)` for `ι = o` and `(y, v) = (255/256, 25/2)` for `ι = b`. In both
cases `0 < y < 2` and the non-closing weight `V_nc(y) = y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵` is
below `1`:
`V_nc(8191/8192) = 13614318431135259681796091905/19811876626992448094437638144` and
`V_nc(255/256) = 393511316155005825/580973148023816192`. The closed form of `𝖵` then gives exact
rational values `𝖵(y) = a / b`:

* for `ι = o`, `a = 6187886789300271379243896831`, `b = 6197558195857188412641546239`;
* for `ι = b`, `a = 178454632614069375`, `b = 187461831868810367`.

The inequality `𝖵(y) < y ^ v` is equivalent to an integer inequality between positive integers:
`a^100 · 8192^1279 < b^100 · 8191^1279` for `ι = o` (ratio `0.99996…`) and
`a^2 · 256^25 < b^2 · 255^25` for `ι = b` (ratio `0.99936…`).

## Main results

* `CollatzPosDens.holdVpgf_clearingPoint_eq_o`, `CollatzPosDens.holdVpgf_clearingPoint_eq_b`:
  the exact values of `𝖵(y_cl(ι))`.
* `CollatzPosDens.holdVpgf_clearingPoint_lt`: `𝖵(y_cl(ι)) < y_cl(ι) ^ v_cl(ι)` for every `ι`.

## Implementation notes

`𝖵` takes values in `[0, ∞]`; the right-hand side `y_cl(ι) ^ v_cl(ι)` is the real power
(`Real.rpow`) embedded by `ENNReal.ofReal`. The integer inequalities are checked in `ℕ` by the
kernel; their exponents are small.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The exact value at the original index,
`𝖵(y_cl(o)) = 6187886789300271379243896831/6197558195857188412641546239`. -/
theorem holdVpgf_clearingPoint_eq_o :
    holdVpgf (clearingPoint .o : ℝ) =
      ENNReal.ofReal (6187886789300271379243896831 / 6197558195857188412641546239) := by
  rw [clearingPoint_cast_o, holdVpgf_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The exact value at the bootstrap index,
`𝖵(y_cl(b)) = 178454632614069375/187461831868810367`. -/
theorem holdVpgf_clearingPoint_eq_b :
    holdVpgf (clearingPoint .b : ℝ) =
      ENNReal.ofReal (178454632614069375 / 187461831868810367) := by
  rw [clearingPoint_cast_b, holdVpgf_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- If `0 ≤ x`, `0 ≤ y`, `0 < d` and `x ^ d < y ^ k`, then `x < y ^ (k / d)`. -/
private lemma lt_rpow_div_of_pow_lt_vpgfClear {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k d : ℕ}
    (hd : d ≠ 0) (h : x ^ d < y ^ k) : x < y ^ ((k : ℝ) / d) := by
  calc x = (x ^ d) ^ ((d : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hx hd).symm
    _ < (y ^ k) ^ ((d : ℝ)⁻¹) :=
        Real.rpow_lt_rpow (by positivity) h (by positivity)
    _ = y ^ ((k : ℝ) / d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy, div_eq_mul_inv]

/-- **The vertical generating function at the clearing point.** For every Fourier index `ι`,
`𝖵(y_cl(ι)) < y_cl(ι) ^ v_cl(ι)`. -/
@[collatz_pos_dens "lem_tr_vpgf_clear"]
theorem holdVpgf_clearingPoint_lt (ι : FIndex) :
    holdVpgf (clearingPoint ι : ℝ) <
      ENNReal.ofReal ((clearingPoint ι : ℝ) ^ (clearingPower ι : ℝ)) := by
  have hy0 : (0 : ℝ) < clearingPoint ι := by exact_mod_cast clearingPoint_pos ι
  cases ι with
  | o =>
    rw [holdVpgf_clearingPoint_eq_o, ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hy0 _),
      clearingPower_cast_o]
    have key : (6187886789300271379243896831 : ℕ) ^ 100 * 8192 ^ 1279 <
        8191 ^ 1279 * 6197558195857188412641546239 ^ 100 := by decide +kernel
    have h := lt_rpow_div_of_pow_lt_vpgfClear (x := 6187886789300271379243896831 /
      6197558195857188412641546239) (by norm_num) hy0.le (k := 1279) (d := 100) (by norm_num) (by
        rw [clearingPoint_cast_o, div_pow, div_pow,
          div_lt_div_iff₀ (by positivity) (by positivity)]
        exact_mod_cast key)
    exact_mod_cast h
  | b =>
    rw [holdVpgf_clearingPoint_eq_b, ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hy0 _),
      clearingPower_cast_b]
    have key : (178454632614069375 : ℕ) ^ 2 * 256 ^ 25 <
        255 ^ 25 * 187461831868810367 ^ 2 := by decide +kernel
    have h := lt_rpow_div_of_pow_lt_vpgfClear (x := 178454632614069375 / 187461831868810367)
      (by norm_num) hy0.le (k := 25) (d := 2) (by norm_num) (by
        rw [clearingPoint_cast_b, div_pow, div_pow,
          div_lt_div_iff₀ (by positivity) (by positivity)]
        exact_mod_cast key)
    exact_mod_cast h

end CollatzPosDens
