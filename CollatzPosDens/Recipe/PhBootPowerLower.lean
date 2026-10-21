/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhLogChain
public import CollatzPosDens.Transfer.S02Amix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A lower bound for the bootstrap chaining power

Let `c_bt = 1079/1000` be the ratio of the bootstrap chaining and `a := a_mx(b) = 29/20` the
profile exponent at the bootstrap index. Then
$$c_{\mathrm{bt}}^{\,a} > \frac{1116557504}{10^9}$$
(positive real power). Indeed `c_bt^a = exp(a log c_bt)`, and the enclosure
`log c_bt > 76034686275/10^12` gives `a log c_bt > x := 88200236079/(8 · 10^11)`; the partial
sum of the exponential series of degree `8` at `x` is `1.11655750435775138… ≥ 1116557504/10^9`.

## Main results

* `CollatzPosDens.lt_bootChainRatio_rpow_amix_b`: `1116557504/10^9 < c_bt ^ a_mx(b)`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Lower bound for the bootstrap chaining power.**
`1116557504/10^9 < c_bt ^ a_mx(b)` for the ratio `c_bt` of the bootstrap chaining and the profile
exponent `a_mx(b)` at the bootstrap index (positive real power). -/
@[collatz_pos_dens "lem_ph_boot_power_lower"]
theorem lt_bootChainRatio_rpow_amix_b :
    (1116557504 / 10 ^ 9 : ℝ) < (bootChainRatio : ℝ) ^ (amix .b : ℝ) := by
  have hc : (0 : ℝ) < bootChainRatio := by rw [bootChainRatio_cast]; norm_num
  have hlog := log_bootChainRatio_mem_Ioo.1
  rw [rpow_def_of_pos hc, amix_cast_b]
  set x : ℝ := 88200236079 / (8 * 10 ^ 11) with hx
  have hx0 : 0 ≤ x := by rw [hx]; norm_num
  have hxlt : x < log (bootChainRatio : ℝ) * (29 / 20) := by rw [hx]; linarith
  have hsum := Real.sum_le_exp_of_nonneg hx0 9
  have hval : (1116557504 / 10 ^ 9 : ℝ) ≤ ∑ i ∈ Finset.range 9, x ^ i / (i.factorial : ℝ) := by
    rw [hx]; norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hval.trans_lt (hsum.trans_lt (exp_lt_exp.2 hxlt))

end CollatzPosDens
