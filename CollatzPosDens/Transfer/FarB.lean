/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.B
public import CollatzPosDens.Transfer.Dcap
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.Lb
public import CollatzPosDens.Transfer.LbValue
public import CollatzPosDens.Transfer.EUpper
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Far-scale bound for `m / (log m)^2`

For every real `m ≥ D_sc`, the quantity `m / (log m)^2` exceeds half the square of `B_*`:
`m / (log m)^2 > B_*^2 / 2`.

The function `x ↦ x / (log x)^2` is increasing on `[e^2, ∞)`, and `m ≥ D_sc > D_cap = (B_* L_B)^2`
with `D_cap ≥ e^2`, so it suffices to bound `D_cap / (log D_cap)^2`. Since `B_* < 2^{L_B}` and
`L_B = 17484`, one has `0 < log D_cap = 2 log B_* + 2 log L_B < (7/5) L_B`, whence
`D_cap / (log D_cap)^2 > (25/49) B_*^2 > B_*^2 / 2`.

## Main results

* `CollatzPosDens.sq_Bstar_div_two_lt_div_log_sq`: for real `m ≥ D_sc`,
  `B_*^2 / 2 < m / (log m)^2`.

## Implementation notes

Monotonicity of `x / (log x)^2` is obtained from the antitonicity of `log x / √x` on
`[e^2, ∞)` (`Real.log_div_sqrt_antitoneOn`) by squaring and inverting. The bound on `log L_B`
uses `L_B < 2^{15}`, hence `log L_B < 15 log 2 < 11`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- `exp 2 < 9`. -/
theorem exp_two_lt_nine : exp 2 < 9 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
  nlinarith [exp_pos 1, exp_one_lt_68_div_25]

/-- The function `x ↦ x / (log x) ^ 2` is monotone on `[e ^ 2, ∞)`. -/
theorem div_log_sq_le_div_log_sq {x y : ℝ} (hx : exp 2 ≤ x) (hxy : x ≤ y) :
    x / (log x) ^ 2 ≤ y / (log y) ^ 2 := by
  have h1 : (1 : ℝ) < exp 2 := one_lt_exp_iff.2 two_pos
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hlogx : 0 < log x := log_pos (by linarith)
  have hlogy : 0 < log y := log_pos (by linarith)
  have hanti := log_div_sqrt_antitoneOn (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hxy)) hxy
  simp only at hanti
  have hsq : (log y / √y) ^ 2 ≤ (log x / √x) ^ 2 := pow_le_pow_left₀ (by positivity) hanti 2
  rw [div_pow, div_pow, sq_sqrt hypos.le, sq_sqrt hxpos.le, div_le_div_iff₀ hypos hxpos] at hsq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- For every real `m ≥ D_sc`, `B_*^2 / 2 < m / (log m)^2`. -/
@[collatz_pos_dens "lem_s02_far_B"]
theorem sq_Bstar_div_two_lt_div_log_sq {m : ℝ} (hm : (Dsc : ℝ) ≤ m) :
    (Bstar : ℝ) ^ 2 / 2 < m / (log m) ^ 2 := by
  set B : ℝ := (Bstar : ℝ) with hB
  set L : ℝ := (LB : ℝ) with hL
  set D : ℝ := (Dcap : ℝ) with hD
  have hL' : L = 17484 := by
    rw [hL, LB_eq]
    norm_num
  have hLpos : 0 < L := by rw [hL']; norm_num
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; exact_mod_cast one_le_Bstar
  have hDeq : D = (B * L) ^ 2 := by rw [hD, cast_Dcap]
  have hDm : D ≤ m := by linarith [show (Dcap : ℝ) < Dsc by exact_mod_cast Dcap_lt_Dsc]
  have hD9 : (9 : ℝ) ≤ D := by
    rw [hDeq, hL']
    nlinarith
  have hDe : exp 2 ≤ D := by linarith [exp_two_lt_nine]
  have hlog2 : log 2 < 347 / 500 := lt_trans log_two_lt_d9 (by norm_num)
  have hlogB : log B < L * log 2 := by
    have h : (Bstar : ℝ) < 2 ^ LB := by exact_mod_cast Bstar_lt_two_pow_LB
    have := log_lt_log (by linarith) h
    rwa [log_pow] at this
  have hlogL : log L < 15 * log 2 := by
    have h : L < (2 : ℝ) ^ 15 := by rw [hL']; norm_num
    have := log_lt_log hLpos h
    rwa [log_pow] at this
  have hlogD : log D = 2 * log B + 2 * log L := by
    rw [hDeq, log_pow, log_mul (by linarith) hLpos.ne']
    push_cast
    ring
  have hlogDpos : 0 < log D := log_pos (by linarith)
  have hlogDlt : log D < 7 / 5 * L := by
    rw [hlogD]
    linarith [mul_lt_mul_of_pos_left hlog2 hLpos]
  have hfD : B ^ 2 / 2 < D / (log D) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    have hsq : (log D) ^ 2 < (7 / 5 * L) ^ 2 := pow_lt_pow_left₀ hlogDlt hlogDpos.le two_ne_zero
    have hB2 : 0 < B ^ 2 := by positivity
    calc B ^ 2 / 2 * (log D) ^ 2 < B ^ 2 / 2 * (7 / 5 * L) ^ 2 :=
          mul_lt_mul_of_pos_left hsq (by positivity)
      _ < (B * L) ^ 2 := by nlinarith [mul_pos hB2 (mul_pos hLpos hLpos)]
      _ = D := hDeq.symm
  exact hfD.trans_le (div_log_sq_le_div_log_sq hDe hDm)

end CollatzPosDens
