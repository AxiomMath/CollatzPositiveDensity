/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShGate
public import CollatzPosDens.Mixing.MxShHLower
public import CollatzPosDens.Mixing.MxShJ
public import CollatzPosDens.Mixing.MxShKhi
public import CollatzPosDens.Mixing.MxShKlo
public import CollatzPosDens.Mixing.MxShTail8

/-!
# Size of a retained gate of the shell cut

Let `n ≥ n₀` (the mixing gate level `n₀ = mxGateLevel = 2 ^ 80`), let `d` lie in the shell window
`k^{sh,-}_n ≤ d ≤ k^{sh,+}_n - 1`, and let `j ∈ ℕ` with `j ≤ J^{sh}_n`. With `H = H^{sh}_n`, the
gate `(d, j)` has at most
$$\#\mathrm{Hd}^{\mathrm{sh}}_n(d,j) \le \binom{H-1}{d}\min(1, 2^{4-j})$$
exposed patterns.

The set `Hd^{sh}_n(d, j)` consists of `d`-element subsets of `{1, …, H - 1}`, so it has at most
`C(H-1, d)` elements; this is the claim for `j ≤ 4`. For `j ≥ 5`, every exposed pattern `β` has
`Of(β) ≥ 2^{j-1}`, and the tail bound `CollatzPosDens.card_setOffset_ge_le_eight_div` with
`N = H - 1` and `x = 2^{j-1}` bounds the number of such `d`-subsets by `2^{4-j} C(H-1, d)`.

## Main results

* `CollatzPosDens.card_shRetainedHeads_le`: the bound above.

## Implementation notes

The bound is stated in `ℝ`, and `2^{4-j}` is the integer power `(2 : ℝ) ^ (4 - j : ℤ)`. The window
condition on the integer `d` is stated with `d : ℕ` and integer comparisons with
`k^{sh,±}_n ∈ ℤ`; under the other hypotheses `k^{sh,-}_n ≥ 1`, so no generality is lost.

## References

* [Mazur, *Collatz positive density*, §12.11]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `1 ≤ j ≤ J^{sh}_n` and `n ≥ 1`, the lower end `2^{j-1}` of the shell `I^{sh}_j` is below
`n ^ 2`. -/
private theorem two_pow_pred_lt_sq_of_le_shJ {n j : ℕ} (hn : 1 ≤ n) (hj1 : 1 ≤ j)
    (hj : j ≤ shJ n) : (2 : ℝ) ^ (j - 1) < (n : ℝ) ^ 2 := by
  have hJ := shJ_lt_add_one n
  have hjR : (j : ℝ) ≤ shJ n := by exact_mod_cast hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : ((j - 1 : ℕ) : ℝ) < Real.logb 2 ((n : ℝ) ^ 2) := by
    rw [Real.logb_pow, Nat.cast_sub hj1, Nat.cast_one]
    push_cast
    linarith
  have := (Real.lt_logb_iff_rpow_lt one_lt_two (by positivity)).1 hlt
  rwa [Real.rpow_natCast] at this

/-- **Size of a retained gate.** Let `mxGateLevel ≤ n`, `k^{sh,-}_n ≤ d ≤ k^{sh,+}_n - 1` and
`j ≤ J^{sh}_n`. Then, with `H = H^{sh}_n`, `#Hd^{sh}_n(d, j) ≤ C(H-1, d) min(1, 2^{4-j})`. -/
@[collatz_pos_dens "lem_mx_sh_gate_mass"]
theorem card_shRetainedHeads_le {n d j : ℕ} (hn : mxGateLevel ≤ n) (hklo : shKLo n ≤ d)
    (hkhi : (d : ℤ) ≤ shKHi n - 1) (hj : j ≤ shJ n) :
    (#(shRetainedHeads n d j) : ℝ) ≤
      ((shHeight n - 1).choose d : ℝ) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ))) := by
  have hn' := hn
  rw [mxGateLevel_def] at hn'
  set H := shHeight n with hHdef
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn'
  have hnR : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn'
  have hHlow := shHeight_lower n
  rw [← hHdef] at hHlow
  have hN : 3 * n ≤ 2 * (H - 1) := by
    have : (3 : ℝ) * n + 2 ≤ 2 * H := by nlinarith
    have : 3 * n + 2 ≤ 2 * H := by exact_mod_cast this
    omega
  have hchoose : (#(shRetainedHeads n d j) : ℝ) ≤ ((H - 1).choose d : ℝ) := by
    exact_mod_cast card_shRetainedHeads_le_choose n d j
  rcases le_or_gt j 4 with hj4 | hj4
  · have hmin : min 1 ((2 : ℝ) ^ (4 - (j : ℤ))) = 1 := by
      refine min_eq_left ?_
      rw [show (4 - (j : ℤ)) = ((4 - j : ℕ) : ℤ) by omega, zpow_natCast]
      exact one_le_pow₀ one_le_two
    rwa [hmin, mul_one]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hzpow : (2 : ℝ) ^ (4 - ((i + 1 : ℕ) : ℤ)) = 8 / 2 ^ i := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 3 := ⟨i - 3, by omega⟩
    rw [show (4 - ((m + 3 + 1 : ℕ) : ℤ)) = -(m : ℤ) by omega, zpow_neg, zpow_natCast, pow_add]
    field_simp
    norm_num
  have hmin : min 1 ((2 : ℝ) ^ (4 - ((i + 1 : ℕ) : ℤ))) = 8 / 2 ^ i := by
    rw [hzpow]
    refine min_eq_right ?_
    rw [div_le_one (by positivity)]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ i := pow_le_pow_right₀ one_le_two (by omega)
  rw [hmin]
  have hd : |2 * (d : ℤ) - ((H - 1 : ℕ) : ℤ)| ≤ 2 * shWidth n + 4 := by
    have h1 := shKLo_eq n
    have h2 := shKHi_eq n
    rw [← hHdef] at h1 h2
    rw [abs_le]
    constructor <;> omega
  have hx : (2 : ℝ) ^ i ≤ 2 * (n : ℝ) ^ 2 := by
    have := two_pow_pred_lt_sq_of_le_shJ hn1 (Nat.le_add_left 1 i) hj
    rw [Nat.add_sub_cancel] at this
    nlinarith
  have htail := card_setOffset_ge_le_eight_div hn hN hd (by positivity) hx
  have hsub : shRetainedHeads n d (i + 1) ⊆
      {S ∈ powersetCard d (Icc 1 (H - 1)) | (2 : ℝ) ^ i ≤ (setOffset S : ℝ)} := by
    intro β hβ
    obtain ⟨h1, h2, h3⟩ := mem_shRetainedHeads.1 hβ
    exact mem_filter.2 ⟨mem_powersetCard.2 ⟨h1, h2⟩, le_of_mem_mxShShell_succ h3⟩
  have hcard : (#(shRetainedHeads n d (i + 1)) : ℝ) ≤
      #{S ∈ powersetCard d (Icc 1 (H - 1)) | (2 : ℝ) ^ i ≤ (setOffset S : ℝ)} := by
    exact_mod_cast card_le_card hsub
  calc (#(shRetainedHeads n d (i + 1)) : ℝ)
      ≤ 8 / 2 ^ i * ((H - 1).choose d : ℝ) := hcard.trans htail
    _ = ((H - 1).choose d : ℝ) * (8 / 2 ^ i) := mul_comm _ _

end CollatzPosDens
