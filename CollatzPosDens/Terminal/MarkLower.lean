/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.TailMargin
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Recipe.ZMargin
public import CollatzPosDens.Recipe.ZMarginRoom
public import CollatzPosDens.Seed.ZTail
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Terminal.S06Tj
public import CollatzPosDens.Terminal.S06TerminalSmall
public import CollatzPosDens.Terminal.TerminalTransport

/-!
# Lower bound for the marked mass

Let `t ≥ t_min` (`targetFloor`) be an odd integer with `Z_{N_*}(t) > θ_tl + ε_Z`
(`tailMargin + centralSumMargin`), let `j ≥ J_c` (`covGen`), and let `X` be admissible for
generation `j`. Then the marked mass satisfies `Θ_{j,X}(t) > 2^{-29}`.

Since `N_* ≤ J_c ≤ j`, the tail bound gives `Z_j(t) > ε_Z`. Terminal transport bounds
`|Θ_{j,X}(t) - Z_j(t)|` by the terminal majorant `T_j`, which is `< 2^{-29}` for `j ≥ J_c`.
Hence `Θ_{j,X}(t) > ε_Z - 2^{-29} ≥ 2^{-29}`, the last step because
`2^{-29} + 2^{-29} ≤ ε_Z`.

## Main results

* `CollatzPosDens.abs_markedMass_sub_weightedCentralSum_lt`: `|Θ_{j,X}(t) - Z_j(t)| < 2^{-29}`
  for odd `t ≥ t_min`, `j ≥ J_c` and `X` admissible for generation `j`.
* `CollatzPosDens.two_zpow_neg_twentyNine_lt_markedMass`: `2^{-29} < Θ_{j,X}(t)`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For an odd integer `t ≥ targetFloor`, `j ≥ covGen` and `X` admissible for generation `j`,
`|Θ_{j,X}(t) - Z_j(t)| < 2^{-29}`. -/
@[collatz_pos_dens "lem_terminal_step"]
theorem abs_markedMass_sub_weightedCentralSum_lt {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {j : ℕ} (hj : covGen ≤ j) {X : ℝ}
    (hX : IsAdmissibleScale t j X) :
    |markedMass j X t - weightedCentralSum j t| < (2 : ℝ) ^ (-29 : ℝ) :=
  (abs_markedMass_sub_weightedCentralSum_le hodd ht hj hX).trans_lt (terminalMajorant_lt hj)

/-- Let `t ≥ targetFloor` be an odd integer with `Z_{N_*}(t) > tailMargin + centralSumMargin`,
let `j ≥ covGen`, and let `X` be admissible for generation `j`. Then `Θ_{j,X}(t) > 2^{-29}`. -/
@[collatz_pos_dens "lem_mark_lower"]
theorem two_zpow_neg_twentyNine_lt_markedMass {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t)
    (hZ : (tailMargin : ℝ) + centralSumMargin < weightedCentralSum generationThreshold t)
    {j : ℕ} (hj : covGen ≤ j) {X : ℝ} (hX : IsAdmissibleScale t j X) :
    (2 : ℝ) ^ (-29 : ℤ) < markedMass j X t := by
  have hNj : generationThreshold ≤ j := selEnd_le_generationThreshold_range.2.trans hj
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast targetFloor_pos) ht
  have hZj := abs_weightedCentralSum_sub_generationThreshold_lt hodd ht0 hZ hNj
  have hT := abs_markedMass_sub_weightedCentralSum_lt hodd ht hj hX
  have e : (2 : ℝ) ^ (-29 : ℝ) = (2 : ℝ)⁻¹ ^ 29 := by
    rw [show (-29 : ℝ) = ((-29 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg,
      inv_pow, zpow_ofNat]
  have hroom : ((2 : ℝ)⁻¹ ^ 29 + 2⁻¹ ^ 29 : ℝ) ≤ centralSumMargin := by
    have h := (Rat.cast_le (K := ℝ)).2 two_inv_pow_add_two_inv_pow_le_centralSumMargin
    push_cast at h
    rwa [centralSumMargin_cast]
  rw [e, abs_lt] at hT
  rw [zpow_neg, zpow_ofNat, ← inv_pow]
  obtain ⟨hT1, -⟩ := hT
  set a : ℝ := (2 : ℝ)⁻¹ ^ 29
  set Zj := weightedCentralSum j (t : ℚ)
  set T := markedMass j X (t : ℚ)
  set c : ℝ := (centralSumMargin : ℝ)
  clear_value a Zj T c
  linarith

end CollatzPosDens
