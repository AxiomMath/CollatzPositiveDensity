/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreeAngle
public import CollatzPosDens.StoppingTrace.TrTreeCertificate
public import CollatzPosDens.StoppingTrace.TrTreeCylinderBound
public import CollatzPosDens.StoppingTrace.TrWhitePolicyValid
public import CollatzPosDens.StoppingTrace.TrZeroDatum
public import CollatzPosDens.StoppingTrace.TrZeroReflect
public import CollatzPosDens.Transfer.S02Dentry

/-!
# The entry kernel at a black point of gap zero

Fix a level `n`, a unit `ξ ∈ G_n` and the colour scale `ε_*`. Let `v ∈ 𝒫` be black with
`gap(v) = 0`. The angles above `v` are governed by an odd integer `m` with `0 < m < 2^17` and a
real `α` with `|α| ≤ 9 ε_* < 1/3`: `ϑ(v + (r, L)) - 9^{r-1} (m + α) / 2^L ∈ ℤ` for `r ≥ 1` and
`0 ≤ L ≤ 17`. The tree certificate, applied to `m` when `m < 2^16` and, through the reflection
`m ↦ 2^17 - m`, `X ↦ 2^17 - X` of the gap-zero tree cost, to `2^17 - m` otherwise, gives reals
`a ≤ α ≤ b` with `F^{cut⁰, W}_{0,0}(m + α) - T^{root}_{0,12} < 77/100`, where
`W = W^{0,12,14}_{m,a,b}`. The pair `(cut⁰, W)` is a tree datum of height `17` and `W` is valid at
`v`, so the tree cylinder bound gives `m_1(v) < 77/100 = 1 - d_entry`.

## Main results

* `CollatzPosDens.trKernel_one_lt_one_sub_dEntry_of_trGap_eq_zero`: for a black point `v` of gap
  zero, `m_1(v) < 1 - d_entry`.

## Implementation notes

The number `m_1(v)` lies in `[0, ∞]`; the bound is stated as
`m_1(v) < ENNReal.ofReal (1 - d_entry)`. Black points are points of `𝒫` and the residue `ξ` is a
unit; these are the hypotheses `v ∈ bkPoints` and `IsResidueUnit ξ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- For an odd `m` with `0 < m < 2^17` and `|α| ≤ 1/3` there are reals `a ≤ α ≤ b` with
`F^{cut⁰, W^{0,12,14}_{m,a,b}}_{0,0}(m + α) - T^{root}_{0,12} < 77/100`. -/
private theorem exists_trTreeCost_sub_trTailGain_lt {m : ℤ} (hm : Odd m) (hm0 : 0 < m)
    (hm1 : m < 2 ^ 17) {α : ℝ} (hα : |α| ≤ 1 / 3) :
    ∃ a b : ℝ, a ≤ α ∧ α ≤ b ∧
      trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 m a b) 0 0 (m + α) - trTailGain 0 12 <
        77 / 100 := by
  by_cases h16 : m < 2 ^ 16
  · obtain ⟨a, b, -, ha, hb, -, h⟩ := trTreeCost_sub_trTailGain_lt hm hm0 h16 hα
    exact ⟨a, b, ha, hb, h⟩
  · have hne : m ≠ 2 ^ 16 := by
      rintro rfl
      exact (Int.not_odd_iff_even.mpr (by decide)) hm
    have hodd : Odd (2 ^ 17 - m) := by
      rw [Int.odd_sub']
      exact iff_of_true hm (by decide)
    have hα' : |-α| ≤ 1 / 3 := by rwa [abs_neg]
    obtain ⟨a', b', -, ha', hb', -, h⟩ :=
      trTreeCost_sub_trTailGain_lt hodd (by omega) (by omega) hα'
    have hr := trTreeCost_trZeroCutoff_reflect (2 ^ 17 - m) a' b' (((2 ^ 17 - m : ℤ) : ℝ) + -α)
    rw [show (2 : ℤ) ^ 17 - (2 ^ 17 - m) = m by ring,
      show (2 : ℝ) ^ 17 - (((2 ^ 17 - m : ℤ) : ℝ) + -α) = m + α by push_cast; ring] at hr
    refine ⟨-b', -a', by linarith, by linarith, ?_⟩
    rw [hr]
    exact h

/-- **The entry kernel at a black point of gap zero.** Let `ξ` be a unit and `v ∈ 𝒫` black for
`ε_*` with `gap(v) = 0`. Then `m_1(v) < 1 - d_entry`. -/
@[collatz_pos_dens "lem_tr_zero_gap_tree"]
theorem trKernel_one_lt_one_sub_dEntry_of_trGap_eq_zero {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) (hgap : trGap n ξ (epsStar : ℝ) v = 0) :
    trKernel n ξ 1 v < ENNReal.ofReal (1 - dEntry) := by
  have hgap0 : trGap n ξ (epsStar : ℝ) v = ((0 : ℕ) : ℤ) := by rw [hgap]; rfl
  obtain ⟨m, hm, hm0, hm1, α, hα, hθ⟩ :=
    exists_odd_bkTheta_add_sub_mem_int hξ hv hb hgap0 (B := 17) (by norm_num)
  have hα' : |α| ≤ 1 / 3 := by
    refine hα.trans ?_
    rw [epsStar_cast]
    norm_num
  obtain ⟨a, b, ha, hb', hlt⟩ := exists_trTreeCost_sub_trTailGain_lt hm hm0 hm1 hα'
  have hW : TrTreeValid n ξ (epsStar : ℝ) v (trZeroDatum m a b).W :=
    trTreeValid_trWhitePolicy (H := 17) le_rfl hgap0.ge (fun r hr L hL => hθ r L hr hL)
      (by norm_num) ha hb'
  have hθ' : ∀ r : ℕ, 1 ≤ r → ∀ L : ℤ, 0 ≤ L → L ≤ (17 : ℕ) →
      ∃ k : ℤ, bkTheta n ξ (v + ((r : ℤ), L)) -
        9 ^ (r - 1) * ((2 : ℝ) ^ (0 : ℕ) * m + α) / (2 : ℝ) ^ L = k := by
    intro r hr L hL0 hL
    lift L to ℕ using hL0
    simpa only [zpow_natCast] using hθ r L hr (by omega)
  refine (trKernel_one_le_ofReal_trTreeCost_sub_trTailGain hξ hv hb hgap0 hθ'
    (trZeroDatum m a b) hW).trans_lt ?_
  rw [trZeroDatum_cut, trZeroDatum_W, trZeroCutoff_zero, pow_zero, one_mul]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num [dEntry_eq])]
  push_cast [dEntry_eq]
  linarith

end CollatzPosDens
