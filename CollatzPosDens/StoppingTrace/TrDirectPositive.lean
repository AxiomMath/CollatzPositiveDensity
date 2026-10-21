/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificate
public import CollatzPosDens.StoppingTrace.TrTreeAngle
public import CollatzPosDens.StoppingTrace.TrTreeCylinderBound
public import CollatzPosDens.StoppingTrace.TrWhitePolicyValid
public import CollatzPosDens.Transfer.S02Dentry

/-!
# The entry kernel at a black point of direct gap

Fix a level `n`, a unit `ξ ∈ G_n` and the colour scale `ε_*`. Let `v ∈ 𝒫` be black with gap
`ω = gap(v) ∈ {1, 6, 9, 13, 16}`, and put `p = 4` if `ω ∈ {1, 6, 9}` and `p = 1` if
`ω ∈ {13, 16}`. The angles above and to the right of `v` are governed by an odd integer `m` with
`0 < m < 2^{p+8}` and a real `α` with `|α| ≤ 9 ε_* < 1/3`:
`ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ` for `r ≥ 1` and `0 ≤ L ≤ ω + p + 8`. The
direct-entry certificate gives reals `-1/3 ≤ a ≤ α ≤ b ≤ 1/3` with
`F^{8,W}_{0,0}(2^ω m + α) - T^{root}_{ω,8} < 77/100`, where `W = W^{ω,8,ω+p}_{m,a,b}`. The pair
`(8, W)` is a tree datum of height `ω + p + 8` and `W` is valid at `v`, so the tree cylinder
bound gives `m_1(v) < 77/100 = 1 - d_entry`.

## Main results

* `CollatzPosDens.trKernel_one_lt_one_sub_dEntry_of_trGap_mem`: for a black point `v` with
  `gap(v) ∈ {1, 6, 9, 13, 16}`, `m_1(v) < 1 - d_entry`.

## Implementation notes

The number `m_1(v)` lies in `[0, ∞]`; the bound is stated as
`m_1(v) < ENNReal.ofReal (1 - d_entry)`. Black points are points of `𝒫` and the residue `ξ` is a
unit; these standing assumptions are the hypotheses `v ∈ bkPoints` and `IsResidueUnit ξ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

/-- The direct positive bound for one pair `(ω, p)` of the certificate: if `v` is black with
`gap(v) = ω`, then `m_1(v) < 1 - d_entry`. -/
private theorem trKernel_one_lt_one_sub_dEntry_of_pair {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) {ω p : ℕ}
    (hωp : (ω, p) ∈ [(1, 4), (6, 4), (9, 4), (13, 1), (16, 1)])
    (hgap : trGap n ξ (epsStar : ℝ) v = ω) :
    trKernel n ξ 1 v < ENNReal.ofReal (1 - dEntry) := by
  obtain ⟨m, hm, hm0, hm1, α, hα, hθ⟩ :=
    exists_odd_bkTheta_add_sub_mem_int hξ hv hb hgap (B := p + 8) (by omega)
  have hα' : |α| ≤ 1 / 3 := by
    refine hα.trans ?_
    rw [epsStar_cast]
    norm_num
  obtain ⟨a, b, -, ha, hb', -, hlt⟩ :=
    exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt hωp hm hm0 hm1 hα'
  obtain ⟨D, hDcut, hDW⟩ := exists_trDirectDatum ω p m a b
  have hθ₁ : ∀ r : ℕ, 1 ≤ r → ∀ L : ℕ, L ≤ ω + p + 8 → ∃ k : ℤ,
      bkTheta n ξ (v + ((r : ℤ), (L : ℤ))) - (9 : ℝ) ^ (r - 1) * (2 ^ ω * m + α) / 2 ^ L = k :=
    fun r hr L hL => hθ r L hr (by omega)
  have hW : TrTreeValid n ξ (epsStar : ℝ) v D.W := by
    rw [hDW]
    exact trTreeValid_trWhitePolicy le_rfl hgap.ge hθ₁ (by push_cast; omega) ha hb'
  have hθ' : ∀ r : ℕ, 1 ≤ r → ∀ L : ℤ, 0 ≤ L → L ≤ ((ω + p + 8 : ℕ) : ℤ) →
      ∃ k : ℤ, bkTheta n ξ (v + ((r : ℤ), L)) -
        9 ^ (r - 1) * ((2 : ℝ) ^ ω * m + α) / (2 : ℝ) ^ L = k := by
    intro r hr L hL0 hL
    lift L to ℕ using hL0
    simpa only [zpow_natCast] using hθ₁ r hr L (by omega)
  refine (trKernel_one_le_ofReal_trTreeCost_sub_trTailGain hξ hv hb hgap hθ' D hW).trans_lt ?_
  rw [hDcut, hDW, ENNReal.ofReal_lt_ofReal_iff (by norm_num [dEntry_eq]), dEntry_cast]
  linarith

/-- **The entry kernel at a black point of direct gap.** Let `ξ` be a unit and `v ∈ 𝒫` black
for `ε_*` with `gap(v) ∈ {1, 6, 9, 13, 16}`. Then `m_1(v) < 1 - d_entry`. -/
@[collatz_pos_dens "lem_tr_direct_positive"]
theorem trKernel_one_lt_one_sub_dEntry_of_trGap_mem {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v)
    (hgap : trGap n ξ (epsStar : ℝ) v ∈ ({1, 6, 9, 13, 16} : Set ℤ)) :
    trKernel n ξ 1 v < ENNReal.ofReal (1 - dEntry) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgap
  rcases hgap with h | h | h | h | h
  · exact trKernel_one_lt_one_sub_dEntry_of_pair hξ hv hb (ω := 1) (p := 4) (by simp)
      (by rw [h]; rfl)
  · exact trKernel_one_lt_one_sub_dEntry_of_pair hξ hv hb (ω := 6) (p := 4) (by simp)
      (by rw [h]; rfl)
  · exact trKernel_one_lt_one_sub_dEntry_of_pair hξ hv hb (ω := 9) (p := 4) (by simp)
      (by rw [h]; rfl)
  · exact trKernel_one_lt_one_sub_dEntry_of_pair hξ hv hb (ω := 13) (p := 1) (by simp)
      (by rw [h]; rfl)
  · exact trKernel_one_lt_one_sub_dEntry_of_pair hξ hv hb (ω := 16) (p := 1) (by simp)
      (by rw [h]; rfl)

end CollatzPosDens
