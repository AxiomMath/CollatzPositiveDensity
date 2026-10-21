/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.PrefixExtension
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.FcLateSurvival
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Seed.S05OffsetCap
public import CollatzPosDens.Seed.S05CapLoss
public import CollatzPosDens.Seed.S05CappedBlockMass

/-!
# Mass of the later selected blocks

For every `n ≥ j_e` (`j_e = selEnd = 29`), the later blocks of the selected central tuples carry
geometric mass
$$\prod_{i=1}^{j_e-1}\mathbf p\bigl(\{v\in\mathcal C(b_i,K_i) :
    \mathrm{off}(v)\le M_{\mathrm{sel}}\}\bigr)
  \cdot\prod_{i=j_e}^{n-1}\mathbf p\bigl(\mathcal C(b_i,K_i)\bigr)
  > \frac{199}{200}-2^{-592},$$
where `M_sel = 2^600` is the offset cap.

Write `a_i = 𝐩(𝒞(b_i, K_i))`, `m_i` for the factor of index `i` on the left, and `c_i` for
`7/(M_sel + 2)` if `i < j_e` and `0` otherwise. Each `𝒞(b_i, K_i)` is prefix-disjoint with
bounded lengths, so `a_i ≤ 1`, and `a_i - c_i ≤ m_i ≤ a_i` by
`CollatzPosDens.geomMass_centralFamily_sub_le_geomMass_setOf_off_le`. Telescoping gives
`∏ a_i - ∏ m_i ≤ ∑ (a_i - m_i) ≤ ∑_{0 < i < j_e} 7/(M_sel + 2) < 2^{-592}` by
`CollatzPosDens.sum_seven_div_offsetCap_add_two_lt`, while
`∏_{0 < i < n} a_i ≥ ∏_{0 ≤ i < n} a_i > 199/200` by
`CollatzPosDens.lt_prod_geomMass_centralFamily`.

## Main results

* `CollatzPosDens.sub_lt_prod_geomMass_laterBlocks`: the lower bound above.

## Implementation notes

The masses are `ℝ≥0∞`-valued and finite; the telescoping estimate is carried out on their
real parts. The bound is written `199/200 - 2⁻¹ ^ 592` in `ℝ≥0∞`, where the subtraction is
exact since `2⁻¹ ^ 592 ≤ 199/200`.

## References

* [Mazur, *Collatz positive density*], §16.7.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The central family `𝒞(b, K)` has geometric mass at most `1`. -/
theorem geomMass_centralFamily_le_one (b K : ℕ) : geomMass (centralFamily b K) ≤ 1 := by
  have hsub := centralFamily_subset_firstCrossing b K
  have hV : InformationTheory.IsPrefixFree (centralFamily b K) := fun u hu v hv huv =>
    isPrefixFree_firstCrossing _ _ _ u (hsub hu) v (hsub hv) huv
  exact geomMass_le_one_of_isPrefixFree hV (h := hb b) fun v hv =>
    length_le_hb_of_mem_firstCrossing (hsub hv)

/-- Telescoping: if `0 ≤ y_i ≤ x_i ≤ 1`, then `∏ x_i - ∏ y_i ≤ ∑ (x_i - y_i)`. -/
private theorem laterBlocks_prod_sub_prod_le_sum_sub {ι : Type*} (s : Finset ι) {x y : ι → ℝ}
    (hy : ∀ i ∈ s, 0 ≤ y i) (hyx : ∀ i ∈ s, y i ≤ x i) (hx : ∀ i ∈ s, x i ≤ 1) :
    ∏ i ∈ s, x i - ∏ i ∈ s, y i ≤ ∑ i ∈ s, (x i - y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hy hyx hx
    rw [Finset.prod_insert hl, Finset.prod_insert hl, Finset.sum_insert hl]
    have ih' := ih hy.2 hyx.2 hx.2
    have hP : ∏ i ∈ s, y i ≤ ∏ i ∈ s, x i :=
      Finset.prod_le_prod₀ (fun i hi => hy.2 i hi) fun i hi => hyx.2 i hi
    have hY0 : 0 ≤ ∏ i ∈ s, y i := Finset.prod_nonneg fun i hi => hy.2 i hi
    have hX1 : ∏ i ∈ s, x i ≤ 1 :=
      Finset.prod_le_one₀ (fun i hi => (hy.2 i hi).trans (hyx.2 i hi)) fun i hi => hx.2 i hi
    nlinarith [hy.1, hyx.1, hx.1]

/-- **Mass of the later selected blocks.** For every `n ≥ j_e`,
`∏_{0 < i < j_e} 𝐩({v ∈ 𝒞(b_i, K_i) : off(v) ≤ M_sel}) · ∏_{j_e ≤ i < n} 𝐩(𝒞(b_i, K_i))`
exceeds `199/200 - 2^{-592}`. -/
@[collatz_pos_dens "lem_s05_later_blocks_mass"]
theorem sub_lt_prod_geomMass_laterBlocks (n : ℕ) (hn : selEnd ≤ n) :
    (199 / 200 : ℝ≥0∞) - 2⁻¹ ^ 592 <
      (∏ i ∈ Finset.Ioo 0 selEnd,
          geomMass {v ∈ centralFamily (scale i) (cap i) | off v ≤ offsetCap}) *
        ∏ i ∈ Finset.Ico selEnd n, geomMass (centralFamily (scale i) (cap i)) := by
  have hse : 0 < selEnd := by rw [selEnd_eq]; norm_num
  have hgn : 0 < n := lt_of_lt_of_le hse hn
  set a : ℕ → ℝ≥0∞ := fun i => geomMass (centralFamily (scale i) (cap i)) with ha_def
  set m : ℕ → ℝ≥0∞ := fun i => if i < selEnd then
      geomMass {v ∈ centralFamily (scale i) (cap i) | off v ≤ offsetCap} else a i
    with hm_def
  -- The left side is `∏_{0 < i < n} m_i`.
  have hprod : (∏ i ∈ Finset.Ioo 0 selEnd,
        geomMass {v ∈ centralFamily (scale i) (cap i) | off v ≤ offsetCap}) *
        ∏ i ∈ Finset.Ico selEnd n, geomMass (centralFamily (scale i) (cap i)) =
      ∏ i ∈ Finset.Ico (0 + 1) n, m i := by
    rw [← Finset.prod_Ico_consecutive _ (show 0 + 1 ≤ selEnd by omega) hn,
      Finset.Ico_add_one_left_eq_Ioo]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i hi => ?_)
      (Finset.prod_congr rfl fun i hi => ?_)
    · rw [Finset.mem_Ioo] at hi
      simp only [hm_def, hi.2, ↓reduceIte]
    · rw [Finset.mem_Ico] at hi
      simp only [hm_def, ha_def, not_lt.2 hi.1, ↓reduceIte]
  rw [hprod]
  have ha1 : ∀ i, a i ≤ 1 := fun i => geomMass_centralFamily_le_one _ _
  have hma : ∀ i, m i ≤ a i := fun i => by
    simp only [hm_def]
    split_ifs
    · exact geomMass_mono fun v hv => hv.1
    · exact le_rfl
  have ha_top : ∀ i, a i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (ha1 i)
  have hm_top : ∀ i, m i ≠ ⊤ := fun i => ne_top_of_le_ne_top (ha_top i) (hma i)
  have hmr : ∀ i, (m i).toReal ≤ (a i).toReal := fun i => ENNReal.toReal_mono (ha_top i) (hma i)
  have har : ∀ i, (a i).toReal ≤ 1 := fun i => by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ha1 i)
  -- The deficit of each block.
  set c : ℕ → ℝ := fun _ => 7 / ((offsetCap : ℝ) + 2) with hc_def
  have hdef : ∑ i ∈ Finset.Ico (0 + 1) n, ((a i).toReal - (m i).toReal) <
      2 ^ (-592 : ℤ) := by
    rw [← Finset.sum_Ico_consecutive _ (show 0 + 1 ≤ selEnd by omega) hn]
    have hlate : ∑ i ∈ Finset.Ico selEnd n, ((a i).toReal - (m i).toReal) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      simp only [hm_def, not_lt.2 hi.1, ↓reduceIte, sub_self]
    rw [hlate, add_zero]
    have hcap := sum_seven_div_offsetCap_add_two_lt
    have hcapR : ∑ i ∈ Finset.Ioo 0 selEnd, c i < (2 : ℝ) ^ (-592 : ℤ) := by
      have := (Rat.cast_lt (K := ℝ)).2 hcap
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, Rat.cast_zpow,
        Rat.cast_natCast]
        using this
    refine lt_of_le_of_lt ?_ hcapR
    rw [← Finset.Ico_add_one_left_eq_Ioo]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    have h := geomMass_centralFamily_sub_le_geomMass_setOf_off_le i
    simp only [hm_def, ha_def, hc_def, hi.2, ↓reduceIte]
    linarith
  -- Late survival, in real parts.
  have hsurv : (199 / 200 : ℝ) < ∏ i ∈ Finset.Ico (0 + 1) n, (a i).toReal := by
    have h := lt_prod_geomMass_centralFamily n
    rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
      (ENNReal.prod_ne_top fun i _ => ha_top i),
      ENNReal.toReal_prod, Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hgn] at h
    have h199 : (199 / 200 : ℝ≥0∞).toReal = 199 / 200 := by
      rw [ENNReal.toReal_div]; norm_num
    rw [h199] at h
    have hP0 : 0 ≤ ∏ i ∈ Finset.Ico (0 + 1) n, (a i).toReal :=
      Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
    calc (199 / 200 : ℝ) < _ := h
      _ ≤ 1 * ∏ i ∈ Finset.Ico (0 + 1) n, (a i).toReal :=
          mul_le_mul_of_nonneg_right (har 0) hP0
      _ = _ := one_mul _
  have htel := laterBlocks_prod_sub_prod_le_sum_sub (Finset.Ico (0 + 1) n)
    (x := fun i => (a i).toReal) (y := fun i => (m i).toReal)
    (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hmr i) (fun i _ => har i)
  have hreal : (199 / 200 : ℝ) - 2 ^ (-592 : ℤ) <
      ∏ i ∈ Finset.Ico (0 + 1) n, (m i).toReal := by
    linarith
  -- Back to `ℝ≥0∞`.
  have hpow : ((2 : ℝ≥0∞)⁻¹ ^ 592) ≤ 199 / 200 := by
    calc ((2 : ℝ≥0∞)⁻¹ ^ 592) ≤ 2⁻¹ ^ 1 := pow_le_pow_right_of_le_one' (by norm_num) (by norm_num)
      _ ≤ 199 / 200 := by
        rw [pow_one, ← ENNReal.toReal_le_toReal (by simp)
          (ENNReal.div_ne_top (by simp) (by simp)), ENNReal.toReal_div, ENNReal.toReal_inv]
        norm_num
  have hlhs : ((199 / 200 : ℝ≥0∞) - 2⁻¹ ^ 592).toReal = (199 / 200 : ℝ) - 2 ^ (-592 : ℤ) := by
    rw [ENNReal.toReal_sub_of_le hpow (ENNReal.div_ne_top (by simp) (by simp)),
      ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_inv, zpow_neg, inv_pow]
    norm_num
  rw [← ENNReal.toReal_lt_toReal (ENNReal.sub_ne_top (ENNReal.div_ne_top (by simp) (by simp)))
    (ENNReal.prod_ne_top fun i _ => hm_top i), hlhs, ENNReal.toReal_prod]
  exact hreal

end CollatzPosDens
