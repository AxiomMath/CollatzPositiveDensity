/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB473
public import CollatzPosDens.FirstCrossing.ScalesLinearLower
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Seed.HistoryOffset
public import CollatzPosDens.Seed.S05BlockWeight
public import CollatzPosDens.Seed.S05ConcatWord
public import CollatzPosDens.Seed.S05OffsetCap
public import CollatzPosDens.Seed.S05Selector
public import CollatzPosDens.Seed.S05Tuples

/-!
# Offsets of selected tuples

Let `j_e = 29` be the generation `selEnd`, let `n ≥ j_e` and let `τ = (v_0, …, v_{n-1})` be a
selected central tuple, `τ ∈ 𝔗_n`. Then the offset of the concatenated word
`ŵ(τ) = v_0 ⋯ v_{n-1}` satisfies
$$0 \le \mathrm{off}(\hat w(\tau)) \le \tfrac34 + 2^{-8}.$$

Put `P_i = v_0 ⋯ v_{i-1}` for `0 ≤ i ≤ 29` and `S = v_{29} ⋯ v_{n-1}`, so `ŵ(τ) = P_{29} S`.
Each block weight satisfies `ω(v_l) < 16^{-e_{b_l}}`, and the exponents `e_{b_l}` add up to the
scale increments, so `ω(P_i) ≤ 16^{-(b_i - b_0)}`. The cocycle identity for the offset gives
$$\mathrm{off}(\hat w(\tau)) = \mathrm{off}(v_0)
  + \sum_{0 < i < 29} \omega(P_i)\,\mathrm{off}(v_i) + \omega(P_{29})\,\mathrm{off}(S).$$
The selector bounds the first term by `3/4` and each middle term by
`16^{-(b_i - b_0)} M_sel ≤ 2^{600 - 664 i}`, with `M_sel = 2^600` and `b_i - b_0 ≥ 166 i`, so
the middle sum is below `2^{-62}`; the offset of a central suffix is at most `2^{b_{29} + 1}`,
and `b_{29} = 22095`, `b_{29} - b_0 = 5551`, so the last term is at most `2^{-108}`.

## Main results

* `CollatzPosDens.off_concatWord_mem_Icc_of_mem_selectedTuples`:
  `0 ≤ off(ŵ(τ)) ≤ 3/4 + 2^{-8}` for `n ≥ j_e` and `τ ∈ 𝔗_n`.

## Implementation notes

The prefixes `P_i` are the flattenings of the first `i` entries of the list `[v_0, …, v_{n-1}]`,
and the bounds on their weights and offsets are proved together by induction on `i ≤ 29`. Each
middle term is bounded by `2^{-(63+i)}` (as `600 - 664 i ≤ -(63 + i)` for `i ≥ 1`), so that the
middle sum telescopes below `2^{-62}`; summing the geometric series `2^{600-664i}` directly
gives `2^{-63}` instead. Either bound leaves ample room below `2^{-8}`. The lower bound
`0 ≤ off(ŵ(τ))` holds for every word and is recorded alongside the upper bound.

## References

* [Mazur, *Collatz positive density*], §16.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weight and offset of the prefix `P_i = v_0 ⋯ v_{i-1}` of a selected tuple, for
`i ≤ 29`: `ω(P_i) ≤ 16^{-(b_i - b_0)}`, and for `i ≥ 1`,
`off(P_i) ≤ 3/4 + 2^{-62} - 2^{-(62+i)}`. -/
private lemma weight_off_prefix_le_of_mem_selectedTuples {n : ℕ} (hn : selEnd ≤ n)
    {τ : Fin n → Word} (hτ : τ ∈ selectedTuples n) :
    ∀ i ≤ 29, Word.weight ((List.ofFn τ).take i).flatten ≤
        (16 : ℚ) ^ (-((scale i : ℤ) - scale 0)) ∧
      (1 ≤ i → off ((List.ofFn τ).take i).flatten ≤
        3 / 4 + (1 / 2) ^ 62 - (1 / 2) ^ (62 + i)) := by
  have hse := selEnd_eq
  intro i hi
  induction i with
  | zero =>
    refine ⟨?_, fun h => absurd h (by norm_num)⟩
    rw [List.take_zero, List.flatten_nil, Word.weight_nil, sub_self, neg_zero, zpow_zero]
  | succ i ih =>
    obtain ⟨ihw, iho⟩ := ih (by omega)
    have hj : i < n := by omega
    have hm : τ ⟨i, hj⟩ ∈ centralFamily (scale i) (cap i) :=
      selectedTuples_mem_centralFamily hτ ⟨i, hj⟩
    rw [flatten_take_succ_ofFn τ hj]
    set P : Word := ((List.ofFn τ).take i).flatten
    set v : Word := τ ⟨i, hj⟩
    have hlin := scale_linear_lower i
    set b := scale i
    have hb : 256 ≤ b := by omega
    have hblk := sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily hb hm
    have hinv : (0 : ℚ) ≤ (2 ^ (3 * b))⁻¹ := by positivity
    have hv : v.weight ≤ (16 : ℚ) ^ (-(eb b : ℤ)) := by
      rw [zpow_neg, zpow_natCast, ← one_div, le_div_iff₀ (by positivity)]
      linarith
    have hP := Word.weight_pos P
    refine ⟨?_, fun _ => ?_⟩
    · rw [Word.weight_append, scale_succ]
      calc P.weight * v.weight ≤ (16 : ℚ) ^ (-((b : ℤ) - scale 0)) * 16 ^ (-(eb b : ℤ)) :=
            mul_le_mul ihw hv (Word.weight_pos v).le (by positivity)
        _ = (16 : ℚ) ^ (-(((b + eb b : ℕ) : ℤ) - scale 0)) := by
            rw [← zpow_add₀ (by norm_num), show -((b : ℤ) - scale 0) + -(eb b : ℤ) =
              -(((b + eb b : ℕ) : ℤ) - scale 0) by push_cast; ring]
    · rw [off_append]
      have hov := off_nonneg v
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · have h0 : off v ≤ 3 / 4 := (selectedTuples_selector hτ).off_le_three_quarters (by omega)
        simp only [P, List.take_zero, List.flatten_nil, off_nil, Word.weight_nil] at h0 ⊢
        norm_num
        linarith
      · have hcap : off v ≤ (offsetCap : ℚ) :=
          (selectedTuples_selector hτ).off_le_offsetCap (i := i) hi1 (by omega)
        rw [cast_offsetCap] at hcap
        have hprod : P.weight * off v ≤ (1 / 2) ^ (63 + i) := by
          calc P.weight * off v ≤ (16 : ℚ) ^ (-((b : ℤ) - scale 0)) * 2 ^ 600 :=
                mul_le_mul ihw hcap hov (by positivity)
            _ = (2 : ℚ) ^ (4 * (-((b : ℤ) - scale 0)) + 600) := by
                rw [show (16 : ℚ) = 2 ^ (4 : ℤ) by norm_num, ← zpow_mul,
                  ← zpow_natCast (2 : ℚ) 600, ← zpow_add₀ two_ne_zero]
                push_cast
                ring_nf
            _ ≤ (2 : ℚ) ^ (-((63 + i : ℕ) : ℤ)) := by
                refine zpow_le_zpow_right₀ (by norm_num) ?_
                rw [scale_zero]
                push_cast
                omega
            _ = (1 / 2) ^ (63 + i) := by
                rw [zpow_neg, zpow_natCast, one_div_pow, one_div]
        have h1 := iho hi1
        have h2 : ((1 : ℚ) / 2) ^ (62 + i) = 2 * (1 / 2) ^ (63 + i) := by
          rw [show 63 + i = (62 + i) + 1 by omega, pow_succ]
          ring
        rw [show 62 + (i + 1) = 63 + i by omega]
        linarith

/-- **Offsets of selected tuples.** For `n ≥ j_e` and `τ ∈ 𝔗_n`,
`0 ≤ off(ŵ(τ)) ≤ 3/4 + 2^{-8}`. -/
@[collatz_pos_dens "lem_s05_selected_offset"]
theorem off_concatWord_mem_Icc_of_mem_selectedTuples {n : ℕ} (hn : selEnd ≤ n)
    {τ : Fin n → Word} (hτ : τ ∈ selectedTuples n) :
    0 ≤ off (concatWord τ) ∧ off (concatWord τ) ≤ 3 / 4 + 1 / 2 ^ 8 := by
  have hse := selEnd_eq
  refine ⟨off_nonneg _, ?_⟩
  obtain ⟨hw, ho⟩ := weight_off_prefix_le_of_mem_selectedTuples hn hτ 29 le_rfl
  have ho := ho (by norm_num)
  have h29 : scale 29 = 22095 := scale_selEnd
  rw [h29, scale_zero] at hw
  have hS : off ((List.ofFn τ).drop 29).flatten ≤ 2 ^ (scale 29 + 1) :=
    off_flatten_le_of_mem_centralFamily cap _ 29 fun k hk => by
      rw [List.length_drop, List.length_ofFn] at hk
      rw [List.getElem_drop, List.getElem_ofFn]
      exact selectedTuples_mem_centralFamily hτ ⟨29 + k, by omega⟩
  rw [h29] at hS
  rw [concatWord, ← List.take_append_drop 29 (List.ofFn τ), List.flatten_append, off_append]
  set P : Word := ((List.ofFn τ).take 29).flatten
  set S : Word := ((List.ofFn τ).drop 29).flatten
  have hP := Word.weight_pos P
  have hS0 := off_nonneg S
  have hlast : P.weight * off S ≤ (1 / 2) ^ 108 := by
    calc P.weight * off S
        ≤ (16 : ℚ) ^ (-(((22095 : ℕ) : ℤ) - ((16544 : ℕ) : ℤ))) * 2 ^ (22095 + 1) :=
          mul_le_mul hw hS hS0 (by positivity)
      _ = (1 / 2) ^ 108 := by
          rw [show -(((22095 : ℕ) : ℤ) - ((16544 : ℕ) : ℤ)) = -((5551 : ℕ) : ℤ) by norm_num,
            zpow_neg, zpow_natCast, show (16 : ℚ) ^ 5551 = 2 ^ 108 * 2 ^ (22095 + 1) by
              rw [← pow_add, show (16 : ℚ) = 2 ^ 4 by norm_num, ← pow_mul], mul_inv,
            inv_mul_cancel_right₀ (by positivity), one_div_pow, one_div]
  have : (3 : ℚ) / 4 + (1 / 2) ^ 62 - (1 / 2) ^ (62 + 29) + (1 / 2) ^ 108 ≤
      3 / 4 + 1 / 2 ^ 8 := by norm_num
  linarith

end CollatzPosDens
