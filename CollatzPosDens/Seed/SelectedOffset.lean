/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.OffsetBound
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.HistoryOffset
public import CollatzPosDens.Seed.BlockWeight
public import CollatzPosDens.Seed.ConcatWord
public import CollatzPosDens.Seed.FirstScales
public import CollatzPosDens.Seed.Rounding
public import CollatzPosDens.Seed.Selector
public import CollatzPosDens.Seed.Tuples

/-!
# Offsets of selected tuples

Let `n ≥ 5` and let `t = (v₀, …, v_{n-1})` be a selected central tuple, `t ∈ 𝔗_n`. Then the
offset of the concatenated word `ŵ(t) = v₀ v₁ ⋯ v_{n-1}` satisfies
$$\tfrac{85}{256} \le \mathrm{off}(\hat w(t)) \le \tfrac{637}{256}.$$

Write `S = v₅ ⋯ v_{n-1}` and `sⱼ = ω(vⱼ)`. The first six scales are `9, 10, …, 14`, so
`e_{b_j} = 1` and `16 sⱼ < 1` for `j < 5`; moreover `|v₀| ≤ h₉ = 14`, `|v₁| ≤ h₁₀ = 16` and
`0 ≤ off(S) ≤ 2^{15}`. The cocycle identity for the offset gives
$$\mathrm{off}(\hat w(t)) = \mathrm{off}(v_0) + s_0\,\mathrm{off}(v_1)
  + s_0 s_1\bigl[\mathrm{off}(v_2) + s_2(\mathrm{off}(v_3)
  + s_3(\mathrm{off}(v_4) + s_4\,\mathrm{off}(S)))\bigr].$$
The lower bound drops the bracket and uses `roundedOffset_sub_le_off_le` with `p = 9, 6`
together with `fiveBlockSelector`; the upper bound uses the bounds `off(v₂) ≤ 16`,
`off(v₃) ≤ 64`, `off(v₄) ≤ 256` from `fiveBlockSelector`, which bound the bracketed term by
`29/256`.

## Main results

* `CollatzPosDens.off_concatWord_mem_Icc_of_mem_selectedTuples`:
  `85/256 ≤ off(ŵ(t)) ≤ 637/256` for `n ≥ 5` and `t ∈ 𝔗_n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The concatenated word of a tuple of length at least five, split after its first five
blocks. -/
private lemma concatWord_eq_five {m : ℕ} (t : Fin (m + 5) → Word) :
    concatWord t = t ⟨0, by omega⟩ ++ (t ⟨1, by omega⟩ ++ (t ⟨2, by omega⟩ ++
      (t ⟨3, by omega⟩ ++ (t ⟨4, by omega⟩ ++ ((List.ofFn t).drop 5).flatten)))) := by
  simp only [concatWord, List.ofFn_succ, List.drop_succ_cons, List.drop_zero,
    List.flatten_cons]
  rfl

/-- The offset bound for `v₀ v₁ v₂ v₃ v₄ S` from the block bounds. -/
private lemma off_five_append_mem_Icc (v₀ v₁ v₂ v₃ v₄ S : Word)
    (h₀ : v₀.length ≤ 14) (h₁ : v₁.length ≤ 16)
    (hw₀ : 16 * v₀.weight < 1) (hw₁ : 16 * v₁.weight < 1) (hw₂ : 16 * v₂.weight < 1)
    (hw₃ : 16 * v₃.weight < 1) (hw₄ : 16 * v₄.weight < 1)
    (hS : off S ≤ 2 ^ 15) (hsel : fiveBlockSelector v₀ v₁ v₂ v₃ v₄) :
    85 / 256 ≤ off (v₀ ++ (v₁ ++ (v₂ ++ (v₃ ++ (v₄ ++ S))))) ∧
      off (v₀ ++ (v₁ ++ (v₂ ++ (v₃ ++ (v₄ ++ S))))) ≤ 637 / 256 := by
  obtain ⟨hl, hu, -, hr₂, hr₃, hr₄⟩ := hsel
  simp only [off_append]
  have p₀ := Word.weight_pos v₀
  have p₁ := Word.weight_pos v₁
  have p₂ := Word.weight_pos v₂
  have p₃ := Word.weight_pos v₃
  have p₄ := Word.weight_pos v₄
  have o₁ := off_nonneg v₁
  have o₂ := off_nonneg v₂
  have o₃ := off_nonneg v₃
  have o₄ := off_nonneg v₄
  have oS := off_nonneg S
  have r₀ := roundedOffset_sub_le_off_le 9 v₀
  have r₁ := roundedOffset_sub_le_off_le 6 v₁
  have e₂ := (off_le_roundedOffset 3 v₂).trans hr₂
  have e₃ := (off_le_roundedOffset 0 v₃).trans hr₃
  have e₄ := (off_le_roundedOffset (-3) v₄).trans hr₄
  have l₀ : (v₀.length : ℚ) ≤ 14 := by exact_mod_cast h₀
  have l₁ : (v₁.length : ℚ) ≤ 16 := by exact_mod_cast h₁
  norm_num at r₀ r₁
  set B := off v₂ + v₂.weight * (off v₃ + v₃.weight * (off v₄ + v₄.weight * off S))
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ 29 := by
    have t₄ : off v₄ + v₄.weight * off S ≤ 2304 := by nlinarith
    have t₄' : 0 ≤ off v₄ + v₄.weight * off S := by positivity
    have t₃ : off v₃ + v₃.weight * (off v₄ + v₄.weight * off S) ≤ 208 := by nlinarith
    have t₃' : 0 ≤ off v₃ + v₃.weight * (off v₄ + v₄.weight * off S) := by positivity
    nlinarith
  have hrd₁ := roundedOffset_nonneg 6 v₁
  constructor
  · have : 0 ≤ v₀.weight * (v₁.weight * B) := by positivity
    nlinarith
  · have h01 : v₀.weight * v₁.weight ≤ 1 / 256 := by nlinarith
    have : v₀.weight * (v₁.weight * B) ≤ 29 / 256 := by
      rw [← mul_assoc]
      nlinarith
    nlinarith

/-- **Offsets of selected tuples.** For `n ≥ 5` and `t ∈ 𝔗_n`,
`85/256 ≤ off(ŵ(t)) ≤ 637/256`. -/
@[collatz_pos_dens "lem_s05_selected_offset"]
theorem off_concatWord_mem_Icc_of_mem_selectedTuples {n : ℕ} (hn : 5 ≤ n)
    {t : Fin n → Word} (ht : t ∈ selectedTuples n) :
    85 / 256 ≤ off (concatWord t) ∧ off (concatWord t) ≤ 637 / 256 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hmem := selectedTuples_mem_centralFamily ht
  have hsc := scale_first_six
  simp only [Prod.mk.injEq] at hsc
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hsc
  have hwt : ∀ j : Fin (m + 5), (j : ℕ) < 5 → 16 * (t j).weight < 1 := by
    intro j hj
    have h := sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily (nine_le_scale j) (hmem j)
    have he : eb (scale j) = 1 := by
      have := scale_succ j
      obtain ⟨j, hj'⟩ := j
      simp only at hj ⊢ this
      interval_cases j <;>
        simp only [Nat.reduceAdd, s0, s1, s2, s3, s4, s5] at this ⊢ <;> omega
    rw [he, pow_one] at h
    have : (0 : ℚ) ≤ (2 ^ (3 * scale j))⁻¹ := by positivity
    linarith
  have hlen : ∀ j : Fin (m + 5), (t j).length ≤ hb (scale j) := fun j =>
    length_le_hb_of_mem_firstCrossing (centralFamily_subset_firstCrossing _ _ (hmem j))
  have h₀ := hlen ⟨0, by omega⟩
  have h₁ := hlen ⟨1, by omega⟩
  simp only [s0, s1] at h₀ h₁
  have hS := (off_historySuffix_mem_Icc 5 t fun j _ => hmem j).2
  rw [s5] at hS
  rw [concatWord_eq_five]
  exact off_five_append_mem_Icc _ _ _ _ _ _ (by simpa [hb_eq] using h₀)
    (by simpa [hb_eq] using h₁) (hwt _ (by simp)) (hwt _ (by simp)) (hwt _ (by simp))
    (hwt _ (by simp)) (hwt _ (by simp)) (by simpa using hS)
    (selectedTuples_selector ht hn)

end CollatzPosDens
