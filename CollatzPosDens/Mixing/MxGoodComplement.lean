/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Mixing.MxGood
public import CollatzPosDens.Mixing.MxWindowHigh
public import CollatzPosDens.Mixing.MxWindowLow
public import CollatzPosDens.Mixing.MxOffsetTail
public import CollatzPosDens.Mixing.MxOvershootTail
public import CollatzPosDens.Mixing.MxProbeTail
public import CollatzPosDens.Mixing.MxWindowHighBound
public import CollatzPosDens.Mixing.MxWindowLowPos

/-!
# Most words are good

For every integer `n ≥ 2^{131072}`, the words of length `n` outside the good set `Gd_n` have
small geometric mass:
$$\mathbf{p}\bigl(\mathbb{Z}_{\ge1}^n \setminus \mathrm{Gd}_n\bigr) \le n^{-9/8}.$$

Write `V = Lv_n` and `S_i = A(w_{≤ i})`. The window ends satisfy
`2 q^-_n ≤ V - ½ n^{2049/4096}` and `2 q^+_n ≥ V + ½ n^{2049/4096}`, and both lie in `[1, n]`.
A word `w ∉ Gd_n` of length `n` with `off(w) ≤ n^{4609/4096}` either has `S_{q^-_n} > V` or
`S_{q^+_n} ≤ V`, in which case the prefix sum at a window end deviates from twice its length by
at least `½ n^{2049/4096}`, or it crosses `V` at a first index `i` with `q^-_n < i ≤ q^+_n`, and
then, not being good, it overshoots the level by more than `1 + ⌈(9/8) log₂ n⌉`. The four
resulting sets have masses at most `(1/3) n^{-9/8}`, `2 n^{-10}`, `2 n^{-10}` and
`(1/2) n^{-9/8}`, and `5/6 + 4 n^{-71/8} ≤ 1`.

## Main results

* `CollatzPosDens.geomMass_compl_mxGood_le`: `𝐩(ℤ_{≥1}^n \ Gd_n) ≤ n^{-9/8}` for
  `n ≥ 2^{131072}`.

## Implementation notes

The set `ℤ_{≥1}^n` is the set of words (lists of positive integers) of length `n`, and the bound
`n^{-9/8}` is a real number embedded in `ℝ≥0∞` by `ENNReal.ofReal`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For real `n ≥ 24`,
`(1/3) n^{-9/8} + 2 n^{-10} + 2 n^{-10} + (1/2) n^{-9/8} ≤ n^{-9/8}`. -/
private lemma geomMass_compl_mxGood_le_numeric {n : ℝ} (hn : 24 ≤ n) :
    1 / 3 * n ^ (-(9 / 8 : ℝ)) + 2 * n ^ (-10 : ℝ) + 2 * n ^ (-10 : ℝ) +
      1 / 2 * n ^ (-(9 / 8 : ℝ)) ≤ n ^ (-(9 / 8 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have hsplit : n ^ (-10 : ℝ) = n ^ (-(9 / 8 : ℝ)) * n ^ (-(71 / 8 : ℝ)) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hle : n ^ (-(71 / 8 : ℝ)) ≤ n ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hinv : n ^ (-1 : ℝ) ≤ 1 / 24 := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hn
  have hq : 0 < n ^ (-(9 / 8 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  rw [hsplit]
  nlinarith

/-- A word of length `n` outside `Gd_n` has a large offset, a prefix sum at a window end deviating
from twice its length by at least `D`, or an overshoot of the level `Lv_n`. -/
theorem compl_mxGood_subset_tails {n a b : ℕ} {D : ℝ} (ha : (a : ℤ) = mxWindowLow n)
    (hb : (b : ℤ) = mxWindowHigh n) (hbn : b ≤ n) (haR : 2 * (a : ℝ) ≤ mxLevel n - D)
    (hbR : mxLevel n + D ≤ 2 * (b : ℝ)) :
    {w : Word | w.length = n} \ mxGood n ⊆
      {w : Word | w.length = n ∧ (n : ℝ) ^ (4609 / 4096 : ℝ) < (off w : ℝ)} ∪
      {w : Word | w.length = n ∧ D ≤ |(Word.valSum (w.take a) : ℝ) - 2 * a|} ∪
      {w : Word | w.length = n ∧ D ≤ |(Word.valSum (w.take b) : ℝ) - 2 * b|} ∪
      {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
        mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
        ⌊mxLevel n⌋ + 1 + ⌈(9 / 8 : ℝ) * Real.logb 2 n⌉ < (Word.valSum (w.take i) : ℤ)} := by
  rintro w ⟨hlen, hng⟩
  simp only [Set.mem_ofPred_eq] at hlen
  by_cases hoff : (n : ℝ) ^ (4609 / 4096 : ℝ) < (off w : ℝ)
  · exact Or.inl (Or.inl (Or.inl ⟨hlen, hoff⟩))
  push Not at hoff
  by_cases hA : mxLevel n < (Word.valSum (w.take a) : ℝ)
  · exact Or.inl (Or.inl (Or.inr ⟨hlen, le_trans (by linarith) (le_abs_self _)⟩))
  push Not at hA
  by_cases hB : (Word.valSum (w.take b) : ℝ) ≤ mxLevel n
  · exact Or.inl (Or.inr ⟨hlen, le_trans (by linarith) (neg_le_abs _)⟩)
  push Not at hB
  have hex : ∃ i, mxLevel n < (Word.valSum (w.take i) : ℝ) := ⟨b, hB⟩
  set i := Nat.find hex
  have hi : mxLevel n < (Word.valSum (w.take i) : ℝ) := Nat.find_spec hex
  have hib : i ≤ b := Nat.find_min' hex hB
  have hai : a < i := by
    by_contra h
    push Not at h
    have : (Word.valSum (w.take i) : ℝ) ≤ Word.valSum (w.take a) := by
      exact_mod_cast Word.valSum_le_of_isPrefix (List.take_prefix_take_left h)
    linarith
  have hprev : (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n := by
    simpa using Nat.find_min hex (show i - 1 < i by omega)
  refine Or.inr ⟨hlen, i, by omega, by omega, hprev, hi, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hng ⟨hlen, hoff, i, by omega, by omega, ⟨by omega, by omega⟩, hprev, hi, hcon⟩

/-- For every integer `n ≥ 2^{131072}`, `𝐩(ℤ_{≥1}^n \ Gd_n) ≤ n^{-9/8}`. -/
@[collatz_pos_dens "lem_mx_good_complement"]
theorem geomMass_compl_mxGood_le (n : ℕ) (hn : 2 ^ 131072 ≤ n) :
    geomMass ({w : Word | w.length = n} \ mxGood n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  have hnR : (2 : ℝ) ^ 131072 ≤ n := by exact_mod_cast hn
  have h24 : (24 : ℝ) ≤ n :=
    le_trans (le_trans (by norm_num : (24 : ℝ) ≤ 2 ^ 5)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))) hnR
  set D : ℝ := (1 / 2 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) with hD
  have hlo := mxWindowLow_pos_bound hn
  have hhi := mxWindowHigh_bound n hn
  have hqlo := mxWindowLow_le n
  have hqhi := le_mxWindowHigh n
  have hlo0 : 0 < mxWindowLow n := by
    exact_mod_cast (lt_of_le_of_lt (by positivity) hlo : (0 : ℝ) < mxWindowLow n)
  have hlohi : mxWindowLow n ≤ mxWindowHigh n := by
    have : (0 : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) := by positivity
    exact_mod_cast (by linarith : (mxWindowLow n : ℝ) ≤ mxWindowHigh n)
  set a := (mxWindowLow n).toNat
  set b := (mxWindowHigh n).toNat
  have ha : (a : ℤ) = mxWindowLow n := Int.toNat_of_nonneg hlo0.le
  have hb : (b : ℤ) = mxWindowHigh n := Int.toNat_of_nonneg (by omega)
  have hbn : b ≤ n := by omega
  have han : a ≤ n := by omega
  have haR : 2 * (a : ℝ) ≤ mxLevel n - D := by
    have : (a : ℝ) = mxWindowLow n := by exact_mod_cast ha
    linarith
  have hbR : mxLevel n + D ≤ 2 * (b : ℝ) := by
    have : (b : ℝ) = mxWindowHigh n := by exact_mod_cast hb
    linarith
  have hO_le := geomMass_offsetTail_le n hn
  have hPA_le := geomMass_abs_valSum_take_sub_ge_le hnR han
  have hPB_le := geomMass_abs_valSum_take_sub_ge_le hnR hbn
  have hOv_le := geomMass_mxOvershootTail_le n
  calc geomMass ({w : Word | w.length = n} \ mxGood n)
      ≤ geomMass (_ ∪ _ ∪ _ ∪ _) := geomMass_mono (compl_mxGood_subset_tails ha hb hbn haR hbR)
    _ ≤ geomMass _ + geomMass _ + geomMass _ + geomMass _ := by
        refine (geomMass_union_le _ _).trans ?_
        gcongr
        refine (geomMass_union_le _ _).trans ?_
        gcongr
        exact geomMass_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 3 * (n : ℝ) ^ (-(9 / 8 : ℝ))) +
          ENNReal.ofReal (2 * (n : ℝ) ^ (-10 : ℝ)) +
          ENNReal.ofReal (2 * (n : ℝ) ^ (-10 : ℝ)) +
          ENNReal.ofReal (1 / 2 * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (1 / 3 * (n : ℝ) ^ (-(9 / 8 : ℝ)) + 2 * (n : ℝ) ^ (-10 : ℝ) +
          2 * (n : ℝ) ^ (-10 : ℝ) + 1 / 2 * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-(9 / 8 : ℝ))) :=
        ENNReal.ofReal_le_ofReal (geomMass_compl_mxGood_le_numeric h24)

end CollatzPosDens
