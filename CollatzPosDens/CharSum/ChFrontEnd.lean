/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQfinite
public import CollatzPosDens.CharSum.ChQfiniteStep
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChPenalty
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.CharSum.ChQBeyond
public import CollatzPosDens.CharSum.ChQHorizon
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQRecursionLe
public import CollatzPosDens.CharSum.ChBlockHold
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChEnvelopeRhs
public import CollatzPosDens.CharSum.ChFactorPenalty
public import CollatzPosDens.CharSum.ChFrontPascal
public import CollatzPosDens.CharSum.ChPascalMass
public import CollatzPosDens.CharSum.ChRawLaw
public import CollatzPosDens.CharSum.ChRawPenalty
public import CollatzPosDens.Renewal.RnHoldMass

/-!
# The front end of the character-sum bound

Fix `n`, `ξ ∈ G_n` and `ε ≥ ε_*`, and let `J = ⌊n/2⌋`. Then
`|μ̂_n(ξ)| ≤ ∑_{h ∈ 𝒫} η(h) Q(h)`.

By `norm_refLawDft_le_tsum_chPairFactor` and `prod_chPairFactor_le_chPenalty` (which needs
`ε ≥ ε_*`), `|μ̂_n(ξ)| ≤ ∑_{b ∈ ℤ^J} ∏_i ϖ(b_i) Pen(b)`. By the law of the raw word, the right
side is `∑_{β ∈ 𝔅^J} ∏_k bw(βᵏ) Pen(raw_J(β))`, and the penalty of a raw word factors along the
block path as `∏_{k=1}^J w(Bp_k(β)) ∏_{k=1}^J I(Bp_{k-1}(β); βᵏ)`. Multiplied by `w((0, 0))`,
this is exactly the term of the series defining `Q^{(J)}((0, 0))`, so the right side equals
`Q^{(J)}((0, 0)) / w((0, 0))`. For `J = 0` this is `1 = ∑_h η(h) Q(h)`, since `Q(h) = 1` whenever
`j(h) ≥ 1 > J`. For `J = K + 1` the step recursion for the finite-horizon white products turns it
into `∑_{β ∈ 𝔅} bw(β) I((0, 0); β) Q^{(K)}(bpt(β))`; here `Q^{(K)}(bpt(β)) = Q(bpt(β))` since
`J ≤ j(bpt(β)) + K`, and `I ≤ 1` together with the grouping of blocks by their block points gives
the bound `∑_h η(h) Q(h)`.

## Main results

* `CollatzPosDens.norm_refLawDft_le_tsum_holdLaw_mul_chQ`: `|μ̂_n(ξ)| ≤ ∑_{h ∈ 𝒫} η(h) Q(h)`.

## Implementation notes

Instead of splitting off the first block of `β ∈ 𝔅^J` directly, the proof uses the step recursion
`Q^{(K+1)}(p) = w(p) ∑_β bw(β) I(p; β) Q^{(K)}(p + bpt(β))` at `p = (0, 0)`: the series
`∑_β ∏_k bw(βᵏ) Pen(raw_J(β))` differs from the one defining `Q^{(J)}((0, 0))` only by the factor
`w((0, 0)) > 0` (the `i = 0` factor of the white product), which cancels against the same factor
in the step recursion. This also covers the case `J = 0` uniformly, as
`Q^{(0)}((0, 0)) = w((0, 0))`.

## References

* [Mazur, *Collatz positive density*], §7.6.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- The prefix sums of a tuple, read as a list. -/
private theorem sum_take_ofFn_eq_sum_Iio {J : ℕ} (b : Fin J → ℤ) (i : Fin J) :
    ((List.ofFn b).take i).sum = ∑ l ∈ Iio i, b l := by
  induction J with
  | zero => exact i.elim0
  | succ J ih =>
    rw [List.ofFn_succ]
    induction i using Fin.cases with
    | zero =>
      have h0 : Iio (0 : Fin (J + 1)) = ∅ := by
        ext l
        simp
      simp [h0]
    | succ i =>
      rw [Fin.val_succ, List.take_succ_cons, List.sum_cons, ih]
      have h : Iio i.succ = insert 0 ((Iio i).image Fin.succ) := by
        rw [Fin.finsetImage_succ_Iio]
        ext l
        simp only [mem_Iio, mem_insert, mem_Ioo]
        rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;> simp [Fin.succ_pos]
      rw [h, sum_insert (by simp), sum_image (Fin.succ_injective _).injOn]

/-- For `ε ≥ ε_*`, the pair factors along a tuple `b` are bounded by its penalty. -/
private theorem prod_chPairFactor_le_chPenalty_ofFn {n J : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (b : Fin J → ℤ) :
    ∏ i : Fin J, chPairFactor n ξ (i + 1) (∑ l ∈ Iio i, b l) (b i) ≤
      chPenalty n ξ ε (List.ofFn b) := by
  refine le_of_eq_of_le ?_ (prod_chPairFactor_le_chPenalty hε (List.ofFn b))
  rw [← Fin.prod_congr' _ (List.length_ofFn).symm]
  refine prod_congr rfl fun i _ ↦ ?_
  simp [sum_take_ofFn_eq_sum_Iio]

/-- `∑_b ∏_i ϖ(b_i) G(b)` is summable for a function `G` with values in `[0, 1]`. -/
theorem summable_prod_varpi_mul {J : ℕ} (G : List ℤ → ℝ) (hG0 : ∀ b, 0 ≤ G b)
    (hG1 : ∀ b, G b ≤ 1) :
    Summable fun b : Fin J → ℤ ↦ (∏ i, varpi (b i)) * G (List.ofFn b) :=
  (hasSum_prod_varpi J).summable.of_nonneg_of_le
    (fun _ ↦ mul_nonneg (prod_nonneg fun _ _ ↦ varpi_nonneg _) (hG0 _))
    fun _ ↦ mul_le_of_le_one_right (prod_nonneg fun _ _ ↦ varpi_nonneg _) (hG1 _)

/-- Inserting the law of the raw word: `∑_b ∏_i ϖ(b_i) G(b) = ∑_{β ∈ 𝔅^J} ∏_k bw(βᵏ) G(raw_J(β))`
for a function `G` with values in `[0, 1]`. -/
private theorem tsum_varpi_mul_eq_tsum_chBlockWeight_mul (J : ℕ) (G : List ℤ → ℝ)
    (hG0 : ∀ b, 0 ≤ G b) (hG1 : ∀ b, G b ≤ 1) :
    ∑' b : Fin J → ℤ, (∏ i, varpi (b i)) * G (List.ofFn b) =
      ∑' β : Fin J → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        (∏ k, chBlockWeight (β k)) * G (chRaw J (List.ofFn fun k ↦ (β k).1)) := by
  let F : (Fin J → ℤ) × (Fin J → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) → ℝ := fun x ↦
    ((∏ k, chBlockWeight (x.2 k)) *
      if chRaw J (List.ofFn fun k ↦ (x.2 k).1) = List.ofFn x.1 then 1 else 0) *
        G (List.ofFn x.1)
  have hF0 : ∀ x, 0 ≤ F x := fun x ↦ mul_nonneg (mul_nonneg
    (prod_nonneg fun k _ ↦ chBlockWeight_nonneg _) (by split_ifs <;> norm_num)) (hG0 _)
  have hb : ∀ b, HasSum (fun c ↦ F (b, c)) ((∏ i, varpi (b i)) * G (List.ofFn b)) :=
    fun b ↦ (hasSum_prod_chBlockWeight_chRaw_eq le_rfl b).mul_right _
  have hF : Summable F := by
    rw [summable_prod_of_nonneg hF0]
    exact ⟨fun b ↦ (hb b).summable,
      by simpa only [(hb _).tsum_eq] using summable_prod_varpi_mul G hG0 hG1⟩
  have hc : ∀ c : Fin J → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}, HasSum (fun b ↦ F (b, c))
      ((∏ k, chBlockWeight (c k)) * G (chRaw J (List.ofFn fun k ↦ (c k).1))) := by
    intro c
    have hlen : (chRaw J (List.ofFn fun k ↦ (c k).1)).length = J :=
      length_chRaw_of_le_length (by simp)
    set b₀ : Fin J → ℤ := fun i ↦ (chRaw J (List.ofFn fun k ↦ (c k).1))[(i : ℕ)]'(by omega)
    have hb₀ : List.ofFn b₀ = chRaw J (List.ofFn fun k ↦ (c k).1) :=
      List.ext_getElem (by simp [hlen]) fun i _ _ ↦ by simp [b₀]
    have : (fun b ↦ F (b, c)) = fun b ↦
        if b = b₀ then (∏ k, chBlockWeight (c k)) * G (chRaw J (List.ofFn fun k ↦ (c k).1))
        else 0 := by
      funext b
      by_cases h : b = b₀
      · subst h
        simp [F, hb₀]
      · have : chRaw J (List.ofFn fun k ↦ (c k).1) ≠ List.ofFn b := fun h' ↦
          h (List.ofFn_injective (h'.symm.trans hb₀.symm))
        simp [F, h, this]
    rw [this]
    exact hasSum_ite_eq b₀ _
  exact (hF.hasSum.prod_fiberwise hb).tsum_eq.trans
    (((Equiv.prodComm _ _).hasSum_iff.mpr hF.hasSum).prod_fiberwise hc).tsum_eq.symm

/-- The penalty of the raw word of `β ∈ 𝔅^J`, `J = ⌊n/2⌋`, times `w((0, 0))`, is the term of the
series defining `Q^{(J)}((0, 0))`. -/
private theorem chWhiteFactor_zero_mul_chPenalty_chRaw (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    (β : Fin (n / 2) → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    chWhiteFactor n ξ ε 0 * ((∏ k, chBlockWeight (β k)) *
        chPenalty n ξ ε (chRaw (n / 2) (List.ofFn fun k ↦ (β k).1))) =
      chQFiniteTerm n ξ ε (n / 2) 0 β := by
  by_cases hc : ∀ k, chBlockWeight (β k) ≠ 0
  · rw [chPenalty_chRaw ξ ε le_rfl (fun b hb ↦ by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
        exact (β k).2) (fun b hb ↦ by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
        exact hc k)]
    have hw : ∏ k : Fin (List.ofFn fun k ↦ (β k).1).length,
        chWhiteFactor n ξ ε (chBlockPath (List.ofFn fun k ↦ (β k).1) (k + 1)) =
        ∏ i ∈ range (n / 2), chWhiteFactor n ξ ε
          (chBlockPath (List.ofFn fun k ↦ (β k).1) (i + 1)) := by
      rw [Fin.prod_univ_eq_prod_range (fun i ↦ chWhiteFactor n ξ ε
        (chBlockPath (List.ofFn fun k ↦ (β k).1) (i + 1))), List.length_ofFn]
    have hI : ∏ k : Fin (List.ofFn fun k ↦ (β k).1).length,
        chInternalWeight n ξ ε (chBlockPath (List.ofFn fun k ↦ (β k).1) k)
          (List.ofFn fun k ↦ (β k).1)[k] =
        ∏ k : Fin (n / 2), chInternalWeight n ξ ε
          (chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k) := by
      rw [← Fin.prod_congr' (fun k : Fin (n / 2) ↦ chInternalWeight n ξ ε
        (chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)) List.length_ofFn]
      refine prod_congr rfl fun k _ ↦ ?_
      simp only [Fin.getElem_fin, List.getElem_ofFn]
      rfl
    rw [hw, hI, chQFiniteTerm, prod_range_succ']
    simp only [zero_add, chBlockPath_zero]
    ring
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    rw [chQFiniteTerm, prod_eq_zero (mem_univ k) hk]
    simp

/-- **The front end.** For `ξ ∈ G_n` and `ε ≥ ε_*`, `|μ̂_n(ξ)| ≤ ∑_{h ∈ 𝒫} η(h) Q(h)`. -/
@[collatz_pos_dens "lem_ch_front_end"]
theorem norm_refLawDft_le_tsum_holdLaw_mul_chQ (n : ℕ) (ξ : ResidueGroup n) {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) :
    ‖refLawDft n ξ‖ ≤ ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε h := by
  have hS1 := summable_chEnvelopeRhs n ξ (n / 2) 1 0
  simp only [zero_add, add_comm 1] at hS1
  refine (norm_refLawDft_le_tsum_chPairFactor n ξ).trans <|
    (Summable.tsum_le_tsum (fun b ↦ mul_le_mul_of_nonneg_left
      (prod_chPairFactor_le_chPenalty_ofFn hε b) (prod_nonneg fun i _ ↦ varpi_nonneg _)) hS1
      (summable_prod_varpi_mul _ (fun _ ↦ (chPenalty_pos _ _ _ _).le)
        (chPenalty_le_one _ _ _))).trans ?_
  rw [tsum_varpi_mul_eq_tsum_chBlockWeight_mul _ _ (fun b ↦ (chPenalty_pos _ _ _ _).le)
    (chPenalty_le_one _ _ _)]
  -- the series is `Q^{(J)}((0, 0)) / w((0, 0))`
  have hw0 := chWhiteFactor_pos n ξ ε 0
  have hsum : chWhiteFactor n ξ ε 0 *
      ∑' β : Fin (n / 2) → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        (∏ k, chBlockWeight (β k)) *
          chPenalty n ξ ε (chRaw (n / 2) (List.ofFn fun k ↦ (β k).1)) =
      chQFinite n ξ ε (n / 2) 0 := by
    rw [← tsum_mul_left, chQFinite_eq_tsum]
    exact tsum_congr fun β ↦ chWhiteFactor_zero_mul_chPenalty_chRaw n ξ ε β
  have hj : ∀ p : bkPoints, 1 ≤ bkJ p.1 := fun p ↦ mem_bkPoints.mp p.2
  generalize hJ : n / 2 = J at hsum hj
  cases J with
  | zero =>
    rw [chQFinite_zero] at hsum
    rw [(mul_eq_left₀ hw0.ne').mp hsum, ← tsum_holdLaw_bkPoints]
    refine le_of_eq (tsum_congr fun p ↦ ?_)
    rw [chQ_eq_one_of_lt_bkJ n ξ ε (by have := hj p; omega), mul_one]
  | succ K =>
    rw [chQFinite_succ, mul_right_inj' hw0.ne'] at hsum
    have hb := chQ_le_mul_tsum_hasSum_blocks n ξ ε 0
    simp only [zero_add] at hb
    rw [hsum, ← hb.tsum_eq]
    refine Summable.tsum_le_tsum (fun β ↦ ?_) ?_ hb.summable
    · have hβ := mem_bkPoints.mp (chBlockPoint_mem_bkPoints β.1)
      rw [zero_add, ← chQ_eq_chQFinite n ξ ε (chBlockPoint_mem_bkPoints _) (by omega),
        mul_right_comm]
      exact mul_le_of_le_one_right (mul_nonneg (chBlockWeight_nonneg _) (chQ_nonneg _ _ _ _))
        (chInternalWeight_le_one _ _ _ _ _)
    · refine hasSum_prod_chBlockWeight_single.summable.of_nonneg_of_le (fun β ↦ ?_) fun β ↦ ?_
      · exact mul_nonneg (mul_nonneg (chBlockWeight_nonneg _) (chInternalWeight_nonneg _ _ _ _ _))
          (chQFinite_nonneg _ _ _ _ _)
      · rw [mul_assoc]
        exact mul_le_of_le_one_right (chBlockWeight_nonneg _)
          ((mul_le_of_le_one_left (chQFinite_nonneg _ _ _ _ _)
            (chInternalWeight_le_one _ _ _ _ _)).trans (chQFinite_le_one _ _ _ _ _))

end CollatzPosDens
