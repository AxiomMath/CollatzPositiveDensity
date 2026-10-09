/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockHold
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpFinite
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnFpWord
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The passage lists carry the first-passage law

For a level `s : ℕ` and every `G : ℤ × ℤ → ℝ≥0∞`, the sum over the passage lists
`π ∈ trPassage s` of `trListWeight π * G (chBlockPath π π.length)` equals the sum over
`x : ℤ × ℤ` of `firstPassageLaw s x * G x`: under the weights `trListWeight`, the end point
`chBlockPath π π.length` of a passage list is distributed according to the first-passage law
`firstPassageLaw s`.

The proof sorts the lists of blocks `π` by their word of block points `π.map chBlockPoint`.
Since `trListWeight` is a product of the weights `chBlockWeight` of the blocks, and `holdLaw` at a
block point `p` is the total `chBlockWeight` of the blocks with block point `p`, the lists with
word `h` have total weight `firstPassageLawWeight h`. A live list is a passage list for level `s`
exactly when its word is a first-passage word for `s` (`IsFirstPassageWord`), and a list that is
not live has weight zero; summing over the first-passage words `h`, and then grouping them by
their sum `h.sum`, gives the right side.

## Main results

* `CollatzPosDens.tsum_trPassage_eq_tsum_firstPassageLaw`: the identity above.
* `CollatzPosDens.tsum_chBlockPoint_fiber_trListWeight`: the lists of blocks with a given
  word `h` of block points have total weight `firstPassageLawWeight h`.
* `CollatzPosDens.mem_trPassage_iff_isFirstPassageWord`: a list is a passage list for `s` iff
  its closing letters lie in `{4, 5}`, it is live, and its word of block points is a first-passage
  word for `s`.

## Implementation notes

The sums are unconditional sums in `ℝ≥0∞`, the nonnegative real weights `trListWeight π` and
`firstPassageLaw s x` entering through `ENNReal.ofReal`. A list of blocks is a list of pairs
`List ℤ × ℤ` whose closing letters lie in `{4, 5}`.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The second coordinate of a sum of points is the sum of the second coordinates. -/
private lemma sum_map_bkL (L : List (ℤ × ℤ)) : (L.map bkL).sum = L.sum.2 := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

/-- The partial sums of the levels of the block points of `π` are the levels of its block
path. -/
private lemma sum_map_bkL_take_map_chBlockPoint (π : List (List ℤ × ℤ)) (k : ℕ) :
    (((π.map chBlockPoint).take k).map bkL).sum = (chBlockPath π k).2 := by
  rw [sum_map_bkL, chBlockPath, List.map_take]

/-- A list of blocks is a passage list for level `s` iff its closing letters lie in `{4, 5}`, it
is live, and its word of block points `π.map chBlockPoint` is a first-passage word for `s`. -/
lemma mem_trPassage_iff_isFirstPassageWord {s : ℕ} {π : List (List ℤ × ℤ)} :
    π ∈ trPassage s ↔ (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive π ∧
      IsFirstPassageWord s (π.map chBlockPoint) := by
  have hend : ((π.map chBlockPoint).map bkL).sum = (chBlockPath π π.length).2 := by
    rw [← sum_map_bkL_take_map_chBlockPoint, List.take_of_length_le (by simp)]
  simp only [mem_trPassage, IsFirstPassageWord, ne_eq, List.map_eq_nil_iff, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, chBlockPoint_mem_bkPoints,
    implies_true, true_and, List.length_map, sum_map_bkL_take_map_chBlockPoint, hend]

/-- The blocks with closing letter in `{4, 5}` and block point `p ∈ bkPoints` have total
`chBlockWeight` equal to `holdLaw p.1.toNat p.2`, in `ℝ≥0∞`. -/
private lemma tsum_ofReal_chBlockWeight_fiber {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    ∑' b : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint b = p},
      ENNReal.ofReal (chBlockWeight b.1) = ENNReal.ofReal (holdLaw p.1.toNat p.2) := by
  have hs : Summable fun b : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint b = p} ↦
      chBlockWeight b.1 := by
    have h1 : Summable fun b : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)} ↦ chBlockWeight b.1 :=
      hasSum_prod_chBlockWeight_single.summable
    have hi : Function.Injective fun b : {b : List ℤ × ℤ //
        b.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint b = p} ↦
        (⟨b.1, b.2.1⟩ : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      simp only [Subtype.mk.injEq] at h
      subst h
      rfl
    simpa only [Function.comp_def] using Summable.comp_injective (α := ℝ) h1 hi
  rw [holdLaw_eq_tsum_chBlockWeight hp,
    ENNReal.ofReal_tsum_of_nonneg (fun b ↦ chBlockWeight_nonneg _) hs]

/-- **The law of block-point words.** For a word `h` of points of `bkPoints`, the lists of blocks
`π` with closing letters in `{4, 5}` and `π.map chBlockPoint = h` have total `trListWeight`
equal to `firstPassageLawWeight h`. -/
theorem tsum_chBlockPoint_fiber_trListWeight (h : List (ℤ × ℤ)) (hh : ∀ p ∈ h, p ∈ bkPoints) :
    ∑' π : {π : List (List ℤ × ℤ) //
        (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ π.map chBlockPoint = h},
      ENNReal.ofReal (trListWeight π.1) = ENNReal.ofReal (firstPassageLawWeight h) := by
  induction h with
  | nil =>
    rw [tsum_eq_single ⟨[], by simp, rfl⟩]
    · simp
    · intro x hx
      exact absurd (Subtype.ext (List.map_eq_nil_iff.mp x.2.2)) hx
  | cons p t ih =>
    have hp : p ∈ bkPoints := hh p List.mem_cons_self
    have ht : ∀ q ∈ t, q ∈ bkPoints := fun q hq ↦ hh q (List.mem_cons_of_mem _ hq)
    let e : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint b = p} ×
        {π : List (List ℤ × ℤ) // (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ π.map chBlockPoint = t} →
        {π : List (List ℤ × ℤ) //
          (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ π.map chBlockPoint = p :: t} :=
      fun x ↦ ⟨x.1.1 :: x.2.1, List.forall_mem_cons.2 ⟨x.1.2.1, x.2.2.1⟩, by
        simp [x.1.2.2, x.2.2.2]⟩
    have he : Function.Bijective e := by
      refine ⟨?_, ?_⟩
      · rintro ⟨⟨b, hb⟩, ⟨π, hπ⟩⟩ ⟨⟨b', hb'⟩, ⟨π', hπ'⟩⟩ hbb
        simp only [e, Subtype.mk.injEq, List.cons.injEq] at hbb
        obtain ⟨rfl, rfl⟩ := hbb
        rfl
      · rintro ⟨_ | ⟨b, π⟩, hc, hm⟩
        · simp at hm
        · simp only [List.map_cons, List.cons.injEq] at hm
          simp only [List.forall_mem_cons] at hc
          exact ⟨(⟨b, hc.1, hm.1⟩, ⟨π, hc.2, hm.2⟩), rfl⟩
    rw [← (Equiv.ofBijective e he).tsum_eq]
    simp only [Equiv.ofBijective_apply, e, trListWeight_cons,
      ENNReal.ofReal_mul (chBlockWeight_nonneg _)]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih ht, ENNReal.tsum_mul_right, tsum_ofReal_chBlockWeight_fiber hp,
      firstPassageLawWeight_cons, ENNReal.ofReal_mul (holdLaw_nonneg _ _)]

open Classical in
/-- **The passage lists carry the first-passage law.** For `s : ℕ` and `G : ℤ × ℤ → ℝ≥0∞`, the
sum over `π ∈ trPassage s` of `trListWeight π * G (chBlockPath π π.length)` equals the sum over
`x : ℤ × ℤ` of `firstPassageLaw s x * G x`. -/
@[collatz_pos_dens "lem_tr_passage_law"]
theorem tsum_trPassage_eq_tsum_firstPassageLaw (s : ℕ) (G : ℤ × ℤ → ℝ≥0∞) :
    ∑' π : trPassage s, ENNReal.ofReal (trListWeight π.1) * G (chBlockPath π.1 π.1.length) =
      ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x) * G x := by
  set K : List (ℤ × ℤ) → ℝ≥0∞ := fun h ↦
    if IsFirstPassageWord s h then G h.sum else 0 with hK
  have hL : ∑' π : trPassage s, ENNReal.ofReal (trListWeight π.1) *
        G (chBlockPath π.1 π.1.length) =
      ∑' h : List (ℤ × ℤ), ENNReal.ofReal (firstPassageLawWeight h) * K h := by
    rw [tsum_subtype (trPassage s)
      (fun π ↦ ENNReal.ofReal (trListWeight π) * G (chBlockPath π π.length))]
    have hpt : ∀ π : List (List ℤ × ℤ), (trPassage s).indicator
        (fun π ↦ ENNReal.ofReal (trListWeight π) * G (chBlockPath π π.length)) π =
        ∑' h : List (ℤ × ℤ), (if (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ π.map chBlockPoint = h
          then ENNReal.ofReal (trListWeight π) else 0) * K h := by
      intro π
      rw [tsum_eq_single (π.map chBlockPoint) (fun h hne ↦ by simp [Ne.symm hne])]
      have hend : (π.map chBlockPoint).sum = chBlockPath π π.length :=
        (chBlockPath_of_length_le π le_rfl).symm
      by_cases hπ : π ∈ trPassage s
      · obtain ⟨hc, -, hfp⟩ := mem_trPassage_iff_isFirstPassageWord.mp hπ
        rw [Set.indicator_of_mem hπ, ite_eq_left ⟨hc, rfl⟩, hK]
        simp only [ite_eq_left hfp, hend]
      · rw [Set.indicator_of_notMem hπ]
        by_cases hc : ∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)
        · by_cases hfp : IsFirstPassageWord s (π.map chBlockPoint)
          · have hl : ¬ TrLive π := fun hl ↦
              hπ (mem_trPassage_iff_isFirstPassageWord.mpr ⟨hc, hl, hfp⟩)
            have h0 : trListWeight π = 0 := by
              rw [trListWeight_eq_zero_iff]
              simpa [TrLive] using hl
            rw [h0, ENNReal.ofReal_zero]
            simp
          · rw [hK]
            simp only [ite_eq_right hfp, mul_zero]
        · rw [ite_eq_right fun h ↦ hc h.1, zero_mul]
    simp_rw [hpt]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun h ↦ ?_
    rw [ENNReal.tsum_mul_right]
    by_cases hfp : IsFirstPassageWord s h
    · congr 1
      rw [← tsum_chBlockPoint_fiber_trListWeight h fun p hp ↦ hfp.mem_bkPoints hp]
      refine Eq.trans ?_ (tsum_subtype {π : List (List ℤ × ℤ) |
        (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ π.map chBlockPoint = h}
        (fun π ↦ ENNReal.ofReal (trListWeight π))).symm
      refine tsum_congr fun π ↦ ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    · simp [hK, hfp]
  have hR : ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x) * G x =
      ∑' h : List (ℤ × ℤ), ENNReal.ofReal (firstPassageLawWeight h) * K h := by
    have hF : ∀ x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x) =
        ∑' h : List (ℤ × ℤ), if IsFirstPassageWord s h ∧ h.sum = x
          then ENNReal.ofReal (firstPassageLawWeight h) else 0 := by
      intro x
      rw [firstPassageLaw, ENNReal.ofReal_tsum_of_nonneg
        (fun h ↦ firstPassageLawWeight_nonneg _)
        (summable_of_hasFiniteSupport (firstPassageLaw_finite_support s x))]
      refine Eq.trans (tsum_subtype {h : List (ℤ × ℤ) | IsFirstPassageWord s h ∧ h.sum = x}
        (fun h ↦ ENNReal.ofReal (firstPassageLawWeight h))) ?_
      refine tsum_congr fun h ↦ ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simp_rw [hF, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun h ↦ ?_
    rw [tsum_eq_single h.sum (fun x hx ↦ by simp [Ne.symm hx])]
    by_cases hfp : IsFirstPassageWord s h <;> simp [hK, hfp]
  rw [hL, hR]

end CollatzPosDens
