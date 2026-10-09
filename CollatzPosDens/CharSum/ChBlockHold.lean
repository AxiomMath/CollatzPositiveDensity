/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnPascal

/-!
# The holding-time law is the law of block points

For every lattice point `h ∈ 𝒫`, the holding-time law is the total weight of the blocks with
block point `h`:
`η(h) = ∑_{β ∈ 𝔅, bpt(β) = h} bw(β)`,
where `𝔅 = ℤ^{<ω} × {4, 5}` is the set of blocks.

Writing `h = (j, l)`, a block `(c, e)` has block point `(j, l)` exactly when `|c| = j - 1` and
`c₁ + ⋯ + c_{j-1} + e = l`. Its weight `ϖ(e) ∏ [cᵢ ∉ {4, 5}] ϖ(cᵢ)` vanishes unless every `cᵢ`
is at least `2` and avoids `{4, 5}`, and then the word `(c₁, …, c_{j-1}, e)` is a hold word in
`𝒞_{j,l}` whose summand in `η(j, l)` is the weight of the block. The map
`(c, e) ↦ (c₁, …, c_{j-1}, e)` is a bijection between the blocks of nonzero weight with block
point `(j, l)` and the hold words, which gives the identity.

## Main results

* `CollatzPosDens.holdLaw_eq_tsum_chBlockWeight`: `η(h) = ∑_{bpt(β) = h} bw(β)` for
  `h ∈ 𝒫`.
* `CollatzPosDens.holdLaw_succ_eq_tsum_chBlockWeight`: the same identity at
  `h = (j + 1, l)` with `j : ℕ`.
* `CollatzPosDens.exists_mem_holdWords_holdWordBlock_eq`: every block of nonzero weight with
  block point `(j + 1, l)` is the block `holdWordBlock w` of a hold word `w ∈ 𝒞_{j+1,l}`.

## Implementation notes

A block is a pair `List ℤ × ℤ`, and `𝔅` is the subtype of pairs whose closing letter lies in
`{4, 5}`; the sum over blocks with block point `h` is a `tsum` over the subtype of such blocks
with `chBlockPoint β = h`. A point `h ∈ 𝒫 ⊆ ℤ × ℤ` has `h.1 ≥ 1`, and `η(h)` is
`holdLaw h.1.toNat h.2`. The identity holds as an equality of `tsum`s without any summability
hypothesis: only finitely many blocks with a given block point have nonzero weight, and they are
matched with the hold words through `tsum_eq_tsum_of_ne_zero_bij`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The block `((c₁, …, c_j), c_{j+1})` attached to a word `c ∈ ℤ^{j+1}`. -/
def holdWordBlock {n : ℕ} (c : Fin (n + 1) → ℤ) : List ℤ × ℤ :=
  (List.ofFn fun k : Fin n ↦ c k.castSucc, c (Fin.last n))

/-- The map `c ↦ holdWordBlock c` from words `ℤ^{n+1}` to blocks is injective. -/
theorem holdWordBlock_injective {n : ℕ} :
    Function.Injective (holdWordBlock (n := n)) := by
  intro c c' h
  simp only [holdWordBlock, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext k
  induction k using Fin.lastCases with
  | last => exact h2
  | cast k => exact congrFun (List.ofFn_injective h1) k

/-- A block of nonzero weight with closing letter in `{4, 5}` and block point `(n + 1, l)` is the
block of a hold word of `𝒞_{n+1, l}`. -/
theorem exists_mem_holdWords_holdWordBlock_eq {n : ℕ} {l : ℤ} {β : List ℤ × ℤ}
    (he : β.2 ∈ ({4, 5} : Set ℤ)) (hpt : chBlockPoint β = ((n : ℤ) + 1, l))
    (hne : chBlockWeight β ≠ 0) : ∃ w ∈ holdWords (n + 1) l, holdWordBlock w = β := by
  obtain ⟨c, e⟩ := β
  simp only [chBlockPoint, Prod.mk.injEq] at hpt
  obtain ⟨hlen, hsum⟩ := hpt
  obtain rfl : c.length = n := by omega
  have hc : ∀ a ∈ c, 2 ≤ a ∧ a ∉ ({4, 5} : Set ℤ) := fun a ha ↦
    ⟨two_le_of_chBlockWeight_ne_zero hne ha, fun h ↦ hne (chBlockWeight_eq_zero_of_mem ha h)⟩
  let w : Fin (c.length + 1) → ℤ := Fin.snoc (α := fun _ ↦ ℤ) c.get e
  have hw : w ∈ holdWords (c.length + 1) l := by
    rw [mem_holdWords_succ]
    refine ⟨fun i ↦ ?_, ?_, ?_⟩
    · simpa [w] using hc _ (List.get_mem c i)
    · simpa [w] using he
    · simp only [w, Fin.snoc_castSucc, Fin.snoc_last]
      rw [← List.sum_ofFn, List.ofFn_get]
      exact hsum
  refine ⟨w, hw, ?_⟩
  simp only [holdWordBlock, w, Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get]

/-- The identity `η(j + 1, l) = ∑_{bpt(β) = (j + 1, l)} bw(β)`, the sum running over the blocks
`β ∈ 𝔅 = ℤ^{<ω} × {4, 5}`. -/
theorem holdLaw_succ_eq_tsum_chBlockWeight (n : ℕ) (l : ℤ) :
    holdLaw (n + 1) l =
      ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = ((n : ℤ) + 1, l)},
        chBlockWeight β := by
  rw [holdLaw_def]
  symm
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun c ↦ ⟨holdWordBlock c.1.1, ?_, ?_⟩) ?_ ?_ ?_
  · exact holdWords_last_mem c.1.2
  · obtain ⟨-, -, hs⟩ := mem_holdWords_succ.1 c.1.2
    simpa only [holdWordBlock, chBlockPoint, List.length_ofFn, List.sum_ofFn, Prod.mk.injEq,
      true_and] using hs
  · exact fun _ _ h ↦ Subtype.ext (Subtype.ext (holdWordBlock_injective (congrArg Subtype.val h)))
  · rintro ⟨β, he, hpt⟩ hne
    simp only [Function.mem_support] at hne
    obtain ⟨w, hw, rfl⟩ := exists_mem_holdWords_holdWordBlock_eq he hpt hne
    have hgw : (∏ i, varpi (w i)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
      rw [varpi_of_two_le (holdWords_two_le hw i)]
      have : (2 : ℝ) ≤ (w i : ℝ) := by exact_mod_cast holdWords_two_le hw i
      have : (0 : ℝ) < (w i : ℝ) - 1 := by linarith
      positivity
    exact ⟨⟨⟨w, hw⟩, hgw⟩, rfl⟩
  · rintro ⟨⟨c, hc⟩, -⟩
    obtain ⟨hi, -, -⟩ := mem_holdWords_succ.1 hc
    simp only [holdWordBlock]
    rw [chBlockWeight_of_forall_notMem _ fun a ha ↦ ?_, Fin.prod_univ_castSucc, List.map_ofFn,
      List.prod_ofFn, mul_comm]
    · rfl
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
      exact (hi k).2

/-- **The holding-time law is the law of block points.** For every `h ∈ 𝒫`,
`η(h) = ∑_{β ∈ 𝔅, bpt(β) = h} bw(β)`, where `𝔅 = ℤ^{<ω} × {4, 5}`. -/
@[collatz_pos_dens "lem_ch_block_hold"]
theorem holdLaw_eq_tsum_chBlockWeight {h : ℤ × ℤ} (hh : h ∈ bkPoints) :
    holdLaw h.1.toNat h.2 =
      ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = h},
        chBlockWeight β := by
  obtain ⟨j, l⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 1 :=
    ⟨(j - 1).toNat, by rw [mem_bkPoints_mk] at hh; omega⟩
  rw [show ((n : ℤ) + 1).toNat = n + 1 by omega]
  exact holdLaw_succ_eq_tsum_chBlockWeight n l

end CollatzPosDens
