/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChBlockHold
public import CollatzPosDens.Renewal.RnHoldFinite
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Renewal.RnPascal

/-!
# Lists of blocks have total weight one

Let `𝔅 = ℤ^{<ω} × {4, 5}` be the set of blocks and `bw` the block weight. For every `K ∈ ℕ`,
the series `∑_{β ∈ 𝔅^K} ∏_{k=1}^K bw(βᵏ)` of nonnegative terms converges and its sum is `1`.

The case `K = 1` is the statement that the block weights form a probability distribution on
`𝔅`. Every block has a block point in the point set `𝒫` (`CollatzPosDens.bkPoints`); grouping
the blocks by their block point, the total weight of the blocks with block point `h` is the
holding-time law `η(h)`, and `η` has total mass `1` on `𝒫`. Only finitely many blocks with a
given block point have nonzero weight (they correspond to the finitely many hold words), so each
fibre is summable. The case of general `K` follows since a sum of products of nonnegative series
is the product of the sums.

## Main results

* `CollatzPosDens.hasSum_prod_chBlockWeight_single`: `∑_{β ∈ 𝔅} bw(β) = 1`.
* `CollatzPosDens.prod_chBlockWeight_nonneg`: the terms `∏_k bw(βᵏ)` are nonnegative.
* `CollatzPosDens.hasSum_prod_chBlockWeight`: `∑_{β ∈ 𝔅^K} ∏_k bw(βᵏ) = 1`, as a `HasSum`.
* `CollatzPosDens.tsum_prod_chBlockWeight`: the same identity for the `tsum`.

## Implementation notes

As in `CollatzPosDens.holdLaw_eq_tsum_chBlockWeight`, a block is a pair `List ℤ × ℤ` and
`𝔅` is the subtype of pairs whose closing letter lies in `{4, 5}`; a list of `K` blocks is a
function `Fin K → 𝔅`. The series is stated with `HasSum`, which records both its convergence
(unconditional, as is automatic for nonnegative terms) and its value.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The blocks with a given block point `(n + 1, l)` have finitely many nonzero weights. -/
private lemma summable_chBlockWeight_fiber_succ (n : ℕ) (l : ℤ) :
    Summable fun β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧
        chBlockPoint β = ((n : ℤ) + 1, l)} ↦ chBlockWeight β := by
  apply summable_of_hasFiniteSupport
  refine (((holdWords_finite (n + 1) l).image holdWordBlock).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro ⟨β, he, hpt⟩ hne
  simp only [Function.mem_support] at hne
  exact exists_mem_holdWords_holdWordBlock_eq he hpt hne

/-- The blocks with block point `h ∈ 𝒫` have total weight `η(h)`. -/
private lemma hasSum_chBlockWeight_fiber {h : ℤ × ℤ} (hh : h ∈ bkPoints) :
    HasSum (fun β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = h} ↦
      chBlockWeight β) (holdLaw h.1.toNat h.2) := by
  rw [holdLaw_eq_tsum_chBlockWeight hh]
  refine Summable.hasSum ?_
  obtain ⟨j, l⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 1 :=
    ⟨(j - 1).toNat, by rw [mem_bkPoints_mk] at hh; omega⟩
  exact summable_chBlockWeight_fiber_succ n l

/-- Blocks, sorted by their block point. -/
private def listMassSigmaEquiv : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)} ≃
    Σ p : bkPoints, {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = p.1} where
  toFun β := ⟨⟨chBlockPoint β.1, chBlockPoint_mem_bkPoints _⟩, ⟨β.1, β.2, rfl⟩⟩
  invFun x := ⟨x.2.1, x.2.2.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨p, hp⟩, ⟨β, he, hβ⟩⟩
    change chBlockPoint β = p at hβ
    subst hβ
    rfl

/-- **The block weights form a probability distribution.** `∑_{β ∈ 𝔅} bw(β) = 1`, where
`𝔅 = ℤ^{<ω} × {4, 5}`. -/
theorem hasSum_prod_chBlockWeight_single :
    HasSum (fun β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)} ↦ chBlockWeight β) 1 := by
  set f : (Σ p : bkPoints, {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧
    chBlockPoint β = p.1}) → ℝ := fun x ↦ chBlockWeight x.2.1
  have hfib : ∀ p : bkPoints, HasSum (fun β ↦ f ⟨p, β⟩) (holdLaw p.1.1.toNat p.1.2) :=
    fun p ↦ hasSum_chBlockWeight_fiber p.2
  have h0 : 0 ≤ f := fun _ ↦ chBlockWeight_nonneg _
  have hs : Summable f := by
    rw [summable_sigma_of_nonneg h0]
    refine ⟨fun p ↦ (hfib p).summable, ?_⟩
    simp_rw [(hfib _).tsum_eq]
    exact hasSum_holdLaw_bkPoints.summable
  have hf : HasSum f 1 :=
    (hs.hasSum.sigma hfib).unique hasSum_holdLaw_bkPoints ▸ hs.hasSum
  rw [← listMassSigmaEquiv.symm.hasSum_iff]
  exact hf

/-- The terms `∏_{k=1}^K bw(βᵏ)` of the series over lists of blocks are nonnegative. -/
@[collatz_pos_dens "lem_ch_block_list_mass"]
theorem prod_chBlockWeight_nonneg {K : ℕ}
    (β : Fin K → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}) :
    0 ≤ ∏ k, chBlockWeight (β k) :=
  Finset.prod_nonneg fun _ _ ↦ chBlockWeight_nonneg _

/-- **Lists of blocks have total weight one.** For every `K ∈ ℕ`, the series
`∑_{β ∈ 𝔅^K} ∏_{k=1}^K bw(βᵏ)` converges and its sum is `1`. -/
@[collatz_pos_dens "lem_ch_block_list_mass"]
theorem hasSum_prod_chBlockWeight (K : ℕ) :
    HasSum (fun β : Fin K → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)} ↦
      ∏ k, chBlockWeight (β k)) 1 := by
  simpa using hasSum_pi_fin_prod_of_nonneg hasSum_prod_chBlockWeight_single
    (fun _ ↦ chBlockWeight_nonneg _) K

/-- `∑_{β ∈ 𝔅^K} ∏_{k=1}^K bw(βᵏ) = 1`. -/
theorem tsum_prod_chBlockWeight (K : ℕ) :
    ∑' β : Fin K → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}, ∏ k, chBlockWeight (β k) = 1 :=
  (hasSum_prod_chBlockWeight K).tsum_eq

section BlockSums

open scoped ENNReal

/-- A sum over live blocks of a function vanishing on dead blocks is a sum over `𝔅`. -/
theorem tsum_liveBlocks_eq (F : List ℤ × ℤ → ℝ≥0∞)
    (hF : ∀ β, chBlockWeight β = 0 → F β = 0) :
    ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0}, F β =
      ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}, F β := by
  refine (tsum_subtype {β : List ℤ × ℤ | β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0} F).trans
    (Eq.trans ?_ (tsum_subtype {β : List ℤ × ℤ | β.2 ∈ ({4, 5} : Set ℤ)} F).symm)
  congr 1
  ext β
  by_cases h : chBlockWeight β = 0
  · simp [Set.indicator, h, hF β h]
  · simp [Set.indicator, h]

/-- A sum over `𝔅 = ℤ^{<ω} × {4, 5}`, sorted by the length of the nonclosing word. -/
theorem tsum_blocks_eq_tsum_ofFn (F : List ℤ × ℤ → ℝ≥0∞) :
    ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}, F β =
      ∑' m : ℕ, ∑' v : Fin m → ℤ, (F (List.ofFn v, 4) + F (List.ofFn v, 5)) := by
  refine (tsum_subtype {β : List ℤ × ℤ | β.2 ∈ ({4, 5} : Set ℤ)} F).trans ?_
  rw [ENNReal.tsum_prod (f := fun c e =>
    Set.indicator {β : List ℤ × ℤ | β.2 ∈ ({4, 5} : Set ℤ)} F (c, e))]
  have h : ∀ c : List ℤ, ∑' e : ℤ,
      Set.indicator {β : List ℤ × ℤ | β.2 ∈ ({4, 5} : Set ℤ)} F (c, e) = F (c, 4) + F (c, 5) := by
    intro c
    rw [tsum_eq_sum (s := {4, 5}) fun e he => ?_, Finset.sum_pair (by norm_num)]
    · simp [Set.indicator]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      simp [Set.indicator, he]
  simp_rw [h]
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma']
  rfl

end BlockSums

end CollatzPosDens
