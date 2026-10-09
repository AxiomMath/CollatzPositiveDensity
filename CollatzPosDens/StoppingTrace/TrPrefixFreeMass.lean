/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrSublist
public import CollatzPosDens.StoppingTrace.TrListSplit
public import CollatzPosDens.CharSum.ChBlockListMass

/-!
# Prefix-free families of block lists

Let `M ∈ ℕ` and let `F` be a set of block lists, each of length at most `M`, such that no element
of `F` is a proper prefix of another element of `F`. Then `∑_{u ∈ F} bw^⊗(u) ≤ 1`. This is a
Kraft-type inequality for the product block weights.

For `u ∈ F` of length `q ≤ M`, the lists `β ∈ 𝔅^M` with `β_{[1,q]} = u` carry total weight
`bw^⊗(u) ∑_{f ∈ 𝔅^{M-q}} bw^⊗(f) = bw^⊗(u)`, by splitting a block list at `q` and since lists of
blocks have total weight one. Prefix-freeness makes these cylinders pairwise disjoint, so the sum
over `F` is at most the total weight `1` of `𝔅^M`.

## Main results

* `CollatzPosDens.blockListEquivFin`: lists in `𝔅^K` are the tuples `Fin K → 𝔅`.
* `CollatzPosDens.tsum_ofReal_trListWeight_length_eq`:
  `∑_{β ∈ 𝔅^K} bw^⊗(β) = 1` for lists.
* `CollatzPosDens.tsum_trListWeight_le_one_of_prefixFree_cylinder`:
  the cylinder over `u ∈ 𝔅^q` inside `𝔅^N`, `q ≤ N`, has weight `bw^⊗(u)`.
* `CollatzPosDens.tsum_trListWeight_le_one_of_prefixFree`: the prefix-free mass bound.

## Implementation notes

As in `CollatzPosDens.tsum_trListWeight_trSublist`, a block list is a
`List (List ℤ × ℤ)` all of whose closing letters lie in `{4, 5}`, and `𝔅^K` is the subtype of
such lists of length `K`. The family `F` is a `Set` of lists, and the sum is the unconditional
sum in `[0, ∞]` of the nonnegative real weights `bw^⊗(u)` embedded through `ENNReal.ofReal`.
"No element is a proper prefix of another" is stated as: `u <+: v` for `u, v ∈ F` forces
`u = v`.

## References

* [Mazur, *Collatz positive density*], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- Lists of length `K` of blocks are tuples `Fin K → 𝔅`. -/
def blockListEquivFin (K : ℕ) :
    {u : List (List ℤ × ℤ) //
      u.length = K ∧ ∀ x ∈ u, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}} ≃
      (Fin K → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}) where
  toFun u k := ⟨u.1[(k : ℕ)]'(by have := u.2.1; omega), u.2.2 _ (List.getElem_mem _)⟩
  invFun x := ⟨List.ofFn fun k ↦ (x k).1, by simp, fun y hy ↦ by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
    exact (x k).2⟩
  left_inv u := by
    obtain ⟨u, rfl, -⟩ := u
    exact Subtype.ext (List.ofFn_getElem)
  right_inv x := by
    funext k
    simp

/-- **Lists of blocks have total weight one**, for lists: `∑_{β ∈ 𝔅^K} bw^⊗(β) = 1`. -/
theorem tsum_ofReal_trListWeight_length_eq (K : ℕ) :
    ∑' β : {β : List (List ℤ × ℤ) //
        β.length = K ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (trListWeight β.1) = 1 := by
  rw [← (blockListEquivFin K).symm.tsum_eq]
  simp only [blockListEquivFin, Equiv.coe_fn_symm_mk, trListWeight_ofFn]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ prod_chBlockWeight_nonneg x)
    (hasSum_prod_chBlockWeight K).summable, tsum_prod_chBlockWeight, ENNReal.ofReal_one]

/-- The cylinder `{β ∈ 𝔅^N : β_{[1,q]} = u}` over `u ∈ 𝔅^q`, `q ≤ N`, has weight `bw^⊗(u)`. -/
theorem tsum_trListWeight_le_one_of_prefixFree_cylinder {N : ℕ} (u : List (List ℤ × ℤ))
    (hu : ∀ x ∈ u, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}) (hN : u.length ≤ N) :
    ∑' β : {β : List (List ℤ × ℤ) //
        β.length = N ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (trListWeight β.1) * (if β.1.take u.length = u then 1 else 0) =
      ENNReal.ofReal (trListWeight u) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hN
  have h := tsum_trListWeight_trSublist {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)} u.length b
    (fun u' _ ↦ if u' = u then 1 else 0)
  simp only [trSublist_one] at h
  rw [h]
  have hu' : (∀ x ∈ u, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}) := hu
  rw [tsum_eq_single (⟨u, rfl, hu'⟩ : {u' : List (List ℤ × ℤ) //
      u'.length = u.length ∧ ∀ x ∈ u', x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}})]
  · simp only [ite_true, mul_one]
    rw [ENNReal.tsum_mul_left, tsum_ofReal_trListWeight_length_eq, mul_one]
  · intro v hv
    have : v.1 ≠ u := fun h ↦ hv (Subtype.ext h)
    simp [this]

/-- **Prefix-free families of block lists.** If `F` is a set of block lists, each of length at
most `M`, no element of which is a proper prefix of another, then `∑_{u ∈ F} bw^⊗(u) ≤ 1`. -/
@[collatz_pos_dens "lem_tr_prefix_free_mass"]
theorem tsum_trListWeight_le_one_of_prefixFree (M : ℕ) (F : Set (List (List ℤ × ℤ)))
    (hblock : ∀ u ∈ F, ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) (hlen : ∀ u ∈ F, u.length ≤ M)
    (hpf : InformationTheory.IsPrefixFree F) :
    ∑' u : F, ENNReal.ofReal (trListWeight u.1) ≤ 1 := by
  calc ∑' u : F, ENNReal.ofReal (trListWeight u.1)
      = ∑' u : F, ∑' β : {β : List (List ℤ × ℤ) //
          β.length = M ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}},
          ENNReal.ofReal (trListWeight β.1) *
            (if β.1.take u.1.length = u.1 then 1 else 0) :=
        tsum_congr fun u ↦
          (tsum_trListWeight_le_one_of_prefixFree_cylinder u.1 (hblock u.1 u.2) (hlen u.1 u.2)).symm
    _ = ∑' β : {β : List (List ℤ × ℤ) //
          β.length = M ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}},
          ENNReal.ofReal (trListWeight β.1) *
            ∑' u : F, (if β.1.take u.1.length = u.1 then 1 else 0) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun β ↦ ENNReal.tsum_mul_left
    _ ≤ ∑' β : {β : List (List ℤ × ℤ) //
          β.length = M ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}},
          ENNReal.ofReal (trListWeight β.1) * 1 := by
        refine ENNReal.tsum_le_tsum fun β ↦ mul_le_mul_right ?_ _
        by_cases hex : ∃ w : F, β.1.take w.1.length = w.1
        · obtain ⟨w, hw⟩ := hex
          rw [tsum_eq_single w]
          · simp [hw]
          · intro v hv
            refine ite_eq_right fun hv' ↦ ?_
            apply hv
            have hwp : w.1 <+: β.1 := hw ▸ List.take_prefix _ _
            have hvp : v.1 <+: β.1 := hv' ▸ List.take_prefix _ _
            rcases le_total v.1.length w.1.length with h | h
            · exact Subtype.ext (hpf _ v.2 _ w.2 (List.prefix_of_prefix_length_le hvp hwp h))
            · exact Subtype.ext (hpf _ w.2 _ v.2
                (List.prefix_of_prefix_length_le hwp hvp h)).symm
        · push Not at hex
          simp [hex]
    _ = 1 := by simp_rw [mul_one]; exact tsum_ofReal_trListWeight_length_eq M

end CollatzPosDens
