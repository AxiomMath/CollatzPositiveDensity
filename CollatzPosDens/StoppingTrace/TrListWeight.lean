/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockWeight
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The weight of a block list

For a list `β = (β¹, …, β^N)` of blocks, its weight is the product of the weights of its blocks,
`bw^⊗(β) = ∏_{k=1}^N bw(βᵏ)`, the empty product being `1`. The weight is multiplicative under
concatenation: `bw^⊗(β ++ γ) = bw^⊗(β) · bw^⊗(γ)`.

## Main definitions

* `CollatzPosDens.trListWeight`: the weight `bw^⊗(β)` of a block list.

## Main results

* `CollatzPosDens.trListWeight_nil`, `CollatzPosDens.trListWeight_cons`,
  `CollatzPosDens.trListWeight_append`: the empty list has weight `1`, and the weight is
  multiplicative.
* `CollatzPosDens.trListWeight_eq_prod_fin`: `bw^⊗(β) = ∏_{k < N} bw(βᵏ)` indexed by `Fin N`.
* `CollatzPosDens.trListWeight_nonneg`: the weight is nonnegative.
* `CollatzPosDens.trListWeight_ne_zero_iff`: the weight is nonzero iff every block has
  nonzero weight.

## Implementation notes

A list in `𝔅^N` is modelled as a `List (List ℤ × ℤ)` of length `N`; the length `N` is then
`β.length` rather than a separate parameter. The weight is real-valued, like the block weight `bw`
it is built from; being nonnegative, it embeds in `[0, ∞]` in sums of nonnegative terms.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weight `bw^⊗(β) = ∏_{k=1}^N bw(βᵏ)` of a block list `β = (β¹, …, β^N)`
(empty product `1`). -/
@[collatz_pos_dens "def_tr_list_weight"]
noncomputable def trListWeight (β : List (List ℤ × ℤ)) : ℝ :=
  (β.map chBlockWeight).prod

/-- The weight of a block list is the product of the weights of its blocks. -/
lemma trListWeight_def (β : List (List ℤ × ℤ)) :
    trListWeight β = (β.map chBlockWeight).prod :=
  rfl

/-- The empty block list has weight `1`. -/
@[simp]
lemma trListWeight_nil : trListWeight [] = 1 := rfl

/-- `bw^⊗(b :: β) = bw(b) · bw^⊗(β)`. -/
@[simp]
lemma trListWeight_cons (b : List ℤ × ℤ) (β : List (List ℤ × ℤ)) :
    trListWeight (b :: β) = chBlockWeight b * trListWeight β := by
  simp [trListWeight]

/-- A one-block list has the weight of its block. -/
lemma trListWeight_singleton (b : List ℤ × ℤ) : trListWeight [b] = chBlockWeight b := by
  simp

/-- The weight is multiplicative under concatenation: `bw^⊗(β ++ γ) = bw^⊗(β) · bw^⊗(γ)`. -/
@[simp]
lemma trListWeight_append (β γ : List (List ℤ × ℤ)) :
    trListWeight (β ++ γ) = trListWeight β * trListWeight γ := by
  simp [trListWeight]

/-- Appending a block `b` multiplies the weight by `bw(b)`. -/
lemma trListWeight_concat (β : List (List ℤ × ℤ)) (b : List ℤ × ℤ) :
    trListWeight (β ++ [b]) = trListWeight β * chBlockWeight b := by
  simp

/-- The weight of the list `(f 0, …, f (N-1))` is `∏_{k < N} bw(f k)`. -/
lemma trListWeight_ofFn {N : ℕ} (f : Fin N → List ℤ × ℤ) :
    trListWeight (List.ofFn f) = ∏ k, chBlockWeight (f k) := by
  rw [trListWeight, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The weight of a block list as a product indexed by `Fin N`, `N = β.length`. -/
lemma trListWeight_eq_prod_fin (β : List (List ℤ × ℤ)) :
    trListWeight β = ∏ k : Fin β.length, chBlockWeight β[k] := by
  conv_lhs => rw [← List.ofFn_getElem (xs := β)]
  exact trListWeight_ofFn _

/-- The weight of a block list is nonnegative. -/
lemma trListWeight_nonneg (β : List (List ℤ × ℤ)) : 0 ≤ trListWeight β :=
  List.prod_nonneg fun x hx ↦ by
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact chBlockWeight_nonneg b

/-- The weight of a block list is nonzero iff every block in it has nonzero weight. -/
lemma trListWeight_ne_zero_iff {β : List (List ℤ × ℤ)} :
    trListWeight β ≠ 0 ↔ ∀ b ∈ β, chBlockWeight b ≠ 0 := by
  simp [trListWeight, List.prod_eq_zero_iff]

/-- The weight of a block list vanishes iff some block in it has weight zero. -/
lemma trListWeight_eq_zero_iff {β : List (List ℤ × ℤ)} :
    trListWeight β = 0 ↔ ∃ b ∈ β, chBlockWeight b = 0 := by
  simp [trListWeight, List.prod_eq_zero_iff]

end CollatzPosDens
