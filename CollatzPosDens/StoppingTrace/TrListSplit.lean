/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrSublist
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Splitting a block list

For `a, b ∈ ℕ` and `Ψ : 𝔅^a × 𝔅^b → [0, ∞]`,
`∑_{β ∈ 𝔅^{a+b}} bw^⊗(β) Ψ(β_{[1,a]}, β_{[a+1,a+b]})
  = ∑_{u ∈ 𝔅^a} ∑_{f ∈ 𝔅^b} bw^⊗(u) bw^⊗(f) Ψ(u, f)`.
Concatenation `(u, f) ↦ uf` is a bijection `𝔅^a × 𝔅^b → 𝔅^{a+b}`, inverse to
`β ↦ (β_{[1,a]}, β_{[a+1,a+b]})`, and the list weight is multiplicative under it; reindexing the
left side along it gives the right side.

## Main results

* `CollatzPosDens.tsum_trListWeight_trSublist`: the splitting identity.

## Implementation notes

A list in `𝔅^N` is a `List (List ℤ × ℤ)` of length `N` all of whose entries lie in the set `B`
of blocks, and `𝔅^N` is the corresponding subtype. The identity is proved for an arbitrary set
`B` of pairs: the block set `𝔅 = ℤ^{<ω} × {4, 5}` is the case `B = {β | β.2 ∈ {4, 5}}`. The
weight `bw^⊗` is real and nonnegative, and enters the sums of `[0, ∞]`-valued terms through
`ENNReal.ofReal`; all sums are unconditional sums in `[0, ∞]`. The function `Ψ` is taken on all
pairs of lists, which generalizes functions on `𝔅^a × 𝔅^b` (extend by `0`): only its values on
`𝔅^a × 𝔅^b` enter.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- Concatenation `𝔅^a × 𝔅^b ≃ 𝔅^{a+b}`, inverse to `β ↦ (β_{[1,a]}, β_{[a+1,a+b]})`. -/
private def appendEquiv {α : Type*} (B : Set α) (a b : ℕ) :
    {u : List α // u.length = a ∧ ∀ x ∈ u, x ∈ B} ×
        {f : List α // f.length = b ∧ ∀ x ∈ f, x ∈ B} ≃
      {β : List α // β.length = a + b ∧ ∀ x ∈ β, x ∈ B} where
  toFun p := ⟨p.1.1 ++ p.2.1, by simp [p.1.2.1, p.2.2.1], fun x hx ↦ by
    rcases List.mem_append.mp hx with h | h
    exacts [p.1.2.2 x h, p.2.2.2 x h]⟩
  invFun β :=
    (⟨trSublist β.1 1 a, by
        rw [length_trSublist le_rfl (by omega)]; omega,
        fun x hx ↦ β.2.2 x (mem_of_mem_trSublist hx)⟩,
      ⟨trSublist β.1 (a + 1) (a + b), by
        rw [length_trSublist (by omega) (by omega)]; omega,
        fun x hx ↦ β.2.2 x (mem_of_mem_trSublist hx)⟩)
  left_inv p := by
    obtain ⟨⟨u, hu, -⟩, ⟨f, hf, -⟩⟩ := p
    subst hu hf
    ext1
    · exact Subtype.ext (trSublist_append_left u f)
    · exact Subtype.ext (trSublist_append_right u f)
  right_inv β := by
    obtain ⟨β, hβ, -⟩ := β
    refine Subtype.ext ?_
    change trSublist β 1 a ++ trSublist β (a + 1) (a + b) = β
    rw [trSublist_append_trSublist β le_rfl (by omega) (by omega), ← hβ, trSublist_one_length]

/-- **Splitting a block list.** For `Ψ` with values in `[0, ∞]`,
`∑_{β ∈ 𝔅^{a+b}} bw^⊗(β) Ψ(β_{[1,a]}, β_{[a+1,a+b]})
  = ∑_{u ∈ 𝔅^a} ∑_{f ∈ 𝔅^b} bw^⊗(u) bw^⊗(f) Ψ(u, f)`,
where `𝔅^N` is the set of lists of length `N` with entries in a set `B` of blocks. -/
@[collatz_pos_dens "lem_tr_list_split"]
theorem tsum_trListWeight_trSublist (B : Set (List ℤ × ℤ)) (a b : ℕ)
    (Ψ : List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞) :
    ∑' β : {β : List (List ℤ × ℤ) // β.length = a + b ∧ ∀ x ∈ β, x ∈ B},
        ENNReal.ofReal (trListWeight β.1) *
          Ψ (trSublist β.1 1 a) (trSublist β.1 (a + 1) (a + b)) =
      ∑' u : {u : List (List ℤ × ℤ) // u.length = a ∧ ∀ x ∈ u, x ∈ B},
        ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧ ∀ x ∈ f, x ∈ B},
          ENNReal.ofReal (trListWeight u.1) * ENNReal.ofReal (trListWeight f.1) * Ψ u.1 f.1 := by
  rw [← ENNReal.tsum_prod, ← (appendEquiv B a b).tsum_eq]
  refine tsum_congr fun p ↦ ?_
  obtain ⟨⟨u, hu, -⟩, ⟨f, hf, -⟩⟩ := p
  subst hu hf
  change ENNReal.ofReal (trListWeight (u ++ f)) *
      Ψ (trSublist (u ++ f) 1 u.length) (trSublist (u ++ f) (u.length + 1)
        (u.length + f.length)) = _
  rw [trSublist_append_left, trSublist_append_right, trListWeight_append,
    ENNReal.ofReal_mul (trListWeight_nonneg u)]

end CollatzPosDens
