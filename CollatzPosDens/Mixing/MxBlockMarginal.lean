/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# Block marginals of the geometric mass

Let `i, r, n ∈ ℕ` with `i + r ≤ n` and `E ⊆ ℤ_{≥1}^r`. Then the words `(a₁, …, a_n)` whose
block `(a_{i+1}, …, a_{i+r})` lies in `E` have geometric mass
`𝐩({(a₁, …, a_n) : (a_{i+1}, …, a_{i+r}) ∈ E}) = 𝐩(E)`.

Writing `w = u v x` with `|u| = i`, `|v| = r`, `|x| = n - i - r` is a bijection
`ℤ_{≥1}^i × ℤ_{≥1}^r × ℤ_{≥1}^{n-i-r} ≃ ℤ_{≥1}^n`, and `2^{-A(w)} = 2^{-A(u)} 2^{-A(v)} 2^{-A(x)}`.
The set of such words corresponds to `v ∈ E`, so by Tonelli its mass is
`𝐩(ℤ_{≥1}^i) 𝐩(E) 𝐩(ℤ_{≥1}^{n-i-r}) = 𝐩(E)`.

## Main results

* `CollatzPosDens.geomMass_setOf_block_mem`: the block-marginal identity.

## Implementation notes

The block `(a_{i+1}, …, a_{i+r})` of a word `w` is `(w.drop i).take r`, and `E ⊆ ℤ_{≥1}^r` is
the hypothesis that every word of `E` has length `r`.

## References

* [Mazur, *Collatz positive density*], §13.5.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Splitting a word of length `n` as `u v x` with `|u| = i`, `v ∈ E` and `|x| = n - i - r`:
a bijection onto the words of length `n` whose block `(a_{i+1}, …, a_{i+r})` lies in `E`. -/
private def blockMarginalEquiv {i r n : ℕ} (hn : i + r ≤ n) {E : Set Word}
    (hE : ∀ v ∈ E, v.length = r) :
    {u : Word | u.length = i} × E × {x : Word | x.length = n - i - r} ≃
      {w : Word | w.length = n ∧ (w.drop i).take r ∈ E} where
  toFun p := ⟨p.1.1 ++ p.2.1.1 ++ p.2.2.1, by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨x, hx⟩⟩ := p
    have hv' := hE v hv
    simp only [Set.mem_ofPred_eq] at hu hx ⊢
    refine ⟨by simp [hu, hv', hx]; omega, ?_⟩
    rw [List.append_assoc, List.drop_left' hu, List.take_left' hv']
    exact hv⟩
  invFun w := (⟨w.1.take i, by simp [w.2.1]; omega⟩, ⟨(w.1.drop i).take r, w.2.2⟩,
    ⟨w.1.drop (i + r), by simp [w.2.1]; omega⟩)
  left_inv := by
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨x, hx⟩⟩
    have hv' := hE v hv
    simp only [Set.mem_ofPred_eq] at hu hx
    simp only [List.append_assoc, Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨List.take_left' hu, ?_, ?_⟩
    · rw [List.drop_left' hu, List.take_left' hv']
    · rw [← List.drop_drop, List.drop_left' hu, List.drop_left' hv']
  right_inv := by
    rintro ⟨w, hw⟩
    simp only [Subtype.mk.injEq]
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- **Block marginal.** For `i + r ≤ n` and `E ⊆ ℤ_{≥1}^r`, the words of length `n` whose block
`(a_{i+1}, …, a_{i+r})` lies in `E` have geometric mass `𝐩(E)`. -/
@[collatz_pos_dens "lem_mx_block_marginal"]
theorem geomMass_setOf_block_mem {i r n : ℕ} (hn : i + r ≤ n) {E : Set Word}
    (hE : ∀ v ∈ E, v.length = r) :
    geomMass {w : Word | w.length = n ∧ (w.drop i).take r ∈ E} = geomMass E := by
  rw [geomMass_def {w : Word | w.length = n ∧ (w.drop i).take r ∈ E},
    ← (blockMarginalEquiv hn hE).tsum_eq]
  simp only [blockMarginalEquiv, Equiv.coe_fn_mk, Word.massWeight, Word.valSum_append, pow_add]
  simp_rw [ENNReal.tsum_prod', mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have h₁ := geomMass_setOf_length_eq i
  have h₂ := geomMass_setOf_length_eq (n - i - r)
  simp only [geomMass_def, Word.massWeight] at h₁ h₂
  rw [h₁, h₂, mul_one, one_mul, geomMass_def]

end CollatzPosDens
