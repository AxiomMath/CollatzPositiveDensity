/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.StoppingTrace.TrFreshLaw

/-!
# The exceptional event of a block of offsets

Fix `n ≥ 1` and `J = ⌊n/2⌋`. For an entry point `e ∈ 𝒫`, a level `G ∈ ℕ`, a number of offsets
`v ≤ J` and a real `X > 0`, the *exceptional event* `Ex_{e,G,v,X}` is the set of atoms
`a = ((r, ℓ), β) ∈ 𝒜_n` of the fresh law `μ_{e,G}` for which at least one of the following holds:

* the first passage overshoots: `ℓ - G ≥ X`;
* the first `v` blocks climb high: `l(β¹) + ⋯ + l(βᵛ) ≥ X`;
* the first passage lands far from the drift: `|r - G/4| ≥ G^{3/5}`;
* the first `v` blocks move far: `j(β¹) + ⋯ + j(βᵛ) ≥ G^{3/5}`.

Here `j(βᵏ)` and `l(βᵏ)` are the coordinates of the block point `bpt(βᵏ)`.

## Main definitions

* `CollatzPosDens.c3Exceptional`: the event `Ex_{e,G,v,X}`, a set of atoms of `𝒜_n`.

## Main results

* `CollatzPosDens.mem_c3Exceptional`: the membership criterion.
* `CollatzPosDens.c3Exceptional_subset_trAtoms`: `Ex_{e,G,v,X} ⊆ 𝒜_n`.
* `CollatzPosDens.c3Exceptional_anti`: the event shrinks as `X` grows.

## Implementation notes

Atoms are elements of `(ℕ × ℤ) × List (List ℤ × ℤ)`, and the atoms of `μ_{e,G}` are those of
`𝒜_n = trAtoms n`; membership in `𝒜_n` is the first conjunct of the definition. The sums
`∑_{k ≤ v}` run over the first `v` blocks `β¹, …, βᵛ`, that is over the list `β.take v`. All four
conditions are read in `ℝ`, where `G / 4` is real division and `G^{3/5}` is `Real.rpow`. The
hypotheses `e ∈ 𝒫`, `v ≤ J` and `X > 0` play no role in the definition and are omitted; the
entry point `e` is an explicit but unused argument, as for the fresh law `μ_{e,G}` itself.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exceptional event `Ex_{e,G,v,X}`: the atoms `a = ((r, ℓ), β)` of `μ_{e,G}` (that is, of
`𝒜_n`) with `ℓ - G ≥ X`, or `∑_{k ≤ v} l(βᵏ) ≥ X`, or `|r - G/4| ≥ G^{3/5}`, or
`∑_{k ≤ v} j(βᵏ) ≥ G^{3/5}`, where `(j(βᵏ), l(βᵏ)) = bpt(βᵏ)`. -/
@[collatz_pos_dens "def_c3_eprime"]
def c3Exceptional (n : ℕ) (_e : ℤ × ℤ) (G v : ℕ) (X : ℝ) :
    Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧
    (X ≤ (a.1.2 : ℝ) - G ∨
      X ≤ (((a.2.take v).map fun b => bkL (chBlockPoint b)).sum : ℝ) ∨
      (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(a.1.1 : ℝ) - (G : ℝ) / 4| ∨
      (G : ℝ) ^ ((3 : ℝ) / 5) ≤ (((a.2.take v).map fun b => bkJ (chBlockPoint b)).sum : ℝ))}

/-- Membership in the exceptional event. -/
theorem mem_c3Exceptional {n : ℕ} {e : ℤ × ℤ} {G v : ℕ} {X : ℝ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ c3Exceptional n e G v X ↔ a ∈ trAtoms n ∧
      (X ≤ (a.1.2 : ℝ) - G ∨
        X ≤ (((a.2.take v).map fun b => bkL (chBlockPoint b)).sum : ℝ) ∨
        (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(a.1.1 : ℝ) - (G : ℝ) / 4| ∨
        (G : ℝ) ^ ((3 : ℝ) / 5) ≤ (((a.2.take v).map fun b => bkJ (chBlockPoint b)).sum : ℝ)) :=
  Iff.rfl

/-- Membership in the exceptional event, for an atom written `((r, ℓ), β)`. -/
@[simp]
theorem mk_mem_c3Exceptional {n : ℕ} {e : ℤ × ℤ} {G v : ℕ} {X : ℝ} {r : ℕ} {ℓ : ℤ}
    {β : List (List ℤ × ℤ)} :
    ((r, ℓ), β) ∈ c3Exceptional n e G v X ↔ ((r, ℓ), β) ∈ trAtoms n ∧
      (X ≤ (ℓ : ℝ) - G ∨
        X ≤ (((β.take v).map fun b => bkL (chBlockPoint b)).sum : ℝ) ∨
        (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(r : ℝ) - (G : ℝ) / 4| ∨
        (G : ℝ) ^ ((3 : ℝ) / 5) ≤ (((β.take v).map fun b => bkJ (chBlockPoint b)).sum : ℝ)) :=
  Iff.rfl

/-- The exceptional event consists of atoms of `𝒜_n`. -/
theorem c3Exceptional_subset_trAtoms (n : ℕ) (e : ℤ × ℤ) (G v : ℕ) (X : ℝ) :
    c3Exceptional n e G v X ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- The exceptional event does not depend on the entry point. -/
theorem c3Exceptional_indep_entry (n : ℕ) (e e' : ℤ × ℤ) (G v : ℕ) (X : ℝ) :
    c3Exceptional n e G v X = c3Exceptional n e' G v X :=
  rfl

/-- The exceptional event shrinks as the threshold `X` grows. -/
theorem c3Exceptional_anti {n : ℕ} {e : ℤ × ℤ} {G v : ℕ} {X X' : ℝ} (h : X ≤ X') :
    c3Exceptional n e G v X' ⊆ c3Exceptional n e G v X := by
  rintro a ⟨ha, h1 | h2 | h3 | h4⟩
  · exact ⟨ha, Or.inl (h.trans h1)⟩
  · exact ⟨ha, Or.inr (Or.inl (h.trans h2))⟩
  · exact ⟨ha, Or.inr (Or.inr (Or.inl h3))⟩
  · exact ⟨ha, Or.inr (Or.inr (Or.inr h4))⟩

/-- An atom of `𝒜_n` lies outside the exceptional event iff all four conditions fail:
`ℓ - G < X`, `∑_{k ≤ v} l(βᵏ) < X`, `|r - G/4| < G^{3/5}` and `∑_{k ≤ v} j(βᵏ) < G^{3/5}`. -/
theorem notMem_c3Exceptional_iff {n : ℕ} {e : ℤ × ℤ} {G v : ℕ} {X : ℝ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) :
    a ∉ c3Exceptional n e G v X ↔
      (a.1.2 : ℝ) - G < X ∧
        (((a.2.take v).map fun b => bkL (chBlockPoint b)).sum : ℝ) < X ∧
        |(a.1.1 : ℝ) - (G : ℝ) / 4| < (G : ℝ) ^ ((3 : ℝ) / 5) ∧
        (((a.2.take v).map fun b => bkJ (chBlockPoint b)).sum : ℝ) < (G : ℝ) ^ ((3 : ℝ) / 5) := by
  simp only [mem_c3Exceptional, ha, true_and, not_or, not_le]

end CollatzPosDens
