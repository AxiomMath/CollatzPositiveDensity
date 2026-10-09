/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Int.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Fresh atoms

For `n ≥ 1`, the set of *fresh atoms* is `𝒜_n = (ℕ × ℤ) × 𝔅^{⌊n/2⌋}`. An atom is written
`a = ((r, ℓ), β)`: the pair `(r, ℓ) ∈ ℕ × ℤ` is a displacement, and `β` is a list of `⌊n/2⌋`
blocks of the alphabet `𝔅 = ℤ^{<ω} × {4, 5}`.

## Main definitions

* `CollatzPosDens.trAtoms`: the set `𝒜_n` of fresh atoms.

## Main results

* `CollatzPosDens.mem_trAtoms`: the defining characterisation of `((r, ℓ), β) ∈ 𝒜_n`.

## Implementation notes

A block of `𝔅` is a pair `b : List ℤ × ℤ` and a word of `𝔅^k` is a list `β : List (List ℤ × ℤ)` of
length `k`; the restriction of the blocks to `𝔅 = ℤ^{<ω} × {4, 5}` is the explicit condition that
every closing letter lies in `{4, 5}`. Accordingly `𝒜_n` is the subset of
`(ℕ × ℤ) × List (List ℤ × ℤ)` cut out by `β.length = n / 2` (natural division is `⌊n/2⌋`) and this
closing-letter condition, so that an atom is still pattern-matched as `((r, ℓ), β)` and sums over
`𝒜_n` are sums over the subtype. The definition makes sense for every `n : ℕ`, which generalizes
the source's `n ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝒜_n = (ℕ × ℤ) × 𝔅^{⌊n/2⌋}` of fresh atoms `a = ((r, ℓ), β)`: `β` is a list of
`⌊n/2⌋` blocks, each with closing letter in `{4, 5}`. -/
@[collatz_pos_dens "def_tr_atoms"]
def trAtoms (n : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a.2.length = n / 2 ∧ ∀ b ∈ a.2, b.2 ∈ ({4, 5} : Set ℤ)}

variable {n : ℕ}

/-- The defining characterisation of `a ∈ 𝒜_n`. -/
lemma mem_trAtoms {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ trAtoms n ↔ a.2.length = n / 2 ∧ ∀ b ∈ a.2, b.2 ∈ ({4, 5} : Set ℤ) :=
  Iff.rfl

/-- The characterisation of membership in `𝒜_n` for an atom written `((r, ℓ), β)`. -/
@[simp]
lemma mk_mem_trAtoms {r : ℕ} {ℓ : ℤ} {β : List (List ℤ × ℤ)} :
    ((r, ℓ), β) ∈ trAtoms n ↔ β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ) :=
  Iff.rfl

/-- The block list of a fresh atom has length `⌊n/2⌋`. -/
lemma trAtoms_length {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) :
    a.2.length = n / 2 :=
  ha.1

/-- Every block of a fresh atom has closing letter `4` or `5`. -/
lemma trAtoms_closing_mem {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n)
    {b : List ℤ × ℤ} (hb : b ∈ a.2) : b.2 ∈ ({4, 5} : Set ℤ) :=
  ha.2 b hb

/-- The displacement `(r, ℓ)` of a fresh atom is unconstrained: `𝒜_n` is the product of
`ℕ × ℤ` with the set of words of `𝔅^{⌊n/2⌋}`. -/
lemma trAtoms_eq_prod :
    trAtoms n = Set.univ ×ˢ {β | β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)} := by
  ext ⟨⟨r, ℓ⟩, β⟩
  simp [mem_trAtoms]

/-- The fresh atoms `𝒜_n` split as `(ℕ × ℤ) × 𝔅^{⌊n/2⌋}`. -/
def trAtomsEquiv (n : ℕ) :
    trAtoms n ≃ (ℕ × ℤ) × {β : List (List ℤ × ℤ) //
      β.length = n / 2 ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}} where
  toFun a := (a.1.1, ⟨a.1.2, a.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end CollatzPosDens
