/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.Transfer.EpsStar

/-!
# Policies valid at a black point

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`. For a black point `v` and a set
`W ⊆ ℕ × ℕ × ℕ` of triples `(r, h, c)`, the set `W` is *valid at `v`* if for every
`(r, h, c) ∈ W` with `c ∈ {4, 5}` the point `y = v + (r + 1, h + c)` is not black or satisfies
`l(y) ≤ l_*(v)`, where `l_*(v)` is the top of the black column run above `v`
(`CollatzPosDens.bkColTop`).

## Main definitions

* `CollatzPosDens.TrTreeValid n ξ ε v W`: the set `W` is valid at `v`.

## Main results

* `CollatzPosDens.trTreeValid_iff`: the defining characterization.
* `CollatzPosDens.TrTreeValid.not_bkBlack_or_le`: the condition at a member of `W`.
* `CollatzPosDens.TrTreeValid.mono`: validity passes to subsets.
* `CollatzPosDens.trTreeValid_empty`, `CollatzPosDens.trTreeValid_union`: the empty set is
  valid, and a union of two valid sets is valid.
* `CollatzPosDens.trTreeValid_of_forall`: a set none of whose members has `c ∈ {4, 5}` is
  valid.
* `CollatzPosDens.trTreeValid_of_add_le`: a set whose members with `c ∈ {4, 5}` all satisfy
  `l(v) + h + c ≤ l_*(v)` is valid.

## Implementation notes

Validity is defined at every `v : ℤ × ℤ`, not only at black points; blackness of `v` is a
hypothesis of the results that need it. The definition is stated for an arbitrary colour scale
`ε : ℝ` and is used at `ε = (ε_* : ℝ)` (`CollatzPosDens.epsStar`). The displacement
`(r + 1, h + c)` is the natural-number vector cast to `ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- A set `W ⊆ ℕ × ℕ × ℕ` is *valid at `v`* if for every `(r, h, c) ∈ W` with `c ∈ {4, 5}` the
point `y = v + (r + 1, h + c)` is not black or satisfies `l(y) ≤ l_*(v)`. -/
@[collatz_pos_dens "def_tr_tree_valid"]
def TrTreeValid (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) (W : Set (ℕ × ℕ × ℕ)) :
    Prop :=
  ∀ r h c : ℕ, (r, h, c) ∈ W → (c = 4 ∨ c = 5) →
    ¬BkBlack n ξ ε (v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ))) ∨
      bkL (v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ))) ≤ bkColTop n ξ ε v

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {v : ℤ × ℤ} {W W' : Set (ℕ × ℕ × ℕ)}

/-- Unfolding lemma for `TrTreeValid`. -/
theorem trTreeValid_iff :
    TrTreeValid n ξ ε v W ↔ ∀ r h c : ℕ, (r, h, c) ∈ W → (c = 4 ∨ c = 5) →
      ¬BkBlack n ξ ε (v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ))) ∨
        bkL (v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ))) ≤ bkColTop n ξ ε v :=
  Iff.rfl

/-- The `l`-coordinate of `v + (r + 1, h + c)` is `l(v) + h + c`. -/
@[simp]
theorem bkL_add_natCast_pair (v : ℤ × ℤ) (a b : ℕ) :
    bkL (v + ((a : ℤ), (b : ℤ))) = bkL v + b :=
  rfl

/-- At a member `(r, h, c) ∈ W` with `c ∈ {4, 5}` of a valid set, the point
`y = v + (r + 1, h + c)` is not black or satisfies `l(y) ≤ l_*(v)`. -/
theorem TrTreeValid.not_bkBlack_or_le (hW : TrTreeValid n ξ ε v W) {r h c : ℕ}
    (hm : (r, h, c) ∈ W) (hc : c = 4 ∨ c = 5) :
    ¬BkBlack n ξ ε (v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ))) ∨
      bkL v + (h + c : ℕ) ≤ bkColTop n ξ ε v :=
  hW r h c hm hc

/-- If `W` is valid at `v` and `(r, h, c) ∈ W` with `c ∈ {4, 5}` and `y = v + (r + 1, h + c)`
black, then `l(v) + h + c ≤ l_*(v)`. -/
theorem TrTreeValid.le_bkColTop (hW : TrTreeValid n ξ ε v W) {r h c : ℕ}
    (hm : (r, h, c) ∈ W) (hc : c = 4 ∨ c = 5)
    (hy : BkBlack n ξ ε (v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ)))) :
    bkL v + (h + c : ℕ) ≤ bkColTop n ξ ε v :=
  (hW.not_bkBlack_or_le hm hc).resolve_left (not_not.2 hy)

/-- Validity passes to subsets. -/
theorem TrTreeValid.mono (hW : TrTreeValid n ξ ε v W) (h : W' ⊆ W) :
    TrTreeValid n ξ ε v W' :=
  fun r h' c hm hc => hW r h' c (h hm) hc

/-- The empty set is valid at every point. -/
@[simp]
theorem trTreeValid_empty : TrTreeValid n ξ ε v ∅ :=
  fun _ _ _ hm _ => hm.elim

/-- A union of two sets is valid iff both are. -/
@[simp]
theorem trTreeValid_union :
    TrTreeValid n ξ ε v (W ∪ W') ↔ TrTreeValid n ξ ε v W ∧ TrTreeValid n ξ ε v W' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun h r h' c hm hc => hm.elim (h.1 r h' c · hc) (h.2 r h' c · hc)⟩

/-- A set none of whose members has `c ∈ {4, 5}` is valid at every point. -/
theorem trTreeValid_of_forall (h : ∀ r h c : ℕ, (r, h, c) ∈ W → c ≠ 4 ∧ c ≠ 5) :
    TrTreeValid n ξ ε v W := fun r h' c hm hc => by
  have := h r h' c hm
  omega

/-- A set whose members `(r, h, c)` with `c ∈ {4, 5}` all satisfy `l(v) + h + c ≤ l_*(v)` is
valid at `v`. -/
theorem trTreeValid_of_add_le
    (h : ∀ r h c : ℕ, (r, h, c) ∈ W → (c = 4 ∨ c = 5) → bkL v + (h + c : ℕ) ≤ bkColTop n ξ ε v) :
    TrTreeValid n ξ ε v W :=
  fun r h' c hm hc => Or.inr (h r h' c hm hc)

end CollatzPosDens
