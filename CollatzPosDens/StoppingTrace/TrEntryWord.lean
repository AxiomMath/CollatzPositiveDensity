/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Entry lists

For a black point `v`, the set `𝓔(v)` of *entry lists* consists of the live lists of blocks
`u ∈ 𝔅^q` with `q ≥ 1` whose path `(x_t(v, u))_t` is, at time `q`, black and strictly above the
column top of `v`, i.e. `l(x_q(v, u)) > l_*(v)`, and has this property at no earlier time
`1 ≤ t < q`. Thus `q` is the first positive time at which the path of `u` re-enters the black
set above the column of black points starting at `v`, and it is the last time at which the path
moves. In particular the empty list is never an entry list, and no entry list is a proper prefix
of another.

## Main definitions

* `CollatzPosDens.trEntryWords`: the set `𝓔(v)` of entry lists.

## Main results

* `CollatzPosDens.mem_trEntryWords`: the defining characterisation of `u ∈ 𝓔(v)`.
* `CollatzPosDens.nil_notMem_trEntryWords`: the empty list is not an entry list.
* `CollatzPosDens.isPrefixFree_trEntryWords`: `𝓔(v)` is prefix-free.

## Implementation notes

As in `trPath` and `TrLive`, a list `u ∈ 𝔅^q` is a `u : List (List ℤ × ℤ)` with
`q = u.length`, and the restriction of the blocks to `𝔅 = ℤ^{<ω} × {4, 5}` is the explicit
condition that every closing letter lies in `{4, 5}`. Blackness is `BkBlack n ξ ε` and the column
top is `bkColTop n ξ ε`; the source works with the colour scale `ε = ε_*`
(`CollatzPosDens.epsStar`), and the definition is stated for an arbitrary `ε : ℝ`, to be used
at `ε = (ε_* : ℝ)`. The base point `v` ranges over all of `ℤ × ℤ`, not only black points; on
black points this is the source's set. Both are generalizations.

## References

* [Mazur, *Collatz positive density*, §9.2]
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝓔(v)` of entry lists: live lists `u ∈ 𝔅^q`, `q ≥ 1`, such that `x_q(v, u)` is black
with `l(x_q(v, u)) > l_*(v)`, and for no `1 ≤ t < q` is `x_t(v, u)` black with
`l(x_t(v, u)) > l_*(v)`. -/
@[collatz_pos_dens "def_tr_entry_word"]
def trEntryWords (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) : Set (List (List ℤ × ℤ)) :=
  {u | (∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive u ∧ 1 ≤ u.length ∧
    (BkBlack n ξ ε (trPath v u u.length) ∧ bkColTop n ξ ε v < bkL (trPath v u u.length)) ∧
    ∀ t, 1 ≤ t → t < u.length →
      ¬(BkBlack n ξ ε (trPath v u t) ∧ bkColTop n ξ ε v < bkL (trPath v u t))}

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {v : ℤ × ℤ} {u : List (List ℤ × ℤ)}

/-- The defining characterisation of `u ∈ 𝓔(v)`. -/
lemma mem_trEntryWords :
    u ∈ trEntryWords n ξ ε v ↔
      (∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive u ∧ 1 ≤ u.length ∧
        (BkBlack n ξ ε (trPath v u u.length) ∧ bkColTop n ξ ε v < bkL (trPath v u u.length)) ∧
        ∀ t, 1 ≤ t → t < u.length →
          ¬(BkBlack n ξ ε (trPath v u t) ∧ bkColTop n ξ ε v < bkL (trPath v u t)) :=
  Iff.rfl

/-- Every block of an entry list has closing letter `4` or `5`. -/
lemma trEntryWords_closing_mem (hu : u ∈ trEntryWords n ξ ε v) {b : List ℤ × ℤ}
    (hb : b ∈ u) : b.2 ∈ ({4, 5} : Set ℤ) :=
  hu.1 b hb

/-- An entry list is live. -/
lemma trEntryWords_trLive (hu : u ∈ trEntryWords n ξ ε v) : TrLive u :=
  hu.2.1

/-- An entry list is nonempty. -/
lemma trEntryWords_length_pos (hu : u ∈ trEntryWords n ξ ε v) : 0 < u.length :=
  hu.2.2.1

/-- The empty list is not an entry list. -/
@[simp]
lemma nil_notMem_trEntryWords : [] ∉ trEntryWords n ξ ε v := fun h ↦
  (trEntryWords_length_pos h).ne' rfl

/-- The path of an entry list `u ∈ 𝔅^q` is black at time `q`. -/
lemma trEntryWords_bkBlack (hu : u ∈ trEntryWords n ξ ε v) :
    BkBlack n ξ ε (trPath v u u.length) :=
  hu.2.2.2.1.1

/-- The path of an entry list `u ∈ 𝔅^q` lies above the column top of `v` at time `q`. -/
lemma trEntryWords_bkColTop_lt (hu : u ∈ trEntryWords n ξ ε v) :
    bkColTop n ξ ε v < bkL (trPath v u u.length) :=
  hu.2.2.2.1.2

/-- At no time `1 ≤ t < q` is the path of an entry list `u ∈ 𝔅^q` black and above the column
top of `v`. -/
lemma trEntryWords_not_hit (hu : u ∈ trEntryWords n ξ ε v) {t : ℕ} (ht₁ : 1 ≤ t)
    (ht : t < u.length) :
    ¬(BkBlack n ξ ε (trPath v u t) ∧ bkColTop n ξ ε v < bkL (trPath v u t)) :=
  hu.2.2.2.2 t ht₁ ht

/-- From its length on, the path of an entry list is black and above the column top of `v`. -/
lemma trEntryWords_hit_of_length_le (hu : u ∈ trEntryWords n ξ ε v) {t : ℕ}
    (ht : u.length ≤ t) :
    BkBlack n ξ ε (trPath v u t) ∧ bkColTop n ξ ε v < bkL (trPath v u t) :=
  trPath_of_length_le v u ht ▸ hu.2.2.2.1

/-- The set of entry lists is prefix-free: an entry list that is a prefix of another entry list
is equal to it. -/
lemma isPrefixFree_trEntryWords : InformationTheory.IsPrefixFree (trEntryWords n ξ ε v) := by
  intro u hu u' hu' h
  obtain ⟨γ, rfl⟩ := h
  rcases eq_or_ne γ [] with rfl | hγ
  · simp
  · have hlt : u.length < (u ++ γ).length := by
      simp [List.length_pos_iff.mpr hγ]
    exact (trEntryWords_not_hit hu' (trEntryWords_length_pos hu) hlt
      (trPath_append_of_le v u γ le_rfl ▸ hu.2.2.2.1)).elim

end CollatzPosDens
