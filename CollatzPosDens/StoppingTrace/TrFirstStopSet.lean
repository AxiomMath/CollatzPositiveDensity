/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# First-stop lists

For a base point `o ∈ 𝒫`, the set `𝒰(o)` of *first-stop lists* consists of the live lists of
blocks `u ∈ 𝔅^q`, `q ∈ ℕ`, whose path `(x_t(o, u))_t` is black at time `q` and at no earlier
time `0 ≤ t < q`. Thus `q` is the first time at which the path of `u` meets the black set, and
it is the last time at which the path moves. In particular, if `o` itself is black then the
empty list is the only first-stop list, and no first-stop list is a proper prefix of another.

## Main definitions

* `CollatzPosDens.trFirstStopSet`: the set `𝒰(o)` of first-stop lists.

## Main results

* `CollatzPosDens.mem_trFirstStopSet`: the defining characterisation of `u ∈ 𝒰(o)`.
* `CollatzPosDens.nil_mem_trFirstStopSet_iff`: `[] ∈ 𝒰(o)` iff `o` is black.
* `CollatzPosDens.trFirstStopSet_eq_singleton_nil_of_bkBlack`: if `o` is black then `𝒰(o) = {[]}`.
* `CollatzPosDens.isPrefixFree_trFirstStopSet`: `𝒰(o)` is prefix-free.

## Implementation notes

As in `trPath` and `TrLive`, a list `u ∈ 𝔅^q` is a `u : List (List ℤ × ℤ)` with
`q = u.length`, and the restriction of the blocks to `𝔅 = ℤ^{<ω} × {4, 5}` is the explicit
condition that every closing letter lies in `{4, 5}` (liveness alone does not force it).
Blackness is `BkBlack n ξ ε`. The definition is stated for an arbitrary colour scale `ε : ℝ`,
the case of interest being `ε = ε_*` (`CollatzPosDens.epsStar`), and for an arbitrary base point
`o ∈ ℤ × ℤ`, the case of interest being `o ∈ 𝒫`.

## References

* [Mazur, *Collatz positive density*], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝒰(o)` of first-stop lists: live lists `u ∈ 𝔅^q`, `q ∈ ℕ`, such that `x_q(o, u)` is
black and `x_t(o, u)` is not black for every `0 ≤ t < q`. -/
@[collatz_pos_dens "def_tr_first_stop_set"]
def trFirstStopSet (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (o : ℤ × ℤ) :
    Set (List (List ℤ × ℤ)) :=
  {u | (∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive u ∧ BkBlack n ξ ε (trPath o u u.length) ∧
    ∀ t < u.length, ¬BkBlack n ξ ε (trPath o u t)}

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {o : ℤ × ℤ} {u : List (List ℤ × ℤ)}

/-- The defining characterisation of `u ∈ 𝒰(o)`. -/
lemma mem_trFirstStopSet :
    u ∈ trFirstStopSet n ξ ε o ↔
      (∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive u ∧ BkBlack n ξ ε (trPath o u u.length) ∧
        ∀ t < u.length, ¬BkBlack n ξ ε (trPath o u t) :=
  Iff.rfl

/-- Every block of a first-stop list has closing letter `4` or `5`. -/
lemma trFirstStopSet_closing_mem (hu : u ∈ trFirstStopSet n ξ ε o) {b : List ℤ × ℤ}
    (hb : b ∈ u) : b.2 ∈ ({4, 5} : Set ℤ) :=
  hu.1 b hb

/-- A first-stop list is live. -/
lemma trFirstStopSet_trLive (hu : u ∈ trFirstStopSet n ξ ε o) : TrLive u :=
  hu.2.1

/-- The path of a first-stop list `u ∈ 𝔅^q` is black at time `q`. -/
lemma trFirstStopSet_bkBlack (hu : u ∈ trFirstStopSet n ξ ε o) :
    BkBlack n ξ ε (trPath o u u.length) :=
  hu.2.2.1

/-- The path of a first-stop list `u ∈ 𝔅^q` is not black at any time `t < q`. -/
lemma trFirstStopSet_not_bkBlack (hu : u ∈ trFirstStopSet n ξ ε o) {t : ℕ}
    (ht : t < u.length) : ¬BkBlack n ξ ε (trPath o u t) :=
  hu.2.2.2 t ht

/-- The path of a first-stop list is black from its length on. -/
lemma trFirstStopSet_bkBlack_of_length_le (hu : u ∈ trFirstStopSet n ξ ε o) {t : ℕ}
    (ht : u.length ≤ t) : BkBlack n ξ ε (trPath o u t) := by
  rw [trPath_of_length_le o u ht]
  exact trFirstStopSet_bkBlack hu

/-- The empty list is a first-stop list iff the base point is black. -/
@[simp]
lemma nil_mem_trFirstStopSet_iff : [] ∈ trFirstStopSet n ξ ε o ↔ BkBlack n ξ ε o := by
  simp [mem_trFirstStopSet]

/-- A nonempty first-stop list starts from a base point that is not black. -/
lemma trFirstStopSet_not_bkBlack_of_ne_nil (hu : u ∈ trFirstStopSet n ξ ε o) (hne : u ≠ []) :
    ¬BkBlack n ξ ε o := by
  simpa only [trPath_zero] using trFirstStopSet_not_bkBlack hu (List.length_pos_iff.mpr hne)

/-- If the base point is black, the empty list is the only first-stop list. -/
lemma trFirstStopSet_eq_singleton_nil_of_bkBlack (ho : BkBlack n ξ ε o) :
    trFirstStopSet n ξ ε o = {[]} := by
  ext u
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hu ↦ by_contra fun hne ↦ trFirstStopSet_not_bkBlack_of_ne_nil hu hne ho,
    fun h ↦ h ▸ nil_mem_trFirstStopSet_iff.mpr ho⟩

/-- The set of first-stop lists is prefix-free: a first-stop list that is a prefix of another
first-stop list is equal to it. -/
lemma isPrefixFree_trFirstStopSet : InformationTheory.IsPrefixFree (trFirstStopSet n ξ ε o) := by
  intro u hu u' hu' h
  obtain ⟨γ, rfl⟩ := h
  rcases eq_or_ne γ [] with rfl | hγ
  · simp
  · refine absurd ?_ (trFirstStopSet_not_bkBlack hu' (t := u.length)
      (by simp [List.length_pos_iff.mpr hγ]))
    rw [trPath_append_of_le o u γ le_rfl]
    exact trFirstStopSet_bkBlack hu

end CollatzPosDens
