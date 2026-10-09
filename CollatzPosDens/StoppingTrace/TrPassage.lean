/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrLive

/-!
# Passage lists

For `s ∈ ℕ`, the set `Π_s` of *passage lists* consists of the live lists of blocks
`π = (π¹, …, πᵏ) ∈ 𝔅ᵏ`, where `𝔅 = ℤ^{<ω} × {4, 5}`, with `k ≥ 1` whose block path
`Bp_0(π), Bp_1(π), …, Bp_k(π)` stays at level at most `s` before its last step and is strictly
above level `s` at the end: `l(Bp_i(π)) ≤ s` for every `0 ≤ i < k` and `l(Bp_k(π)) > s`. Here
`l(j, l) = l` is the second coordinate of a lattice point. The passage lists record the first
passage of the block path above level `s`; in particular no proper nonempty prefix of a passage
list is again a passage list.

## Main definitions

* `CollatzPosDens.trPassage`: the set `Π_s` of passage lists.

## Main results

* `CollatzPosDens.mem_trPassage`: the defining characterisation of `π ∈ Π_s`.
* `CollatzPosDens.trPassage_closing_mem`: every closing letter of a passage list is `4` or `5`.
* `CollatzPosDens.trPassage_nil_notMem`: the empty list is not a passage list.
* `CollatzPosDens.trPassage_eq_of_prefix`: `Π_s` is prefix-free.

## Implementation notes

A list in `𝔅ᵏ` is modelled as `π : List (List ℤ × ℤ)` with `k = π.length`, as in
`chBlockPath` and `TrLive`; the condition `k ≥ 1` is `π ≠ []`. The level `l(Bp_i(π))` is the
second coordinate `(chBlockPath π i).2 : ℤ`, compared with the cast of `s`. As in
`trFirstStopSet`, the restriction of the blocks to `𝔅 = ℤ^{<ω} × {4, 5}` is the explicit
condition that every closing letter lies in `{4, 5}`; liveness alone does not force it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `Π_s` of passage lists: live lists `π ∈ 𝔅ᵏ` (every closing letter in `{4, 5}`)
with `k ≥ 1` such that `l(Bp_i(π)) ≤ s` for every `0 ≤ i < k` and `l(Bp_k(π)) > s`. -/
@[collatz_pos_dens "def_tr_passage"]
def trPassage (s : ℕ) : Set (List (List ℤ × ℤ)) :=
  {π | (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive π ∧ π ≠ [] ∧
    (∀ i < π.length, (chBlockPath π i).2 ≤ s) ∧ (s : ℤ) < (chBlockPath π π.length).2}

/-- The defining characterisation of `π ∈ Π_s`. -/
lemma mem_trPassage {s : ℕ} {π : List (List ℤ × ℤ)} :
    π ∈ trPassage s ↔ (∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ TrLive π ∧ π ≠ [] ∧
      (∀ i < π.length, (chBlockPath π i).2 ≤ s) ∧ (s : ℤ) < (chBlockPath π π.length).2 :=
  Iff.rfl

/-- Every block of a passage list has closing letter `4` or `5`. -/
lemma trPassage_closing_mem {s : ℕ} {π : List (List ℤ × ℤ)} (h : π ∈ trPassage s)
    {b : List ℤ × ℤ} (hb : b ∈ π) : b.2 ∈ ({4, 5} : Set ℤ) :=
  h.1 b hb

/-- A passage list is live. -/
lemma trLive_of_mem_trPassage {s : ℕ} {π : List (List ℤ × ℤ)} (h : π ∈ trPassage s) :
    TrLive π :=
  h.2.1

/-- A passage list is nonempty. -/
lemma ne_nil_of_mem_trPassage {s : ℕ} {π : List (List ℤ × ℤ)} (h : π ∈ trPassage s) :
    π ≠ [] :=
  h.2.2.1

/-- A passage list has positive length. -/
lemma length_pos_of_mem_trPassage {s : ℕ} {π : List (List ℤ × ℤ)} (h : π ∈ trPassage s) :
    0 < π.length :=
  List.length_pos_iff.mpr h.2.2.1

/-- For `π ∈ Π_s`, the block path satisfies `l(Bp_i(π)) ≤ s` for every `i < k`. -/
lemma chBlockPath_snd_le_of_mem_trPassage {s : ℕ} {π : List (List ℤ × ℤ)}
    (h : π ∈ trPassage s) {i : ℕ} (hi : i < π.length) : (chBlockPath π i).2 ≤ s :=
  h.2.2.2.1 i hi

/-- For `π ∈ Π_s` of length `k`, the block path satisfies `l(Bp_k(π)) > s`. -/
lemma lt_chBlockPath_snd_of_mem_trPassage {s : ℕ} {π : List (List ℤ × ℤ)}
    (h : π ∈ trPassage s) :
    (s : ℤ) < (chBlockPath π π.length).2 :=
  h.2.2.2.2

/-- The empty list is not a passage list. -/
@[simp]
lemma trPassage_nil_notMem (s : ℕ) : [] ∉ trPassage s :=
  fun h ↦ h.2.2.1 rfl

/-- `Π_s` is prefix-free: if `π` and `π ++ γ` are both passage lists then `γ = []`. -/
lemma trPassage_eq_of_prefix {s : ℕ} {π γ : List (List ℤ × ℤ)} (hπ : π ∈ trPassage s)
    (hπγ : π ++ γ ∈ trPassage s) : γ = [] := by
  by_contra hγ
  have hlt : π.length < (π ++ γ).length := by
    simp [List.length_pos_iff.mpr hγ]
  have h1 := chBlockPath_snd_le_of_mem_trPassage hπγ hlt
  rw [chBlockPath_append_of_le _ _ le_rfl] at h1
  exact absurd (lt_chBlockPath_snd_of_mem_trPassage hπ) (not_lt.mpr h1)

end CollatzPosDens
