/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.StoppingTrace.TrFirstRaw
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# Raw-three witnesses

For a level `s ∈ ℕ`, the set `𝒜₃(s)` of raw-three witnesses consists of the passage lists
`π ∈ Π_s` such that, writing `M = j(Bp_{|π|}(π))` and `i_s(π)` for the first raw crossing,
the letter at position `i_s(π)` of the raw word `raw_M(π)` is `3`, the crossing happens early,
`i_s(π) ≤ ⌊(5s + 16)/16⌋`, and the overshoot is small, `σ_{i_s(π)}(π) ≤ s + 3`.

For a passage list the final raw partial sum `σ_M(π) = l(Bp_{|π|}(π))` exceeds `s`, so
`i_s(π)` is a genuine crossing: `σ_{i_s(π)}(π) > s`. Hence for `π ∈ 𝒜₃(s)` the overshoot
`σ_{i_s(π)}(π) - s` lies in `{1, 2, 3}`.

## Main definitions

* `CollatzPosDens.trRawThreeWitness s`: the set `𝒜₃(s)`.

## Main results

* `CollatzPosDens.mem_trRawThreeWitness`: the defining characterisation of `π ∈ 𝒜₃(s)`.
* `CollatzPosDens.trRawThreeWitness_subset_trPassage`: `𝒜₃(s) ⊆ Π_s`.
* `CollatzPosDens.trRawThreeWitness_closing_mem`: every closing letter of a raw-three
  witness is `4` or `5`.
* `CollatzPosDens.trRawThreeWitness_getElem_flatMap`: the letter `3` read off the full
  concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`.
* `CollatzPosDens.trRawThreeWitness_lt_trRawSum`: `s < σ_{i_s(π)}(π)` on `𝒜₃(s)`.

## Implementation notes

Lists of blocks are `List (List ℤ × ℤ)`, as in `trPassage`; the restriction of the closing
letters to `{4, 5}` is part of membership in `Π_s`. Positions in a word are indexed from `1`
mathematically and from `0` in Lean, so "the letter at position `i_s(π)`" is the entry of index
`i_s(π) - 1`, read with `List.getElem?` so that the condition also excludes an out-of-range
position. On `Π_s` the lists are nonempty, so `1 ≤ i_s(π) ≤ M` and the position is always in
range (`trRawThreeWitness_getElem_flatMap`). The floor `⌊(5s + 16)/16⌋` of a nonnegative
rational is natural-number division `(5 * s + 16) / 16`.

## References

* [Mazur, *Collatz positive density*], §9.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝒜₃(s)` of raw-three witnesses: passage lists `π ∈ Π_s` whose raw word
`raw_M(π)`, `M = j(Bp_{|π|}(π))`, has the letter `3` at position `i_s(π)`, with
`i_s(π) ≤ ⌊(5s + 16)/16⌋` and `σ_{i_s(π)}(π) ≤ s + 3`. -/
@[collatz_pos_dens "def_tr_raw3_witness"]
def trRawThreeWitness (s : ℕ) : Set (List (List ℤ × ℤ)) :=
  {π | π ∈ trPassage s ∧
    (chRaw (chBlockPath π π.length).1.toNat π)[trFirstRaw s π - 1]? = some 3 ∧
    trFirstRaw s π ≤ (5 * s + 16) / 16 ∧
    trRawSum π (trFirstRaw s π) ≤ s + 3}

variable {s : ℕ} {π : List (List ℤ × ℤ)}

/-- `π ∈ 𝒜₃(s)` iff `π ∈ Π_s`, the letter of `raw_M(π)` at position `i_s(π)` is `3`,
`i_s(π) ≤ ⌊(5s + 16)/16⌋` and `σ_{i_s(π)}(π) ≤ s + 3`. -/
lemma mem_trRawThreeWitness :
    π ∈ trRawThreeWitness s ↔ π ∈ trPassage s ∧
      (chRaw (chBlockPath π π.length).1.toNat π)[trFirstRaw s π - 1]? = some 3 ∧
      trFirstRaw s π ≤ (5 * s + 16) / 16 ∧
      trRawSum π (trFirstRaw s π) ≤ s + 3 :=
  Iff.rfl

/-- Every raw-three witness is a passage list: `𝒜₃(s) ⊆ Π_s`. -/
lemma trRawThreeWitness_subset_trPassage (s : ℕ) : trRawThreeWitness s ⊆ trPassage s :=
  fun _ h ↦ h.1

/-- A raw-three witness `π ∈ 𝒜₃(s)` lies in `Π_s`. -/
lemma trRawThreeWitness_mem_trPassage (h : π ∈ trRawThreeWitness s) : π ∈ trPassage s :=
  h.1

/-- Every block of a raw-three witness has closing letter `4` or `5`. -/
lemma trRawThreeWitness_closing_mem (h : π ∈ trRawThreeWitness s) {b : List ℤ × ℤ}
    (hb : b ∈ π) : b.2 ∈ ({4, 5} : Set ℤ) :=
  trPassage_closing_mem h.1 hb

/-- For `π ∈ 𝒜₃(s)`, the letter of `raw_M(π)` at position `i_s(π)` is `3`. -/
lemma trRawThreeWitness_getElem? (h : π ∈ trRawThreeWitness s) :
    (chRaw (chBlockPath π π.length).1.toNat π)[trFirstRaw s π - 1]? = some 3 :=
  h.2.1

/-- For `π ∈ 𝒜₃(s)`, the first raw crossing is early: `i_s(π) ≤ ⌊(5s + 16)/16⌋`. -/
lemma trRawThreeWitness_trFirstRaw_le (h : π ∈ trRawThreeWitness s) :
    trFirstRaw s π ≤ (5 * s + 16) / 16 :=
  h.2.2.1

/-- For `π ∈ 𝒜₃(s)`, the overshoot is small: `σ_{i_s(π)}(π) ≤ s + 3`. -/
lemma trRawThreeWitness_trRawSum_le (h : π ∈ trRawThreeWitness s) :
    trRawSum π (trFirstRaw s π) ≤ s + 3 :=
  h.2.2.2

/-- For `π ∈ 𝒜₃(s)`, the first raw crossing satisfies `1 ≤ i_s(π)`. -/
lemma trRawThreeWitness_one_le_trFirstRaw (h : π ∈ trRawThreeWitness s) :
    1 ≤ trFirstRaw s π :=
  one_le_trFirstRaw (ne_nil_of_mem_trPassage h.1)

/-- The witness condition read off the full concatenation `z = c¹ (e¹) ⋯ cᵏ (eᵏ)`: the
position `i_s(π)` is in range and `z_{i_s(π)} = 3`. -/
lemma trRawThreeWitness_getElem_flatMap (h : π ∈ trRawThreeWitness s) :
    ∃ hlt : trFirstRaw s π - 1 < (π.flatMap fun b => b.1 ++ [b.2]).length,
      (π.flatMap fun b => b.1 ++ [b.2])[trFirstRaw s π - 1] = 3 := by
  have h3 := trRawThreeWitness_getElem? h
  rw [chRaw_toNat_chBlockPath_fst] at h3
  exact List.getElem?_eq_some_iff.mp h3

/-- On `𝒜₃(s)` the first raw crossing is a genuine crossing: `s < σ_{i_s(π)}(π)`. -/
lemma trRawThreeWitness_lt_trRawSum (h : π ∈ trRawThreeWitness s) :
    (s : ℤ) < trRawSum π (trFirstRaw s π) := by
  have hπ := trRawThreeWitness_mem_trPassage h
  refine lt_trRawSum_trFirstRaw ⟨(chBlockPath π π.length).1.toNat,
    Finset.mem_Icc.mpr
      ⟨one_le_chBlockPath_length_fst_toNat (ne_nil_of_mem_trPassage hπ), le_rfl⟩, ?_⟩
  rw [trRawSum_self]
  exact lt_chBlockPath_snd_of_mem_trPassage hπ

end CollatzPosDens
