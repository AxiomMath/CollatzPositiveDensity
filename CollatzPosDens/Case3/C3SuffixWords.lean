/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldWords

/-!
# Suffix words of a crossing letter

For an integer `c`, the set `𝒮_c` of suffix words of the crossing letter `c` is `{()}`, the set
containing only the empty word, when `c ∈ {4, 5}`, and otherwise the union
`⋃_{(j, l) ∈ 𝒫} 𝒞_{j,l}`, over `𝒫 = ℤ_{≥1} × ℤ`, of the hold words `CollatzPosDens.holdWords j l`.
When `c ∉ {4, 5}`, a suffix word is thus a nonempty word of letters at least `2` whose last letter,
and no other, lies in `{4, 5}`.

## Main definitions

* `CollatzPosDens.c3SuffixWords c`: the set `𝒮_c` of finite words of integers.

## Main results

* `CollatzPosDens.c3SuffixWords_of_mem`: `𝒮_c = {()}` when `c ∈ {4, 5}`.
* `CollatzPosDens.c3SuffixWords_of_notMem`: `𝒮_c = ⋃_{(j, l) ∈ 𝒫} 𝒞_{j,l}` when `c ∉ {4, 5}`.
* `CollatzPosDens.mem_c3SuffixWords_of_notMem`: for `c ∉ {4, 5}`, a word `u` lies in `𝒮_c` iff
  it is nonempty and, read as a function of its positions, is a hold word of length `|u|`.
* `CollatzPosDens.two_le_of_mem_c3SuffixWords`: every letter of a word of `𝒮_c` is at least `2`.

## Implementation notes

A finite word of integers is a `List ℤ`, the type of the raw words `CollatzPosDens.chRaw` that
the suffix words are concatenated with; a hold word `w : Fin j → ℤ` enters `𝒮_c` as the list
`List.ofFn w`. The index set `𝒫 = ℤ_{≥1} × ℤ` of the union is parametrized by the pairs
`(j, l) ∈ ℕ × ℤ` with `1 ≤ j`, since `holdWords` takes its length as a natural number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The suffix words `𝒮_c` of a crossing letter `c`: `{()}` if `c ∈ {4, 5}`, and otherwise the
union of the hold words `𝒞_{j,l}` over `(j, l) ∈ 𝒫`, i.e. over `j ≥ 1` and `l ∈ ℤ`. -/
@[collatz_pos_dens "def_c3_suffix_words"]
def c3SuffixWords (c : ℤ) : Set (List ℤ) :=
  if c = 4 ∨ c = 5 then {[]} else ⋃ j : ℕ, ⋃ (_ : 1 ≤ j), ⋃ l : ℤ, List.ofFn '' holdWords j l

/-- For `c ∈ {4, 5}`, `𝒮_c` consists of the empty word alone. -/
theorem c3SuffixWords_of_mem {c : ℤ} (hc : c ∈ ({4, 5} : Set ℤ)) : c3SuffixWords c = {[]} :=
  ite_eq_left_iff.2 fun h => (h hc).elim

/-- For `c ∉ {4, 5}`, `𝒮_c` is the union of the hold words `𝒞_{j,l}` over `j ≥ 1`, `l ∈ ℤ`. -/
theorem c3SuffixWords_of_notMem {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ)) :
    c3SuffixWords c = ⋃ j : ℕ, ⋃ (_ : 1 ≤ j), ⋃ l : ℤ, List.ofFn '' holdWords j l :=
  ite_eq_right_iff.2 fun h => (hc h).elim

/-- For `c ∈ {4, 5}`, a word lies in `𝒮_c` iff it is empty. -/
theorem mem_c3SuffixWords_of_mem {c : ℤ} (hc : c ∈ ({4, 5} : Set ℤ)) {u : List ℤ} :
    u ∈ c3SuffixWords c ↔ u = [] := by
  rw [c3SuffixWords_of_mem hc, Set.mem_singleton_iff]

/-- For `c ∉ {4, 5}`, a word `u` lies in `𝒮_c` iff it is nonempty and its letters, indexed by
its positions, form a hold word `u.get ∈ 𝒞_{|u|,l}` for some `l`. -/
theorem mem_c3SuffixWords_of_notMem {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ)) {u : List ℤ} :
    u ∈ c3SuffixWords c ↔ 1 ≤ u.length ∧ ∃ l, u.get ∈ holdWords u.length l := by
  rw [c3SuffixWords_of_notMem hc]
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨j, hj, l, w, hw, rfl⟩
    refine ⟨by simpa using hj, l, ?_⟩
    have key : ∀ {k : ℕ} (h : k = j) (v : Fin k → ℤ), (∀ i, v i = w (Fin.cast h i)) →
        v ∈ holdWords k l := by
      rintro k rfl v hv
      obtain rfl : v = w := funext hv
      exact hw
    exact key List.length_ofFn _ fun i => List.get_ofFn w i
  · rintro ⟨hj, l, hu⟩
    exact ⟨u.length, hj, l, u.get, hu, List.ofFn_get u⟩

/-- Every letter of a suffix word is at least `2`. -/
theorem two_le_of_mem_c3SuffixWords {c : ℤ} {u : List ℤ} (hu : u ∈ c3SuffixWords c) :
    ∀ x ∈ u, 2 ≤ x := by
  by_cases hc : c ∈ ({4, 5} : Set ℤ)
  · rw [mem_c3SuffixWords_of_mem hc] at hu
    simp [hu]
  · obtain ⟨-, l, hl⟩ := (mem_c3SuffixWords_of_notMem hc).1 hu
    intro x hx
    obtain ⟨i, rfl⟩ := List.get_of_mem hx
    exact holdWords_two_le hl i

end CollatzPosDens
