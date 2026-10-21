/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# First raw crossing events

For a level `s ∈ ℕ` and integers `c, o, r` (of interest when `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1`),
the set `𝒳_{c,o,r}(s)` consists of the passage lists `π ∈ Π_s` such that, writing
`M = j(Bp_{|π|}(π))`, we have `r ≤ M`, the `r`-th letter of the raw word `raw_M(π)` is `c`, and
the raw partial sum satisfies `σ_r(π) = s + o`.

When `1 ≤ o ≤ c` and `c` is the `r`-th letter, `σ_{r-1}(π) = s + o - c ≤ s < σ_r(π)`, so `r` is
the first raw crossing of level `s`, the letter crossing it is `c`, and the overshoot is `o`.

## Main definitions

* `CollatzPosDens.trRawThreeWitness s c o r`: the set `𝒳_{c,o,r}(s)`.

## Main results

* `CollatzPosDens.mem_trRawThreeWitness`: the defining characterisation of `π ∈ 𝒳_{c,o,r}(s)`.
* `CollatzPosDens.trRawThreeWitness_subset_trPassage`: `𝒳_{c,o,r}(s) ⊆ Π_s`.
* `CollatzPosDens.trRawThreeWitness_getElem_flatMap`: the letter `c` read off the full
  concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`.
* `CollatzPosDens.trRawThreeWitness_lt_trRawSum`: `s < σ_r(π)` when `0 < o`.

## Implementation notes

Lists of blocks are `List (List ℤ × ℤ)`; the restriction of the closing letters to `{4, 5}` is
part of membership in `Π_s`. The letter `c` and the overshoot `o` are integers and the position
`r` is a natural number; the side conditions `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1` are not needed to
state the definition and are left to the results that use them. Letters are counted from `1`,
while Lean's lists are indexed from `0`, so "the `r`-th letter" is the entry of index `r - 1`,
read with `List.getElem?`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝒳_{c,o,r}(s)` of first raw crossing events: passage lists `π ∈ Π_s` such that,
with `M = j(Bp_{|π|}(π))`, `r ≤ M`, the `r`-th letter of `raw_M(π)` is `c`, and
`σ_r(π) = s + o`. -/
@[collatz_pos_dens "def_tr_raw3_witness"]
def trRawThreeWitness (s : ℕ) (c o : ℤ) (r : ℕ) : Set (List (List ℤ × ℤ)) :=
  {π | π ∈ trPassage s ∧ r ≤ (chBlockPath π π.length).1.toNat ∧
    (chRaw (chBlockPath π π.length).1.toNat π)[r - 1]? = some c ∧
    trRawSum π r = s + o}

variable {s : ℕ} {c o : ℤ} {r : ℕ} {π : List (List ℤ × ℤ)}

/-- `π ∈ 𝒳_{c,o,r}(s)` iff `π ∈ Π_s`, `r ≤ M`, the `r`-th letter of `raw_M(π)` is `c` and
`σ_r(π) = s + o`, where `M = j(Bp_{|π|}(π))`. -/
lemma mem_trRawThreeWitness :
    π ∈ trRawThreeWitness s c o r ↔ π ∈ trPassage s ∧ r ≤ (chBlockPath π π.length).1.toNat ∧
      (chRaw (chBlockPath π π.length).1.toNat π)[r - 1]? = some c ∧
      trRawSum π r = s + o :=
  Iff.rfl

/-- Every first raw crossing event is a passage list: `𝒳_{c,o,r}(s) ⊆ Π_s`. -/
lemma trRawThreeWitness_subset_trPassage (s : ℕ) (c o : ℤ) (r : ℕ) :
    trRawThreeWitness s c o r ⊆ trPassage s :=
  fun _ h ↦ h.1

/-- A list `π ∈ 𝒳_{c,o,r}(s)` lies in `Π_s`. -/
lemma trRawThreeWitness_mem_trPassage (h : π ∈ trRawThreeWitness s c o r) : π ∈ trPassage s :=
  h.1

/-- Every block of a list in `𝒳_{c,o,r}(s)` has closing letter `4` or `5`. -/
lemma trRawThreeWitness_closing_mem (h : π ∈ trRawThreeWitness s c o r) {b : List ℤ × ℤ}
    (hb : b ∈ π) : b.2 ∈ ({4, 5} : Set ℤ) :=
  trPassage_closing_mem h.1 hb

/-- For `π ∈ 𝒳_{c,o,r}(s)`, the position `r` is at most `M = j(Bp_{|π|}(π))`. -/
lemma trRawThreeWitness_le (h : π ∈ trRawThreeWitness s c o r) :
    r ≤ (chBlockPath π π.length).1.toNat :=
  h.2.1

/-- For `π ∈ 𝒳_{c,o,r}(s)`, the `r`-th letter of `raw_M(π)` is `c`. -/
lemma trRawThreeWitness_getElem? (h : π ∈ trRawThreeWitness s c o r) :
    (chRaw (chBlockPath π π.length).1.toNat π)[r - 1]? = some c :=
  h.2.2.1

/-- For `π ∈ 𝒳_{c,o,r}(s)`, `σ_r(π) = s + o`. -/
lemma trRawThreeWitness_trRawSum (h : π ∈ trRawThreeWitness s c o r) :
    trRawSum π r = s + o :=
  h.2.2.2

/-- The `r`-th letter read off the full concatenation `z = c¹ (e¹) ⋯ cᵏ (eᵏ)`: the
position `r` is in range and `z_r = c`. -/
lemma trRawThreeWitness_getElem_flatMap (h : π ∈ trRawThreeWitness s c o r) :
    ∃ hlt : r - 1 < (π.flatMap fun b => b.1 ++ [b.2]).length,
      (π.flatMap fun b => b.1 ++ [b.2])[r - 1] = c := by
  have h3 := trRawThreeWitness_getElem? h
  rw [chRaw_toNat_chBlockPath_fst] at h3
  exact List.getElem?_eq_some_iff.mp h3

/-- For `π ∈ 𝒳_{c,o,r}(s)` with `0 < o`, the level is crossed at `r`: `s < σ_r(π)`. -/
lemma trRawThreeWitness_lt_trRawSum (h : π ∈ trRawThreeWitness s c o r) (ho : 0 < o) :
    (s : ℤ) < trRawSum π r := by
  rw [trRawThreeWitness_trRawSum h]
  omega

end CollatzPosDens
