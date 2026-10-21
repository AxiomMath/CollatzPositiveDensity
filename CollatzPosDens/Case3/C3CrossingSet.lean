/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# First raw crossing sets

For `ω ∈ ℕ` and integers `c ≥ 2`, `o` and `r ≥ 1`, the first raw crossing set
`𝒞_ω(c, o, r)` is the set of passage lists `π ∈ Π_ω` whose raw word has length
`j(Bp_{|π|}(π)) ≥ r` and whose raw partial sums satisfy `σ_{r-1}(π) = ω + o - c` and
`σ_r(π) = ω + o`. Thus the `r`-th raw letter of `π` is `c`, and it carries the raw partial sums
from height `ω + o - c` to height `ω + o`.

## Main definitions

* `CollatzPosDens.c3CrossingSet ω c o r`: the first raw crossing set `𝒞_ω(c, o, r)`.

## Main results

* `CollatzPosDens.mem_c3CrossingSet`: the defining characterisation of `π ∈ 𝒞_ω(c, o, r)`.
* `CollatzPosDens.c3CrossingSet_subset_trPassage`: `𝒞_ω(c, o, r) ⊆ Π_ω`.
* `CollatzPosDens.trRawSum_sub_of_mem_c3CrossingSet`: on `𝒞_ω(c, o, r)`, the `r`-th raw
  letter is `c`, i.e. `σ_r(π) - σ_{r-1}(π) = c`.

## Implementation notes

The index `r` is a natural number, since it indexes raw partial sums; the conditions `c ≥ 2`
and `r ≥ 1` only restrict the range of parameters of interest and are not needed to form the
set, so they are not part of the definition. For `r ≥ 1`, `r - 1` is the truncated
subtraction of `ℕ`, which agrees with integer subtraction. The length `j(Bp_{|π|}(π))` is an
integer and is compared with the cast of `r`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The first raw crossing set `𝒞_ω(c, o, r)`: the passage lists `π ∈ Π_ω` with
`j(Bp_{|π|}(π)) ≥ r`, `σ_{r-1}(π) = ω + o - c` and `σ_r(π) = ω + o`. -/
@[collatz_pos_dens "def_c3_crossing_set"]
def c3CrossingSet (ω : ℕ) (c o : ℤ) (r : ℕ) : Set (List (List ℤ × ℤ)) :=
  {π | π ∈ trPassage ω ∧ (r : ℤ) ≤ (chBlockPath π π.length).1 ∧
    trRawSum π (r - 1) = ω + o - c ∧ trRawSum π r = ω + o}

/-- The defining characterisation of `π ∈ 𝒞_ω(c, o, r)`. -/
lemma mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ} {π : List (List ℤ × ℤ)} :
    π ∈ c3CrossingSet ω c o r ↔ π ∈ trPassage ω ∧ (r : ℤ) ≤ (chBlockPath π π.length).1 ∧
      trRawSum π (r - 1) = ω + o - c ∧ trRawSum π r = ω + o :=
  Iff.rfl

/-- `𝒞_ω(c, o, r) ⊆ Π_ω`. -/
lemma c3CrossingSet_subset_trPassage (ω : ℕ) (c o : ℤ) (r : ℕ) :
    c3CrossingSet ω c o r ⊆ trPassage ω :=
  fun _ h ↦ h.1

/-- A list in `𝒞_ω(c, o, r)` has raw word of length at least `r`. -/
lemma le_chBlockPath_fst_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ}
    {π : List (List ℤ × ℤ)} (h : π ∈ c3CrossingSet ω c o r) :
    (r : ℤ) ≤ (chBlockPath π π.length).1 :=
  h.2.1

/-- On `𝒞_ω(c, o, r)`, `σ_{r-1}(π) = ω + o - c`. -/
lemma trRawSum_pred_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ}
    {π : List (List ℤ × ℤ)} (h : π ∈ c3CrossingSet ω c o r) :
    trRawSum π (r - 1) = ω + o - c :=
  h.2.2.1

/-- On `𝒞_ω(c, o, r)`, `σ_r(π) = ω + o`. -/
lemma trRawSum_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ}
    {π : List (List ℤ × ℤ)} (h : π ∈ c3CrossingSet ω c o r) :
    trRawSum π r = ω + o :=
  h.2.2.2

/-- On `𝒞_ω(c, o, r)`, the raw partial sums jump by `c` at index `r`:
`σ_r(π) - σ_{r-1}(π) = c`. -/
lemma trRawSum_sub_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ}
    {π : List (List ℤ × ℤ)} (h : π ∈ c3CrossingSet ω c o r) :
    trRawSum π r - trRawSum π (r - 1) = c := by
  rw [trRawSum_of_mem_c3CrossingSet h, trRawSum_pred_of_mem_c3CrossingSet h]
  ring

/-- On `𝒞_ω(c, o, r)`, the offset is determined: `o = σ_r(π) - ω`. -/
lemma eq_trRawSum_sub_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ}
    {π : List (List ℤ × ℤ)} (h : π ∈ c3CrossingSet ω c o r) :
    o = trRawSum π r - ω := by
  rw [trRawSum_of_mem_c3CrossingSet h]
  ring

end CollatzPosDens
