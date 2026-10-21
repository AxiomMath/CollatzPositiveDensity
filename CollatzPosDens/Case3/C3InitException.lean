/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingSet
public import CollatzPosDens.Transfer.S02Hpack

/-!
# The common initial exception

For a Fourier index `ι ∈ 𝔍` and `ω ∈ ℕ`, the common initial exception `𝓑_init(ι, ω)` is the
set of passage lists `π ∈ Π_ω` lying in a first raw crossing set `𝒞_ω(c, o, r)` with integers
`c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1` for which at least one of the following holds:

* the raw word continues for more than `H_pk(ι)` letters after the crossing,
  `j(Bp_{|π|}(π)) - r > H_pk(ι)`;
* the crossing letter is large, `c > 128`;
* the crossing happens late, `r > ⌊9ω/32⌋`.

## Main definitions

* `CollatzPosDens.c3InitException ι ω`: the common initial exception `𝓑_init(ι, ω)`.

## Main results

* `CollatzPosDens.mem_c3InitException`: the defining characterisation of `π ∈ 𝓑_init(ι, ω)`.
* `CollatzPosDens.c3InitException_subset_trPassage`: `𝓑_init(ι, ω) ⊆ Π_ω`.

## Implementation notes

The crossing index `r` is a natural number, as in `c3CrossingSet`; the letter `c` and the
offset `o` are integers. The length `j(Bp_{|π|}(π))` is the integer
`(chBlockPath π π.length).1`, and the floor `⌊9ω/32⌋` of a nonnegative rational is the natural
number division `9 * ω / 32`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The common initial exception `𝓑_init(ι, ω)`: the passage lists `π ∈ Π_ω` with
`π ∈ 𝒞_ω(c, o, r)` for some integers `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1` such that
`j(Bp_{|π|}(π)) - r > H_pk(ι)`, or `c > 128`, or `r > ⌊9ω/32⌋`. -/
@[collatz_pos_dens "def_c3_init_exception"]
def c3InitException (ι : FIndex) (ω : ℕ) : Set (List (List ℤ × ℤ)) :=
  {π | π ∈ trPassage ω ∧ ∃ (c o : ℤ) (r : ℕ), 2 ≤ c ∧ 1 ≤ o ∧ o ≤ c ∧ 1 ≤ r ∧
    π ∈ c3CrossingSet ω c o r ∧
    ((Hpack ι : ℤ) < (chBlockPath π π.length).1 - r ∨ 128 < c ∨ 9 * ω / 32 < r)}

/-- The defining characterisation of `π ∈ 𝓑_init(ι, ω)`. -/
lemma mem_c3InitException {ι : FIndex} {ω : ℕ} {π : List (List ℤ × ℤ)} :
    π ∈ c3InitException ι ω ↔ π ∈ trPassage ω ∧ ∃ (c o : ℤ) (r : ℕ), 2 ≤ c ∧ 1 ≤ o ∧ o ≤ c ∧
      1 ≤ r ∧ π ∈ c3CrossingSet ω c o r ∧
      ((Hpack ι : ℤ) < (chBlockPath π π.length).1 - r ∨ 128 < c ∨ 9 * ω / 32 < r) :=
  Iff.rfl

/-- `𝓑_init(ι, ω) ⊆ Π_ω`. -/
lemma c3InitException_subset_trPassage (ι : FIndex) (ω : ℕ) :
    c3InitException ι ω ⊆ trPassage ω :=
  fun _ h ↦ h.1

/-- Membership in `𝓑_init(ι, ω)` from a crossing set witness: the passage condition is
automatic, since `𝒞_ω(c, o, r) ⊆ Π_ω`. -/
lemma mem_c3InitException_of_mem_c3CrossingSet {ι : FIndex} {ω : ℕ} {π : List (List ℤ × ℤ)}
    {c o : ℤ} {r : ℕ} (hc : 2 ≤ c) (ho : 1 ≤ o) (hoc : o ≤ c) (hr : 1 ≤ r)
    (hπ : π ∈ c3CrossingSet ω c o r)
    (hbad : (Hpack ι : ℤ) < (chBlockPath π π.length).1 - r ∨ 128 < c ∨ 9 * ω / 32 < r) :
    π ∈ c3InitException ι ω :=
  ⟨c3CrossingSet_subset_trPassage ω c o r hπ, c, o, r, hc, ho, hoc, hr, hπ, hbad⟩

end CollatzPosDens
