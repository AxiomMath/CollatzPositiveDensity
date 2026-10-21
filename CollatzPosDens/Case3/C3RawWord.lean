/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChRaw

/-!
# The full raw word of a list of blocks

For `K ∈ ℕ` and a list of blocks `π = (π¹, …, π^K)`, `πᵏ = (cᵏ, eᵏ)`, the *full raw word*
`raw(π) := raw_M(π) ∈ ℤ^M` with `M = j(Bp_K(π))` is the word of all letters of `π`: the
concatenation `c¹ (e¹) c² (e²) ⋯ c^K (e^K)`, each block's nonclosing letters followed by its
closing letter. Its length is `M = j(Bp_K(π)) = |c¹| + ⋯ + |c^K| + K`.

## Main definitions

* `CollatzPosDens.c3RawWord`: the full raw word `raw(π) = raw_{j(Bp_K(π))}(π)`.

## Main results

* `CollatzPosDens.c3RawWord_eq_flatMap`: `raw(π)` is the full concatenation
  `c¹ (e¹) ⋯ c^K (e^K)`.
* `CollatzPosDens.length_c3RawWord`: `|raw(π)| = j(Bp_K(π))`.
* `CollatzPosDens.c3RawWord_nil`, `CollatzPosDens.c3RawWord_cons`,
  `CollatzPosDens.c3RawWord_append`: `raw` of the empty list, of `b :: π` and of `π ++ π'`.

## Implementation notes

As in `chBlockPath` and `chRaw`, a list `π ∈ 𝔅^K` is modelled as `π : List (List ℤ × ℤ)` with
`K = π.length`. The first coordinate `j(Bp_K(π))` is an integer, nonnegative by
`chBlockPath_fst_nonneg`; it is converted to a natural number with `Int.toNat`. A word of
`ℤ^M` is a `List ℤ` (of length `M`, by `length_c3RawWord`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The full raw word `raw(π) = raw_M(π)` with `M = j(Bp_K(π))`, `K = |π|`: the word of all
letters `c¹ (e¹) ⋯ c^K (e^K)` of the list of blocks `π`. -/
@[collatz_pos_dens "def_c3_raw_word"]
def c3RawWord (π : List (List ℤ × ℤ)) : List ℤ :=
  chRaw (chBlockPath π π.length).1.toNat π

/-- `j(Bp_K(π))` is the length `|c¹| + ⋯ + |c^K| + K` of the concatenation
`c¹ (e¹) ⋯ c^K (e^K)`. -/
lemma toNat_chBlockPath_length_fst (π : List (List ℤ × ℤ)) :
    (chBlockPath π π.length).1.toNat = (π.flatMap fun b => b.1 ++ [b.2]).length := by
  rw [chBlockPath_fst, chRaw_length_concat, List.take_length, min_self]
  have : ((π.map fun b => (b.1.length : ℤ))).sum = ((π.map fun b => b.1.length).sum : ℕ) := by
    simp [Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [this]
  omega

/-- `raw(π)` is the full concatenation `c¹ (e¹) ⋯ c^K (e^K)` of the blocks of `π`. -/
lemma c3RawWord_eq_flatMap (π : List (List ℤ × ℤ)) :
    c3RawWord π = π.flatMap fun b => b.1 ++ [b.2] := by
  rw [c3RawWord, toNat_chBlockPath_length_fst, chRaw, List.take_length]

/-- `raw(π)` has length `j(Bp_K(π))`. -/
lemma length_c3RawWord (π : List (List ℤ × ℤ)) :
    (c3RawWord π).length = (chBlockPath π π.length).1.toNat := by
  rw [c3RawWord_eq_flatMap, toNat_chBlockPath_length_fst]

/-- `raw(π)` has length `|c¹| + ⋯ + |c^K| + K`. -/
lemma length_c3RawWord_eq_sum (π : List (List ℤ × ℤ)) :
    (c3RawWord π).length = (π.map fun b => b.1.length).sum + π.length := by
  rw [c3RawWord_eq_flatMap, chRaw_length_concat]

/-- The raw word of the empty list is empty. -/
@[simp]
lemma c3RawWord_nil : c3RawWord [] = [] := by
  simp [c3RawWord_eq_flatMap]

/-- `raw((c, e) :: π) = c (e) raw(π)`. -/
@[simp]
lemma c3RawWord_cons (b : List ℤ × ℤ) (π : List (List ℤ × ℤ)) :
    c3RawWord (b :: π) = b.1 ++ b.2 :: c3RawWord π := by
  simp [c3RawWord_eq_flatMap]

/-- `raw(π ++ π') = raw(π) raw(π')`. -/
lemma c3RawWord_append (π π' : List (List ℤ × ℤ)) :
    c3RawWord (π ++ π') = c3RawWord π ++ c3RawWord π' := by
  simp [c3RawWord_eq_flatMap]

/-- `raw_J(π)` is the prefix of length `J` of `raw(π)`. -/
lemma chRaw_eq_take_c3RawWord (J : ℕ) (π : List (List ℤ × ℤ)) :
    chRaw J π = (c3RawWord π).take J := by
  rw [c3RawWord_eq_flatMap, chRaw]

end CollatzPosDens
