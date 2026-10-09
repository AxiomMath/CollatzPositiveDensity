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
# Raw partial sums

For a list of blocks `π = ((c¹, e¹), …, (cᵏ, eᵏ))`, write `Bp_k(π) = (j, l)` for its final
block path point `chBlockPath π k`, and let `M = j`. Then `M = |c¹| + ⋯ + |cᵏ| + k` is the length
of the concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`, so the raw word `raw_M(π) = chRaw M π` is the whole
concatenation. For `0 ≤ i ≤ M`, the raw partial sum `σ_i(π)` is the sum of the first `i` letters
of `raw_M(π)`; in particular `σ_0(π) = 0`, and `σ_M(π) = l` is the sum of all letters.

## Main definitions

* `CollatzPosDens.trRawSum π i`: the raw partial sum `σ_i(π)`.

## Main results

* `CollatzPosDens.trRawSum_zero`: `σ_0(π) = 0`.
* `CollatzPosDens.trRawSum_eq_sum_take`: `σ_i(π)` is the sum of the first `i` letters of the
  full concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`.
* `CollatzPosDens.trRawSum_succ`: `σ_{i+1}(π) = σ_i(π) + z_{i+1}` for `i < M`, where `z` is
  the concatenation.
* `CollatzPosDens.trRawSum_of_le`: for `i ≥ M`, `σ_i(π) = l(Bp_k(π))`.

## Implementation notes

A list of blocks `π` is a `List (List ℤ × ℤ)` with `k = π.length`. The letters are integers, so
`σ_i(π)` is an integer. The coordinate `M = j` is an integer which is nonnegative
(`chBlockPath_fst_nonneg`); it is converted to a length by `Int.toNat`, which loses nothing.
The index `i` is any natural number and the side condition `i ≤ M` is not part of the
definition: for `i ≥ M` the value is `σ_M(π)` (`trRawSum_of_le`). The hypothesis `k ≥ 1` is
likewise not needed to define `σ_i(π)`; for the empty list every `σ_i` vanishes.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The raw partial sum `σ_i(π)`: the sum of the first `i` letters of `raw_M(π)`, where
`M = j(Bp_k(π))` and `k = |π|`. -/
@[collatz_pos_dens "def_tr_raw_sum"]
def trRawSum (π : List (List ℤ × ℤ)) (i : ℕ) : ℤ :=
  ((chRaw (chBlockPath π π.length).1.toNat π).take i).sum

/-- `σ_i(π)` is the sum of the first `i` letters of `raw_M(π)`, where `M = j(Bp_k(π))`. -/
lemma trRawSum_def (π : List (List ℤ × ℤ)) (i : ℕ) :
    trRawSum π i = ((chRaw (chBlockPath π π.length).1.toNat π).take i).sum := rfl

/-- `σ_0(π) = 0`. -/
@[simp]
lemma trRawSum_zero (π : List (List ℤ × ℤ)) : trRawSum π 0 = 0 := by
  simp [trRawSum]

/-- `M = j(Bp_k(π))` is the length `|c¹| + ⋯ + |cᵏ| + k` of the concatenation. -/
lemma toNat_chBlockPath_fst (π : List (List ℤ × ℤ)) :
    (chBlockPath π π.length).1.toNat = (π.flatMap fun b => b.1 ++ [b.2]).length := by
  rw [chBlockPath_fst, chRaw_length_concat, List.take_length, min_self]
  have : ((π.map fun b => (b.1.length : ℤ))).sum = ((π.map fun b => b.1.length).sum : ℕ) := by
    simp [Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [this]
  omega

/-- `raw_M(π)` with `M = j(Bp_k(π))` is the full concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`. -/
lemma chRaw_toNat_chBlockPath_fst (π : List (List ℤ × ℤ)) :
    chRaw (chBlockPath π π.length).1.toNat π = π.flatMap fun b => b.1 ++ [b.2] := by
  rw [toNat_chBlockPath_fst, chRaw, List.take_length]

/-- `σ_i(π)` is the sum of the first `i` letters of the concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`. -/
lemma trRawSum_eq_sum_take (π : List (List ℤ × ℤ)) (i : ℕ) :
    trRawSum π i = ((π.flatMap fun b => b.1 ++ [b.2]).take i).sum := by
  rw [trRawSum, chRaw_toNat_chBlockPath_fst]

/-- `σ_{i+1}(π) = σ_i(π) + z_{i+1}`, where `z` is the concatenation `c¹ (e¹) ⋯ cᵏ (eᵏ)`. -/
lemma trRawSum_succ (π : List (List ℤ × ℤ)) {i : ℕ}
    (hi : i < (π.flatMap fun b => b.1 ++ [b.2]).length) :
    trRawSum π (i + 1) = trRawSum π i + (π.flatMap fun b => b.1 ++ [b.2])[i] := by
  simp only [trRawSum_eq_sum_take, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some, List.sum_append, List.sum_cons, List.sum_nil, add_zero]

/-- The total sum of the letters of `π` is `l(Bp_k(π))`. -/
lemma sum_flatMap_eq_chBlockPath_snd (π : List (List ℤ × ℤ)) :
    (π.flatMap fun b => b.1 ++ [b.2]).sum = (chBlockPath π π.length).2 := by
  rw [chBlockPath_snd, List.take_length]
  induction π with
  | nil => simp
  | cons b π ih =>
    simp only [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons, List.sum_nil,
      add_zero]

/-- For `i ≥ M = j(Bp_k(π))`, `σ_i(π) = l(Bp_k(π))`; in particular `σ_M(π) = l(Bp_k(π))`. -/
lemma trRawSum_of_le (π : List (List ℤ × ℤ)) {i : ℕ}
    (hi : (chBlockPath π π.length).1.toNat ≤ i) :
    trRawSum π i = (chBlockPath π π.length).2 := by
  rw [toNat_chBlockPath_fst] at hi
  rw [trRawSum_eq_sum_take, List.take_of_length_le hi, sum_flatMap_eq_chBlockPath_snd]

/-- `σ_M(π) = l(Bp_k(π))` for `M = j(Bp_k(π))`. -/
lemma trRawSum_self (π : List (List ℤ × ℤ)) :
    trRawSum π (chBlockPath π π.length).1.toNat = (chBlockPath π π.length).2 :=
  trRawSum_of_le π le_rfl

end CollatzPosDens
