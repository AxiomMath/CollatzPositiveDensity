/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Tuples

/-!
# Prefixes of central histories

Let `M` be an odd positive integer, `n ≥ 0`, `h = (w₀, …, w_{n-1}) ∈ 𝓗_n(M)` and `0 ≤ j ≤ n`.
Then the prefix `(w₀, …, w_{j-1})` lies in `𝓗_j(M)`: each of its entries lies in its central
family, its first five entries (if `j ≥ 5`) are those of `h` and so satisfy the selection
condition defining `selectedTuples`, and its concatenated word is a prefix of `ŵ(h)`, hence
admissible from `M`.

## Main results

* `CollatzPosDens.centralHistories_prefix`: the prefix of length `j ≤ n` of a central history
  of generation `n` from `M` is a central history of generation `j` from `M`.

## Implementation notes

The statement holds for every rational starting point `M`; the oddness and positivity of `M` are
not used and are dropped. The prefix `(w₀, …, w_{j-1})` is the map `i ↦ h (Fin.castLE hj i)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The concatenated word of a prefix of a tuple, followed by the remaining words, is the
concatenated word of the tuple. -/
theorem centralHistories_prefix_concatWord_append {n j : ℕ} (h : Fin n → Word) (hj : j ≤ n) :
    concatWord (fun i : Fin j => h (Fin.castLE hj i)) ++ ((List.ofFn h).drop j).flatten =
      concatWord h := by
  have : concatWord (fun i : Fin j => h (Fin.castLE hj i)) = ((List.ofFn h).take j).flatten := by
    rw [concatWord]
    congr 1
    apply List.ext_getElem
    · simp; omega
    · intro i h₁ h₂
      simp
  rw [this, ← List.flatten_append, List.take_append_drop, concatWord]

/-- **Prefixes of central histories.** If `h = (w₀, …, w_{n-1}) ∈ 𝓗_n(M)` and `j ≤ n`, then
`(w₀, …, w_{j-1}) ∈ 𝓗_j(M)`. -/
@[collatz_pos_dens "lem_s05_history_prefix"]
theorem centralHistories_prefix {M : ℚ} {n j : ℕ} {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) (hj : j ≤ n) :
    (fun i : Fin j => h (Fin.castLE hj i)) ∈ centralHistories M j := by
  refine ⟨selectedTuples_restrict hj hh.1, ?_⟩
  have := hh.2
  rw [← centralHistories_prefix_concatWord_append h hj, admissible_append] at this
  exact this.1

end CollatzPosDens
