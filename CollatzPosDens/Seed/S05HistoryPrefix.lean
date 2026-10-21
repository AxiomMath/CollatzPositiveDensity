/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05Tuples

/-!
# Prefixes of central histories

Let `t` be an odd positive integer, `0 ≤ j ≤ n` and `h = (w_0, …, w_{n-1}) ∈ 𝓗_n(t)`. Then the
prefix `(w_0, …, w_{j-1})`, which is the empty tuple when `j = 0`, lies in `𝓗_j(t)`: each of its
entries lies in its central family, it satisfies the selector `Sel_j` because `h` satisfies
`Sel_n`, and its concatenated word is a prefix of `ŵ(h)`, hence admissible from `t`
(`CollatzPosDens.admissible_append`).

## Main results

* `CollatzPosDens.centralHistories_prefix`: the prefix up to generation `j ≤ n` of a central
  history of generation `n` from `t` is a central history of generation `j` from `t`.

## Implementation notes

The statement holds for every rational starting point `t`, without assuming that `t` is odd or
positive. A history of generation `n` is a map `h : Fin n → Word`, its entry `k`
being `w_k`, and the prefix `(w_0, …, w_{j-1})` is the map `k ↦ h (Fin.castLE _ k)` on `Fin j`.

## References

* [Mazur, *Collatz positive density*], §16.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The concatenated word of a prefix of a tuple, followed by the remaining words, is the
concatenated word of the tuple. -/
theorem centralHistories_prefix_concatWord_append {n j : ℕ} (h : Fin n → Word)
    (hj : j ≤ n) :
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

/-- **Prefixes of central histories.** If `h = (w_0, …, w_{n-1}) ∈ 𝓗_n(t)` and `j ≤ n`,
then `(w_0, …, w_{j-1}) ∈ 𝓗_j(t)`, this tuple being empty if `j = 0`. -/
@[collatz_pos_dens "lem_s05_history_prefix"]
theorem centralHistories_prefix {t : ℚ} {n j : ℕ} {h : Fin n → Word}
    (hh : h ∈ centralHistories t n) (hj : j ≤ n) :
    (fun k : Fin j => h (Fin.castLE hj k)) ∈ centralHistories t j := by
  refine ⟨selectedTuples_restrict hj hh.1, ?_⟩
  have := hh.2
  rw [← centralHistories_prefix_concatWord_append h hj, admissible_append] at this
  exact this.1

end CollatzPosDens
