/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Seed.History

/-!
# One step of a central history

Let `t` be an odd positive integer, `0 ≤ j < n` and `h = (w_0, …, w_{n-1}) ∈ 𝓗_n(t)`. Then the
generation-`j` endpoint `R_j(h)` is a positive odd integer and `w_j` is admissible from `R_j(h)`.

## Main results

* `CollatzPosDens.concatWord_eq_take_append_append_drop`: the splitting
  `ŵ(h) = (w₀ ⋯ w_{j-1}) w_j (w_{j+1} ⋯ w_{m-1})` of a concatenated word at block `j`.
* `CollatzPosDens.centralHistories.historyEndpointAt_step`: for `j < n`, the endpoint
  `R_j(h)` is a positive odd integer and `w_j` is admissible from it.

## Implementation notes

A history is a map `h : Fin n → Word` whose entry `k` is `w_k`, so `w_j` is the entry `⟨j, _⟩`
of `h`. The starting point `t` is an integer cast to `ℚ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/
@[expose] public section

namespace CollatzPosDens

/-- The concatenated word of a tuple splits at block `j` as
`ŵ(h) = (w₀ ⋯ w_{j-1}) w_j (w_{j+1} ⋯ w_{n-1})`. -/
theorem concatWord_eq_take_append_append_drop {n : ℕ} (h : Fin n → Word) {j : ℕ} (hj : j < n) :
    concatWord h = (((List.ofFn h).take j).flatten ++ h ⟨j, hj⟩) ++
      ((List.ofFn h).drop (j + 1)).flatten := by
  rw [← flatten_take_succ_ofFn h hj, ← List.flatten_append, List.take_append_drop, concatWord]

/-- **One step of a central history.** If `t` is a positive odd integer,
`h = (w_0, …, w_{n-1}) ∈ 𝓗_n(t)` and `j < n`, then `R_j(h)` is a positive odd integer and `w_j`
is admissible from `R_j(h)`. -/
@[collatz_pos_dens "lem_s05_history_step"]
theorem centralHistories.historyEndpointAt_step {t : ℤ} (htpos : 0 < t) (htodd : Odd t)
    {n : ℕ} {h : Fin n → Word} (hh : h ∈ centralHistories (t : ℚ) n) {j : ℕ} (hj : j < n) :
    (∃ m : ℤ, historyEndpointAt (t : ℚ) h j = m ∧ 0 < m ∧ Odd m) ∧
      Admissible (historyEndpointAt (t : ℚ) h j) (h ⟨j, hj⟩) := by
  have hadm := hh.2
  rw [concatWord_eq_take_append_append_drop h hj, admissible_append,
    admissible_append] at hadm
  exact ⟨hadm.1.1.exists_src_eq_pos_odd htpos htodd, hadm.1.2⟩

end CollatzPosDens
