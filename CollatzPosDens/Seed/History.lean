/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Seed.ConcatWord
public import CollatzPosDens.Seed.Tuples

/-!
# Central histories

Let `M` be an odd positive integer and `n ≥ 0`. The set of *central histories of generation `n`
from `M`* is
`𝓗_n(M) = {h ∈ 𝔗_n : ŵ(h) is admissible from M}`,
where `𝔗_n` is the set of selected central tuples and `ŵ(h) = w₀ ⋯ w_{n-1}` is the
concatenated word of `h = (w₀, …, w_{n-1})`. The weight `ω`, the valuation sum `A`, the offset
`off` and the length are applied to a history through `ŵ(h)`; the depth of `h` is
`D(h) = |ŵ(h)|`. The generation-`j` endpoint of `h` (`0 ≤ j ≤ n`) is the rational number
`R_j(h) = src(w₀ ⋯ w_{j-1}, M)`, and the endpoint of `h` is `R_h = R_n(h)`.

## Main definitions

* `CollatzPosDens.centralHistories M n`: the set `𝓗_n(M)`.
* `CollatzPosDens.historyDepth h`: the depth `D(h) = |ŵ(h)|`.
* `CollatzPosDens.historyEndpointAt M h j`: the generation-`j` endpoint `R_j(h)`.
* `CollatzPosDens.historyEndpoint M h`: the endpoint `R_h = R_n(h)`.

## Main results

* `CollatzPosDens.mem_centralHistories`: the defining membership condition.
* `CollatzPosDens.centralHistories_finite`: `𝓗_n(M)` is finite.
* `CollatzPosDens.historyDepth_eq_sum`: `D(h) = ∑ⱼ |wⱼ|`.
* `CollatzPosDens.valSum_concatWord`: `A(ŵ(h)) = ∑ⱼ A(wⱼ)`.
* `CollatzPosDens.historyEndpointAt_zero`: `R_0(h) = M`.
* `CollatzPosDens.historyEndpointAt_succ`: `R_{j+1}(h) = src(w_j, R_j(h))`.
* `CollatzPosDens.historyEndpointAt_eq_src_concatWord`: `R_j(h) = src(ŵ(h|_{<j}), M)`.
* `CollatzPosDens.historyEndpoint_eq_src`: `R_h = src(ŵ(h), M)`.

## Implementation notes

A history of generation `n` is a map `Fin n → Word`, and `𝓗_n(M)` is a `Set`, matching
`CollatzPosDens.selectedTuples`. The weight, valuation sum and offset of a history are not
given separate names: they are `ω(concatWord h)`, `A(concatWord h)` and `off(concatWord h)`.
The starting point `M` is taken in `ℚ`, as for `CollatzPosDens.Admissible` and
`CollatzPosDens.src`; the oddness and positivity of `M` are not needed to state the definition
and are assumed by the results that use them. The generation-`j` endpoint is defined for every
`j : ℕ` as the source of the concatenation of the first `min j n` words, so that `R_j(h) = R_n(h)`
for `j ≥ n`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The set `𝓗_n(M)` of central histories of generation `n` from `M`: the selected central
tuples `h ∈ 𝔗_n` whose concatenated word `ŵ(h)` is admissible from `M`. -/
@[collatz_pos_dens "def_history"]
def centralHistories (M : ℚ) (n : ℕ) : Set (Fin n → Word) :=
  {h | h ∈ selectedTuples n ∧ Admissible M (concatWord h)}

/-- The depth `D(h) = |ŵ(h)|` of a history. -/
@[collatz_pos_dens "def_history"]
def historyDepth (h : Fin n → Word) : ℕ := (concatWord h).length

/-- The generation-`j` endpoint `R_j(h) = src(w₀ ⋯ w_{j-1}, M)` of a history `h`. -/
@[collatz_pos_dens "def_history"]
def historyEndpointAt (M : ℚ) (h : Fin n → Word) (j : ℕ) : ℚ :=
  src ((List.ofFn h).take j).flatten M

/-- The endpoint `R_h = R_n(h)` of a history `h` of generation `n`. -/
@[collatz_pos_dens "def_history"]
def historyEndpoint (M : ℚ) (h : Fin n → Word) : ℚ := historyEndpointAt M h n

/-- Membership in the set `𝓗_n(M)` of central histories. -/
theorem mem_centralHistories {M : ℚ} {h : Fin n → Word} :
    h ∈ centralHistories M n ↔ h ∈ selectedTuples n ∧ Admissible M (concatWord h) :=
  Iff.rfl

/-- A central history is a selected central tuple. -/
theorem centralHistories_subset_selectedTuples (M : ℚ) (n : ℕ) :
    centralHistories M n ⊆ selectedTuples n :=
  fun _ hh => hh.1

/-- The set `𝓗_n(M)` of central histories is finite. -/
theorem centralHistories_finite (M : ℚ) (n : ℕ) : (centralHistories M n).Finite :=
  (selectedTuples_finite n).subset (centralHistories_subset_selectedTuples M n)

/-- The concatenated word of a central history is admissible from `M`. -/
theorem admissible_concatWord_of_mem_centralHistories {M : ℚ} {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) : Admissible M (concatWord h) :=
  hh.2

/-- The depth of a history is the sum of the lengths of its words. -/
theorem historyDepth_eq_sum (h : Fin n → Word) : historyDepth h = ∑ j, (h j).length :=
  length_concatWord h

/-- The valuation sum of the concatenated word of a history is the sum of the valuation sums of
its words. -/
theorem valSum_concatWord (h : Fin n → Word) : (concatWord h).valSum = ∑ j, (h j).valSum := by
  simp [concatWord, Word.valSum, List.map_flatten, List.sum_flatten, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]

/-- The generation-`0` endpoint is the starting point: `R_0(h) = M`. -/
@[simp] theorem historyEndpointAt_zero (M : ℚ) (h : Fin n → Word) :
    historyEndpointAt M h 0 = M := rfl

/-- One generation of a history: `R_{j+1}(h) = src(w_j, R_j(h))` for `j < n`. -/
theorem historyEndpointAt_succ (M : ℚ) (h : Fin n → Word) {j : ℕ} (hj : j < n) :
    historyEndpointAt M h (j + 1) = src (h ⟨j, hj⟩) (historyEndpointAt M h j) := by
  rw [historyEndpointAt, flatten_take_succ_ofFn h hj, src_append, historyEndpointAt]

/-- For `j ≤ n`, the generation-`j` endpoint is the source of the concatenation of the first `j`
words: `R_j(h) = src(ŵ(w₀, …, w_{j-1}), M)`. -/
theorem historyEndpointAt_eq_src_concatWord (M : ℚ) (h : Fin n → Word) {j : ℕ} (hj : j ≤ n) :
    historyEndpointAt M h j = src (concatWord fun i : Fin j => h (Fin.castLE hj i)) M := by
  rw [historyEndpointAt, concatWord]
  congr 2
  apply List.ext_getElem
  · simp; omega
  · intro i h₁ h₂
    simp

/-- The generation-`j` endpoints stabilise at `R_n(h)` from `j = n` on. -/
theorem historyEndpointAt_of_le (M : ℚ) (h : Fin n → Word) {j : ℕ} (hj : n ≤ j) :
    historyEndpointAt M h j = historyEndpoint M h := by
  simp [historyEndpoint, historyEndpointAt, List.take_of_length_le, hj]

/-- The endpoint of a history is the source of its concatenated word: `R_h = src(ŵ(h), M)`. -/
theorem historyEndpoint_eq_src (M : ℚ) (h : Fin n → Word) :
    historyEndpoint M h = src (concatWord h) M := by
  rw [historyEndpoint, historyEndpointAt, List.take_of_length_le (by simp), concatWord]

end CollatzPosDens
