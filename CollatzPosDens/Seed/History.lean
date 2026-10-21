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
public import CollatzPosDens.Seed.S05ConcatWord
public import CollatzPosDens.Seed.S05Tuples

/-!
# Central histories

Let `t` be an odd positive integer and `n ≥ 0`. The set of *central histories of generation `n`
from `t`* is
`𝓗_n(t) = {h ∈ 𝔗_n : ŵ(h) is admissible from t}`,
where `𝔗_n = CollatzPosDens.selectedTuples n` is the set of selected central tuples
`h = (w_0, …, w_{n-1})`, `ŵ(h) = w_0 ⋯ w_{n-1}` is their concatenated word
`CollatzPosDens.concatWord h`, and admissibility is `CollatzPosDens.Admissible`. The weight
`ω = CollatzPosDens.weight`, the valuation sum `A = CollatzPosDens.valSum`, the offset
`off = CollatzPosDens.off` and the length are applied to a history through `ŵ(h)`; the depth of
`h` is `D(h) = |ŵ(h)|`. The generation-`j` endpoint of `h` (`0 ≤ j ≤ n`) is the rational number
`R_j(h) = src(w_0 ⋯ w_{j-1}, t)`, where `src = CollatzPosDens.src` and `w_0 ⋯ w_{j-1}` is the
empty word when `j = 0`, so that `R_0(h) = t`; the endpoint of `h` is `R_h = R_n(h)`.

## Main definitions

* `CollatzPosDens.centralHistories t n`: the set `𝓗_n(t)`.
* `CollatzPosDens.historyDepth h`: the depth `D(h) = |ŵ(h)|`.
* `CollatzPosDens.historyEndpointAt t h j`: the generation-`j` endpoint `R_j(h)`.
* `CollatzPosDens.historyEndpoint t h`: the endpoint `R_h = R_n(h)`.

## Main results

* `CollatzPosDens.mem_centralHistories`: the defining membership condition.
* `CollatzPosDens.centralHistories_finite`: `𝓗_n(t)` is finite.
* `CollatzPosDens.historyDepth_eq_sum`: `D(h) = ∑ⱼ |wⱼ|`.
* `CollatzPosDens.valSum_concatWord`: `A(ŵ(h)) = ∑ⱼ A(wⱼ)`.
* `CollatzPosDens.historyEndpointAt_zero`: `R_0(h) = t`.
* `CollatzPosDens.historyEndpointAt_succ`: `R_{j+1}(h) = src(w_j, R_j(h))` for `j < n`.
* `CollatzPosDens.historyEndpointAt_eq_src_concatWord`: `R_j(h) = src(w_0 ⋯ w_{j-1}, t)`
  with `w_0 ⋯ w_{j-1}` a concatenated word.
* `CollatzPosDens.historyEndpoint_eq_src`: `R_h = src(ŵ(h), t)`.

## Implementation notes

A history `(w_0, …, w_{n-1})` of generation `n` is a map `h : Fin n → Word`, its entry `k` being
`w_k`, and `𝓗_n(t)` is a `Set`, matching `CollatzPosDens.selectedTuples`.
The weight, valuation sum and offset of a history are not given separate names: they are
`ω(concatWord h)`, `A(concatWord h)` and `off(concatWord h)`; likewise the depth and the
endpoints are stated for tuples of words of any length. The starting point `t` is taken in `ℚ`,
as for `CollatzPosDens.Admissible` and `CollatzPosDens.src`; the oddness and positivity of `t`
are not needed to state the definition and are assumed by the results that use them. The
generation-`j` endpoint is defined for every `j : ℕ` as the source of the concatenation of the
first `min j n` words, so that `R_j(h) = R_n(h)` for `j ≥ n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.1.
-/
@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The set `𝓗_n(t)` of central histories of generation `n` from `t`: the selected central
tuples `h = (w_0, …, w_{n-1}) ∈ 𝔗_n` whose concatenated word `ŵ(h)` is admissible from `t`. -/
@[collatz_pos_dens "def_history"]
def centralHistories (t : ℚ) (n : ℕ) : Set (Fin n → Word) :=
  {h | h ∈ selectedTuples n ∧ Admissible t (concatWord h)}

/-- The depth `D(h) = |ŵ(h)|` of a history. -/
@[collatz_pos_dens "def_history"]
def historyDepth (h : Fin n → Word) : ℕ := (concatWord h).length

/-- The generation-`j` endpoint `R_j(h) = src(w_0 ⋯ w_{j-1}, t)` of a history
`h = (w_0, …, w_{n-1})`; for `j = 0` the word `w_0 ⋯ w_{j-1}` is empty and `R_0(h) = t`, and for
`j ≥ n` the endpoint is `R_n(h)`. -/
@[collatz_pos_dens "def_history"]
def historyEndpointAt (t : ℚ) (h : Fin n → Word) (j : ℕ) : ℚ :=
  src ((List.ofFn h).take j).flatten t

/-- The endpoint `R_h = R_n(h)` of a history `h` of generation `n`. -/
@[collatz_pos_dens "def_history"]
def historyEndpoint (t : ℚ) (h : Fin n → Word) : ℚ := historyEndpointAt t h n

/-- Membership in the set `𝓗_n(t)` of central histories. -/
theorem mem_centralHistories {t : ℚ} {h : Fin n → Word} :
    h ∈ centralHistories t n ↔ h ∈ selectedTuples n ∧ Admissible t (concatWord h) :=
  Iff.rfl

/-- A central history is a selected central tuple. -/
theorem centralHistories_subset_selectedTuples (t : ℚ) (n : ℕ) :
    centralHistories t n ⊆ selectedTuples n :=
  fun _ hh => hh.1

/-- The set `𝓗_n(t)` of central histories is finite. -/
theorem centralHistories_finite (t : ℚ) (n : ℕ) : (centralHistories t n).Finite :=
  (selectedTuples_finite n).subset (centralHistories_subset_selectedTuples t n)

/-- The concatenated word of a central history is admissible from `t`. -/
theorem admissible_concatWord_of_mem_centralHistories {t : ℚ} {h : Fin n → Word}
    (hh : h ∈ centralHistories t n) : Admissible t (concatWord h) :=
  hh.2

/-- The depth of a history is the sum of the lengths of its words. -/
theorem historyDepth_eq_sum (h : Fin n → Word) : historyDepth h = ∑ j, (h j).length :=
  length_concatWord h

/-- The valuation sum of the concatenated word of a history is the sum of the valuation sums of
its words. -/
theorem valSum_concatWord (h : Fin n → Word) : (concatWord h).valSum = ∑ j, (h j).valSum := by
  simp [concatWord, Word.valSum, List.map_flatten, List.sum_flatten, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]

/-- The generation-`0` endpoint is the starting point: `R_0(h) = t`. -/
@[simp] theorem historyEndpointAt_zero (t : ℚ) (h : Fin n → Word) :
    historyEndpointAt t h 0 = t := rfl

/-- One generation of a history: `R_{j+1}(h) = src(w_j, R_j(h))` for `j < n`. -/
theorem historyEndpointAt_succ (t : ℚ) (h : Fin n → Word) {j : ℕ} (hj : j < n) :
    historyEndpointAt t h (j + 1) = src (h ⟨j, hj⟩) (historyEndpointAt t h j) := by
  rw [historyEndpointAt, flatten_take_succ_ofFn h hj, src_append, historyEndpointAt]

/-- Flattening the first `k ≤ m` blocks of a tuple of `m` words gives the concatenated word of
the restricted tuple. -/
private theorem flatten_take_ofFn {m k : ℕ} (h : Fin m → Word) (hk : k ≤ m) :
    ((List.ofFn h).take k).flatten = concatWord fun i : Fin k => h (Fin.castLE hk i) := by
  rw [concatWord]
  congr 1
  exact List.ext_getElem (by simpa using hk) fun _ _ _ => by simp

/-- Flattening the first `k ≥ m` blocks of a tuple of `m` words gives its concatenated word. -/
private theorem flatten_take_ofFn_of_le {m k : ℕ} (h : Fin m → Word) (hk : m ≤ k) :
    ((List.ofFn h).take k).flatten = concatWord h := by
  rw [List.take_of_length_le (by simpa using hk), concatWord]

/-- For `j ≤ n`, the generation-`j` endpoint is the source of the concatenation of the words
`w_0, …, w_{j-1}`: `R_j(h) = src(ŵ(w_0, …, w_{j-1}), t)`. -/
theorem historyEndpointAt_eq_src_concatWord (t : ℚ) (h : Fin n → Word) {j : ℕ}
    (hj : j ≤ n) :
    historyEndpointAt t h j = src (concatWord fun i : Fin j => h (Fin.castLE hj i)) t := by
  rw [historyEndpointAt, flatten_take_ofFn h hj]

/-- The endpoint of a history is the source of its concatenated word: `R_h = src(ŵ(h), t)`. -/
theorem historyEndpoint_eq_src (t : ℚ) (h : Fin n → Word) :
    historyEndpoint t h = src (concatWord h) t := by
  rw [historyEndpoint, historyEndpointAt, flatten_take_ofFn_of_le h le_rfl]

/-- The generation-`j` endpoints stabilise at `R_n(h)` from `j = n` on. -/
theorem historyEndpointAt_of_le (t : ℚ) (h : Fin n → Word) {j : ℕ} (hj : n ≤ j) :
    historyEndpointAt t h j = historyEndpoint t h := by
  rw [historyEndpoint_eq_src, historyEndpointAt, flatten_take_ofFn_of_le h hj]

end CollatzPosDens
