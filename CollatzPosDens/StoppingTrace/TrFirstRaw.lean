/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# First raw crossing

Let `π : List (List ℤ × ℤ)` be a list of `k ≥ 1` blocks, write `chBlockPath π k = (j, l)` for its
final block-path position, and let `M = j` be the length of the raw word `raw_M(π) = chRaw M π`.
Write `σ_i(π) = trRawSum π i` for the sum of the first `i` letters of
`raw_M(π)`. For a level `s ∈ ℕ`, the first raw crossing `i_s(π)` is the least index
`i ∈ {1, …, M}` with `σ_i(π) > s`, and `M` if there is no such index. It is the position in
`raw_M(π)` at which the running letter sum first goes above the level `s`.

## Main definitions

* `CollatzPosDens.trFirstRaw s π`: the first raw crossing `i_s(π)`.

## Main results

* `CollatzPosDens.trFirstRaw_spec`: if some `i ∈ {1, …, M}` has `σ_i(π) > s`, then
  `i_s(π) ∈ {1, …, M}` and `σ_{i_s(π)}(π) > s`.
* `CollatzPosDens.trFirstRaw_le`: `i_s(π) ≤ M`.
* `CollatzPosDens.one_le_trFirstRaw`: `1 ≤ i_s(π)` when `π` is nonempty.
* `CollatzPosDens.trFirstRaw_mem_Icc`: `i_s(π) ∈ {1, …, M}` when `π` is nonempty.
* `CollatzPosDens.lt_trRawSum_trFirstRaw`: if some `i ∈ {1, …, M}` has `σ_i(π) > s`, then
  `σ_{i_s(π)}(π) > s`.
* `CollatzPosDens.trFirstRaw_le_of_lt`: `i_s(π)` is at most every `i ∈ {1, …, M}` with
  `σ_i(π) > s`.
* `CollatzPosDens.trRawSum_le_of_lt_trFirstRaw`: `σ_i(π) ≤ s` for `i < i_s(π)`.
* `CollatzPosDens.trFirstRaw_of_forall_le`: `i_s(π) = M` when no `σ_i(π)` exceeds `s`.

## Implementation notes

Here `k = π.length`, and `M` is the natural number `(chBlockPath π π.length).1.toNat`, as in
`trRawSum`. The minimum is taken with `Nat.find`, the predicate being decidable, so the definition
is computable. The hypothesis `k ≥ 1` is not needed to define `i_s(π)`; it is used only for the
lower bound `1 ≤ i_s(π)`, since for the empty list `M = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The first raw crossing `i_s(π)`: the least `i ∈ {1, …, M}` with `σ_i(π) > s`, where
`M` is the first coordinate of `chBlockPath π π.length`, or `M` if there is no such `i`. -/
@[collatz_pos_dens "def_tr_first_raw"]
def trFirstRaw (s : ℕ) (π : List (List ℤ × ℤ)) : ℕ :=
  if h : ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i then
    Nat.find h
  else
    (chBlockPath π π.length).1.toNat

variable {s : ℕ} {π : List (List ℤ × ℤ)}

/-- When some `σ_i(π)` with `1 ≤ i ≤ M` exceeds `s`, `i_s(π)` is the least such `i`. -/
lemma trFirstRaw_of_exists
    (h : ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i) :
    trFirstRaw s π = Nat.find h := by
  rw [trFirstRaw, dite_eq_left h]

/-- If no `σ_i(π)` with `1 ≤ i ≤ M` exceeds `s`, then `i_s(π) = M`. -/
lemma trFirstRaw_of_forall_le
    (h : ∀ i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat, trRawSum π i ≤ s) :
    trFirstRaw s π = (chBlockPath π π.length).1.toNat := by
  rw [trFirstRaw, dite_eq_right]
  rintro ⟨i, hi, hlt⟩
  exact absurd (h i hi) (not_le.mpr hlt)

/-- If some `σ_i(π)` with `1 ≤ i ≤ M` exceeds `s`, then `i_s(π)` lies in `{1, …, M}` and
`σ_{i_s(π)}(π) > s`. -/
lemma trFirstRaw_spec
    (h : ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i) :
    trFirstRaw s π ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧
      (s : ℤ) < trRawSum π (trFirstRaw s π) := by
  rw [trFirstRaw_of_exists h]
  exact Nat.find_spec h

/-- If some `σ_i(π)` with `1 ≤ i ≤ M` exceeds `s`, then `σ_{i_s(π)}(π) > s`. -/
lemma lt_trRawSum_trFirstRaw
    (h : ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i) :
    (s : ℤ) < trRawSum π (trFirstRaw s π) :=
  (trFirstRaw_spec h).2

/-- `i_s(π) ≤ M`. -/
lemma trFirstRaw_le : trFirstRaw s π ≤ (chBlockPath π π.length).1.toNat := by
  by_cases h : ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i
  · exact (Finset.mem_Icc.mp (trFirstRaw_spec h).1).2
  · rw [trFirstRaw, dite_eq_right h]

/-- Minimality: `i_s(π) ≤ i` for every `i ∈ {1, …, M}` with `σ_i(π) > s`. -/
lemma trFirstRaw_le_of_lt {i : ℕ} (hi : 1 ≤ i) (hiM : i ≤ (chBlockPath π π.length).1.toNat)
    (h : (s : ℤ) < trRawSum π i) : trFirstRaw s π ≤ i := by
  have hex :
      ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i :=
    ⟨i, Finset.mem_Icc.mpr ⟨hi, hiM⟩, h⟩
  rw [trFirstRaw_of_exists hex]
  exact Nat.find_min' hex ⟨Finset.mem_Icc.mpr ⟨hi, hiM⟩, h⟩

/-- Below the first raw crossing the raw partial sums stay at most `s`: `σ_i(π) ≤ s` for
`i < i_s(π)`. -/
lemma trRawSum_le_of_lt_trFirstRaw {i : ℕ} (hlt : i < trFirstRaw s π) :
    trRawSum π i ≤ s := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  by_contra hcon
  exact absurd (trFirstRaw_le_of_lt hi (hlt.le.trans trFirstRaw_le) (not_le.mp hcon))
    (not_le.mpr hlt)

/-- The first coordinate `M` of `chBlockPath π π.length` is at least `1` for a nonempty list
`π`. -/
lemma one_le_chBlockPath_length_fst_toNat (hπ : π ≠ []) :
    1 ≤ (chBlockPath π π.length).1.toNat := by
  have hlen : 1 ≤ π.length := List.length_pos_iff.mpr hπ
  have hsum : (0 : ℤ) ≤ ((π.take π.length).map fun b => (b.1.length : ℤ)).sum :=
    List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨b, -, rfl⟩; positivity)
  rw [chBlockPath_fst, min_self]
  omega

/-- `1 ≤ i_s(π)` for a nonempty list `π`. -/
lemma one_le_trFirstRaw (hπ : π ≠ []) : 1 ≤ trFirstRaw s π := by
  by_cases h : ∃ i, i ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat ∧ (s : ℤ) < trRawSum π i
  · exact (Finset.mem_Icc.mp (trFirstRaw_spec h).1).1
  · rw [trFirstRaw, dite_eq_right h]
    exact one_le_chBlockPath_length_fst_toNat hπ

/-- `i_s(π) ∈ {1, …, M}` for a nonempty list `π`. -/
lemma trFirstRaw_mem_Icc (hπ : π ≠ []) :
    trFirstRaw s π ∈ Finset.Icc (1 : ℕ) (chBlockPath π π.length).1.toNat :=
  Finset.mem_Icc.mpr ⟨one_le_trFirstRaw hπ, trFirstRaw_le⟩

end CollatzPosDens
