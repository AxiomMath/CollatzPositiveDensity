/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingSet
public import CollatzPosDens.Case3.C3RawWord

/-!
# First raw crossings partition the passage lists

Let `ω ∈ ℕ` and `π ∈ Π_ω`, with `k = |π|`, `M = j(Bp_k(π))` and full raw word
`z = raw(π) ∈ ℤ^M`. Since `π` is live, every letter of `z` is at least `2`, so the raw partial
sums `i ↦ σ_i(π)` are strictly increasing on `0 ≤ i ≤ M`, from `σ_0(π) = 0 ≤ ω` to
`σ_M(π) = l(Bp_k(π)) > ω`. Let `R` be the least index with `σ_R(π) > ω`; then
`π ∈ 𝒞_ω(c, o, R)` with `c = z_R ≥ 2` and `o = σ_R(π) - ω ∈ [1, c]`. Conversely, if
`π ∈ 𝒞_ω(c', o', r')` with `c' ≥ 2` and `1 ≤ o' ≤ c'`, then
`σ_{r'-1}(π) = ω + o' - c' ≤ ω < ω + o' = σ_{r'}(π)`, so `r'` is the first index at which the
raw partial sums exceed `ω`, i.e. `r' = R`, and then `o'` and `c'` are determined. Hence the
first raw crossing sets `𝒞_ω(c, o, r)`, `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1`, partition `Π_ω`.

## Main results

* `CollatzPosDens.trRawSum_le_of_le_of_trLive`: the raw partial sums of a live list are
  nondecreasing.
* `CollatzPosDens.two_le_c3RawWord_getElem`: every letter of the raw word of a live list is
  at least `2`.
* `CollatzPosDens.existsUnique_mem_c3CrossingSet`: every passage list lies in exactly one
  first raw crossing set `𝒞_ω(c, o, r)` with `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1`.

## Implementation notes

A triple `(c, o, r)` is an element of `ℤ × ℤ × ℕ`: the index `r` is a natural number, as in
`c3CrossingSet`, and `r ≥ 1` is the hypothesis `1 ≤ r`. Uniqueness only needs the raw partial
sums to be nondecreasing; strict monotonicity is not used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Every letter of the raw word `raw(π)` of a live list `π` is at least `2`. -/
theorem two_le_of_mem_c3RawWord {π : List (List ℤ × ℤ)} (h : TrLive π) {x : ℤ}
    (hx : x ∈ c3RawWord π) : 2 ≤ x := by
  rw [c3RawWord_eq_flatMap] at hx
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
  exact two_le_of_mem_append_of_chBlockWeight_ne_zero (h b hb) hxb

/-- Every letter `z_{i+1}` of the raw word of a live list is at least `2`. -/
theorem two_le_c3RawWord_getElem {π : List (List ℤ × ℤ)} (h : TrLive π) {i : ℕ}
    (hi : i < (c3RawWord π).length) : 2 ≤ (c3RawWord π)[i] :=
  two_le_of_mem_c3RawWord h (List.getElem_mem hi)

/-- `σ_i(π)` is the sum of the first `i` letters of the raw word `raw(π)`. -/
theorem trRawSum_eq_sum_take_c3RawWord (π : List (List ℤ × ℤ)) (i : ℕ) :
    trRawSum π i = ((c3RawWord π).take i).sum := by
  rw [trRawSum_eq_sum_take, c3RawWord_eq_flatMap]

/-- `σ_{i+1}(π) = σ_i(π) + z_{i+1}` for `i < M`, where `z = raw(π)`. -/
theorem trRawSum_succ_c3RawWord (π : List (List ℤ × ℤ)) {i : ℕ}
    (hi : i < (c3RawWord π).length) :
    trRawSum π (i + 1) = trRawSum π i + (c3RawWord π)[i] := by
  simp only [trRawSum_eq_sum_take_c3RawWord, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some, List.sum_append, List.sum_cons, List.sum_nil, add_zero]

/-- The raw partial sums of a live list are nondecreasing. -/
theorem trRawSum_le_of_le_of_trLive {π : List (List ℤ × ℤ)} (h : TrLive π) {i j : ℕ}
    (hij : i ≤ j) : trRawSum π i ≤ trRawSum π j := by
  rw [trRawSum_eq_sum_take_c3RawWord, trRawSum_eq_sum_take_c3RawWord]
  set z := c3RawWord π
  have hsplit : z.take j = z.take i ++ (z.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (z.take j)]
    rw [List.take_take, min_eq_left hij]
  rw [hsplit, List.sum_append]
  have : 0 ≤ ((z.take j).drop i).sum := List.sum_nonneg fun x hx ↦ by
    have := two_le_of_mem_c3RawWord h (List.mem_of_mem_take (List.mem_of_mem_drop hx))
    omega
  omega

/-- **First raw crossings partition the passage lists.** For `ω ∈ ℕ` and `π ∈ Π_ω` there is
exactly one triple `(c, o, r)` with `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1` and `π ∈ 𝒞_ω(c, o, r)`. -/
@[collatz_pos_dens "lem_c3_crossing_partition"]
theorem existsUnique_mem_c3CrossingSet {ω : ℕ} {π : List (List ℤ × ℤ)}
    (hπ : π ∈ trPassage ω) :
    ∃! t : ℤ × ℤ × ℕ, 2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2 ∧
      π ∈ c3CrossingSet ω t.1 t.2.1 t.2.2 := by
  have hlive := trLive_of_mem_trPassage hπ
  have hM := trRawSum_self π
  have hlen := length_c3RawWord π
  have hnn := chBlockPath_fst_nonneg π π.length
  have hexc : ∃ R, (ω : ℤ) < trRawSum π R :=
    ⟨_, hM ▸ lt_chBlockPath_snd_of_mem_trPassage hπ⟩
  classical
  obtain ⟨R, hR, hRmin, hRM⟩ : ∃ R, (ω : ℤ) < trRawSum π R ∧ (∀ m < R, trRawSum π m ≤ ω) ∧
      R ≤ (chBlockPath π π.length).1.toNat :=
    ⟨Nat.find hexc, Nat.find_spec hexc, fun m hm ↦ not_lt.mp (Nat.find_min hexc hm),
      Nat.find_min' hexc (hM ▸ lt_chBlockPath_snd_of_mem_trPassage hπ)⟩
  have hR1 : 1 ≤ R := by
    by_contra h0
    have : R = 0 := by omega
    rw [this, trRawSum_zero] at hR
    omega
  have hlt : R - 1 < (c3RawWord π).length := by omega
  have hstep := trRawSum_succ_c3RawWord π hlt
  rw [Nat.sub_add_cancel hR1] at hstep
  have hc2 := two_le_c3RawWord_getElem hlive hlt
  have hprev := hRmin (R - 1) (by omega)
  have key : ∀ t : ℤ × ℤ × ℕ, 2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2 ∧
      π ∈ c3CrossingSet ω t.1 t.2.1 t.2.2 →
      t = ((c3RawWord π)[R - 1], trRawSum π R - ω, R) := by
    rintro ⟨c', o', r'⟩ ⟨-, ho', hoc', hr', hmem⟩
    have hp := trRawSum_pred_of_mem_c3CrossingSet hmem
    have hs := trRawSum_of_mem_c3CrossingSet hmem
    simp only at hp hs ho' hoc' hr'
    have hrr : r' = R := by
      rcases lt_trichotomy r' R with h | h | h
      · have := hRmin r' h
        omega
      · exact h
      · have := trRawSum_le_of_le_of_trLive hlive (show R ≤ r' - 1 by omega)
        omega
    subst hrr
    simp only [Prod.mk.injEq, and_true]
    constructor <;> omega
  refine ⟨((c3RawWord π)[R - 1], trRawSum π R - ω, R),
    ⟨hc2, ?_, ?_, hR1, hπ, ?_, ?_, ?_⟩, key⟩ <;> dsimp only <;> omega

end CollatzPosDens
