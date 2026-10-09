/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcSurvivorCount

/-!
# Recursion for surviving prefix counts

Let `H_{b,r_b}` be the barrier `barrier b (rb b)`, which constrains prefixes of length at least
`ℓ_b = lb b`. Past `ℓ_b`, the surviving prefix counts `c_{b,i}(s)` (`fcSurvivorCount`) obey a
simple recursion in the length `i`. A word `x ∈ ℤ_{≥1}^i` is uniquely `x = p (a)` with
`p = x_{≤ i-1}` and a last letter `a ≥ 1`. When `i > ℓ_b`, the barrier conditions on `x` are those
on `p` at length `i - 1` together with `A(x) < H_{b,r_b}(i)`. Hence for `s < H_{b,r_b}(i)` the
surviving words of sum `s` are in bijection with the pairs `(p, s - t)` where `p` is a surviving
word of length `i - 1` and sum `0 ≤ t < s`, and for `s ≥ H_{b,r_b}(i)` there are none:
`c_{b,i}(s) = ∑_{t=0}^{s-1} c_{b,i-1}(t)` if `s < H_{b,r_b}(i)`, and `c_{b,i}(s) = 0` otherwise.

## Main results

* `CollatzPosDens.fcSurvivorCount_step`: the recursion for `c_{b,i}(s)`, `i > ℓ_b`.
* `CollatzPosDens.fcSurvivorCount_succ`: the same recursion indexed as `i + 1` with `i ≥ ℓ_b`.
* `CollatzPosDens.fcSurvivorCount_step_of_barrier_le`: `c_{b,i}(s) = 0` once
  `s ≥ H_{b,r_b}(i)`, for `i ≥ ℓ_b`.

## Implementation notes

The source assumes `b ≥ 1`; the recursion holds for every natural number `b`, so that hypothesis
is dropped. The sum `∑_{t=0}^{s-1}` over integers is `∑ t ∈ Finset.Ico 0 s`, which is empty when
`s ≤ 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open CollatzPosDens

/-- A surviving word of length `i + 1 > ℓ_b` is `p (a)` with `p` surviving at length `i`, and its
sum lies below the barrier. -/
private theorem append_mem_fcSurvivorSet_succ_iff {b i : ℕ} (hi : lb b ≤ i) (p : Word) (a : ℕ+)
    (s : ℤ) :
    p ++ [a] ∈ fcSurvivorSet b (i + 1) s ↔
      p ∈ fcSurvivorSet b i (s - a) ∧ s < barrier b (rb b) (i + 1) := by
  simp only [mem_fcSurvivorSet, List.length_append, List.length_singleton, Nat.add_right_cancel_iff,
    Word.valSum_append, Word.valSum_singleton]
  constructor
  · rintro ⟨hlen, hsum, hj⟩
    refine ⟨⟨hlen, by push_cast at hsum; omega, fun j hj1 hj2 => ?_⟩, ?_⟩
    · have := hj j hj1 (by omega)
      rwa [List.take_append_of_le_length (by omega)] at this
    · have := hj (i + 1) (by omega) le_rfl
      rw [List.take_of_length_le (by simp [hlen]), Word.valSum_append,
        Word.valSum_singleton] at this
      push_cast at this hsum
      omega
  · rintro ⟨⟨hlen, hsum, hj⟩, hs⟩
    refine ⟨hlen, by push_cast; omega, fun j hj1 hj2 => ?_⟩
    rcases Nat.lt_or_ge j (i + 1) with h | h
    · rw [List.take_append_of_le_length (by omega)]
      exact hj j hj1 (by omega)
    · rw [List.take_of_length_le (by simpa [hlen] using h), Word.valSum_append,
        Word.valSum_singleton]
      obtain rfl : j = i + 1 := by omega
      push_cast
      omega

/-- A word of positive length is its `dropLast` followed by its last letter. -/
private theorem fcSurvivorCount_step_decomp {x : Word} {n : ℕ} (h : x.length = n + 1) :
    ∃ a : ℕ+, x = x.dropLast ++ [a] :=
  have hx : x ≠ [] := List.ne_nil_of_length_pos (by omega)
  ⟨x.getLast hx, (List.dropLast_append_getLast hx).symm⟩

/-- For `i ≥ ℓ_b` and `s ≥ H_{b,r_b}(i)`, no word survives: `c_{b,i}(s) = 0`. -/
theorem fcSurvivorCount_step_of_barrier_le {b i : ℕ} (hi : lb b ≤ i) {s : ℤ}
    (hs : barrier b (rb b) i ≤ s) : fcSurvivorCount b i s = 0 := by
  rw [fcSurvivorCount_def, Set.ncard_eq_zero (fcSurvivorSet_finite b i s)]
  ext x
  simp only [mem_fcSurvivorSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hlen hsum hj
  have := hj i hi le_rfl
  rw [List.take_of_length_le (by omega)] at this
  omega

/-- For `0 ≤ t < s < H_{b,r_b}(i + 1)`, dropping the last letter is a bijection from the
surviving words of length `i + 1` and sum `s` whose prefix has sum `t` onto those of length `i`
and sum `t`. -/
private theorem card_filter_valSum_dropLast_eq {b i : ℕ} (hi : lb b ≤ i) {s t : ℤ}
    (hs : s < barrier b (rb b) (i + 1)) (ht : 0 ≤ t ∧ t < s) :
    ((fcSurvivorSet_finite b (i + 1) s).toFinset.filter
        fun x => (Word.valSum x.dropLast : ℤ) = t).card =
      (fcSurvivorSet_finite b i t).toFinset.card := by
  have hst : ((Nat.toPNat' (s - t).toNat : ℕ+) : ℤ) = s - t := by
    rw [Nat.toPNat'_coe, ite_eq_left (by omega)]
    omega
  refine Finset.card_nbij' List.dropLast (fun p => p ++ [Nat.toPNat' (s - t).toNat])
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hx
    simp only [Set.Finite.coe_toFinset]
    obtain ⟨hx, hxt⟩ := hx
    obtain ⟨a, ha⟩ := fcSurvivorCount_step_decomp hx.1
    rw [ha, append_mem_fcSurvivorSet_succ_iff hi] at hx
    have h1 := hx.1.2.1
    rw [show s - a = t by omega] at hx
    exact hx.1
  · intro p hp
    simp only [Set.Finite.coe_toFinset] at hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset,
      List.dropLast_concat]
    refine ⟨(append_mem_fcSurvivorSet_succ_iff hi _ _ _).2 ⟨?_, hs⟩, hp.2.1⟩
    rwa [hst, show s - (s - t) = t by ring]
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hx
    obtain ⟨hx, hxt⟩ := hx
    obtain ⟨a, ha⟩ := fcSurvivorCount_step_decomp hx.1
    have hsum := hx.2.1
    rw [ha, Word.valSum_append, Word.valSum_singleton] at hsum
    rw [ha, List.dropLast_concat] at hxt ⊢
    have : ((a : ℕ) : ℤ) = s - t := by push_cast at hsum; omega
    have hpa : Nat.toPNat' (s - t).toNat = a :=
      PNat.coe_injective (by exact_mod_cast hst.trans this.symm)
    rw [hpa]
  · intro p _
    simp

/-- The recursion for the surviving prefix counts at length `i + 1 > ℓ_b`. -/
theorem fcSurvivorCount_succ {b i : ℕ} (hi : lb b ≤ i) (s : ℤ) :
    fcSurvivorCount b (i + 1) s =
      if s < barrier b (rb b) (i + 1) then ∑ t ∈ Finset.Ico 0 s, fcSurvivorCount b i t
      else 0 := by
  split_ifs with hs
  swap
  · exact fcSurvivorCount_step_of_barrier_le (by omega) (by omega)
  rw [fcSurvivorCount_def, Set.ncard_eq_toFinset_card _ (fcSurvivorSet_finite b (i + 1) s)]
  have hmaps : ∀ x ∈ (fcSurvivorSet_finite b (i + 1) s).toFinset,
      (Word.valSum x.dropLast : ℤ) ∈ Finset.Ico 0 s := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨a, ha⟩ := fcSurvivorCount_step_decomp hx.1
    rw [ha, append_mem_fcSurvivorSet_succ_iff hi] at hx
    have h1 := hx.1.2.1
    have h2 := a.pos
    simp only [Finset.mem_Ico]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [fcSurvivorCount_def, Set.ncard_eq_toFinset_card _ (fcSurvivorSet_finite b i t)]
  exact card_filter_valSum_dropLast_eq hi hs (Finset.mem_Ico.1 ht)

/-- **Recursion for surviving counts.** For `i > ℓ_b` and every integer `s`,
`c_{b,i}(s) = ∑_{t=0}^{s-1} c_{b,i-1}(t)` if `s < H_{b,r_b}(i)`, and `c_{b,i}(s) = 0` otherwise. -/
@[collatz_pos_dens "lem_fc_count_step"]
theorem fcSurvivorCount_step {b i : ℕ} (hi : lb b < i) (s : ℤ) :
    fcSurvivorCount b i s =
      if s < barrier b (rb b) i then ∑ t ∈ Finset.Ico 0 s, fcSurvivorCount b (i - 1) t
      else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact fcSurvivorCount_succ (by omega) s

end CollatzPosDens
