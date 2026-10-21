/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import CollatzPosDens.Mixing.MxShSubsetOffset

/-!
# Splitting the offset of a set at a position

For a finite set `S` of positions and `q ∈ ℕ`, write `S_e = {s ∈ S : s ≤ q}`, `b = |S_e|` and
`T = {s - q : s ∈ S, s > q}`. Splitting the sum defining the offset `Of(S)` into the terms with
`s ≤ q` and those with `s > q` gives
$$\operatorname{Of}(S) = \operatorname{Of}(S_e) + 3^{b}\, 2^{-q}\, \operatorname{Of}(T).$$
Indeed for `s ≤ q` the elements of `S` below `s` are those of `S_e` below `s`, while for `s > q`
they are the `b` elements of `S_e` together with the `t ∈ S` with `q < t < s`, whose images
`t - q` are exactly the elements of `T` below `s - q`; and `2^{-s} = 2^{-q} 2^{-(s-q)}`.

## Main results

* `CollatzPosDens.setOffset_eq_add`: the splitting identity, with `S_e = S.filter (· ≤ q)`.
* `CollatzPosDens.setOffset_eq_add_of_one_le`: the same identity with `S_e = S ∩ {1, …, q}`,
  for `S ⊆ ℤ_{≥1}`.

## Implementation notes

The identity holds for every finite `S ⊆ ℕ` once `S ∩ {1, …, q}` is read as `{s ∈ S : s ≤ q}`;
for `S ⊆ ℤ_{≥1}` the two sets coincide.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

/-- Splitting the offset at `q`:
`Of(S) = Of(S_e) + 3^{|S_e|} 2^{-q} Of({s - q : s ∈ S, s > q})` with `S_e = {s ∈ S : s ≤ q}`. -/
@[collatz_pos_dens "lem_mx_sh_split_offset"]
theorem setOffset_eq_add (S : Finset ℕ) (q : ℕ) :
    setOffset S = setOffset (S.filter (· ≤ q)) +
      (3 : ℚ) ^ (S.filter (· ≤ q)).card * ((2 : ℚ) ^ q)⁻¹ *
        setOffset ((S.filter (q < ·)).image (· - q)) := by
  unfold setOffset
  rw [← Finset.sum_filter_add_sum_filter_not S (· ≤ q)]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    have hsq : s ≤ q := (Finset.mem_filter.1 hs).2
    congr 3
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hts⟩
      exact ⟨⟨ht, by omega⟩, hts⟩
    · rintro ⟨⟨ht, _⟩, hts⟩
      exact ⟨ht, hts⟩
  · have hinj : Set.InjOn (· - q) ((S.filter (q < ·)) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      omega
    rw [Finset.sum_image hinj, Finset.mul_sum]
    have hfilt : S.filter (fun s => ¬ s ≤ q) = S.filter (q < ·) :=
      Finset.filter_congr fun s _ => not_le
    rw [hfilt]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hqs : q < s := (Finset.mem_filter.1 hs).2
    have hsplit : S.filter (· < s) =
        S.filter (· ≤ q) ∪ (S.filter (fun t => q < t ∧ t < s)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨ht, hts⟩
        by_cases htq : t ≤ q
        · exact Or.inl ⟨ht, htq⟩
        · exact Or.inr ⟨ht, by omega, hts⟩
      · rintro (⟨ht, htq⟩ | ⟨ht, _, hts⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨ht, hts⟩
    have hdisj : Disjoint (S.filter (· ≤ q)) (S.filter (fun t => q < t ∧ t < s)) := by
      rw [Finset.disjoint_filter]
      intro t _ htq h
      omega
    have himage : ((S.filter (q < ·)).image (· - q)).filter (· < s - q) =
        (S.filter (fun t => q < t ∧ t < s)).image (· - q) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨t, ⟨ht, htq⟩, rfl⟩, hu⟩
        exact ⟨t, ⟨ht, htq, by omega⟩, rfl⟩
      · rintro ⟨t, ⟨ht, htq, hts⟩, rfl⟩
        exact ⟨⟨t, ⟨ht, htq⟩, rfl⟩, by omega⟩
    have hinj' : Set.InjOn (· - q) ((S.filter (fun t => q < t ∧ t < s)) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, himage, Finset.card_image_of_injOn hinj',
      pow_add]
    have hpow : (2 : ℚ) ^ s = 2 ^ q * 2 ^ (s - q) := by
      rw [← pow_add, Nat.add_sub_cancel' hqs.le]
    rw [hpow, mul_inv]
    ring

/-- Splitting the offset at `q` for `S ⊆ ℤ_{≥1}`:
`Of(S) = Of(S ∩ {1,…,q}) + 3^{|S ∩ {1,…,q}|} 2^{-q} Of({s - q : s ∈ S, s > q})`. -/
theorem setOffset_eq_add_of_one_le {S : Finset ℕ} (hS : ∀ s ∈ S, 1 ≤ s) (q : ℕ) :
    setOffset S = setOffset (S ∩ Finset.Icc 1 q) +
      (3 : ℚ) ^ (S ∩ Finset.Icc 1 q).card * ((2 : ℚ) ^ q)⁻¹ *
        setOffset ((S.filter (q < ·)).image (· - q)) := by
  have h : S ∩ Finset.Icc 1 q = S.filter (· ≤ q) := by
    ext s
    simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨hs, _, hsq⟩
      exact ⟨hs, hsq⟩
    · rintro ⟨hs, hsq⟩
      exact ⟨hs, hS s hs, hsq⟩
  rw [h]
  exact setOffset_eq_add S q

end CollatzPosDens
