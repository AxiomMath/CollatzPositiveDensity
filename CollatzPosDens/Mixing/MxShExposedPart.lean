/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShFairBits
public import CollatzPosDens.Mixing.MxShPatternBound
public import CollatzPosDens.Mixing.MxShSplitBij

/-!
# The exposed part of the offset

Let `N, d, q ∈ ℕ` with `q < N` and `d ≤ N`, let `Λ` be real with
`max(d, N - d)^q ≤ Λ 2^{-q} (N - q)^q`, and let `y ≥ 0` be real. Then among the `d`-subsets `S`
of `{1, …, N}`, those whose part `S ∩ {1, …, q}` below the cut has offset at least `y` number at
most
$$\frac{7\Lambda}{y + 2}\binom N d.$$

The proof groups the sets `S` by `β = S ∩ {1, …, q}`. Splitting at `q`
(`CollatzPosDens.bijOn_splitAt`), the `S` with a given `β` of size `b ≤ d` correspond to
`(d - b)`-subsets of `{1, …, N - q}`, so there are at most `C(N - q, d - b)` of them, and
`C(N - q, d - b) ≤ Λ 2^{-q} C(N, d)` by `CollatzPosDens.choose_sub_mul_pow_le_choose_mul_pow`
and the hypothesis. Summing over the `β` with `Of(β) ≥ y` and applying the offset tail of fair
bits `CollatzPosDens.card_setOffset_ge_le` gives the bound.

## Main results

* `CollatzPosDens.card_setOffset_inter_Icc_ge_le`: the bound above.

## Implementation notes

No hypothesis `0 ≤ Λ` is imposed: it follows from the hypothesis on `Λ`, since `q < N`.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- The `d`-subsets of `{1, …, N}` with a prescribed part `β` below the cut `q`, with `b = |β|`,
number at most `C(N - q, d - b)`, and none exist unless `b ≤ d`. -/
private theorem card_filter_inter_Icc_eq_le {N d q : ℕ} (hqN : q ≤ N) (β : Finset ℕ)
    (s : Finset (Finset ℕ)) (hs : s ⊆ powersetCard d (Icc 1 N)) :
    #{S ∈ s | S ∩ Icc 1 q = β} ≤ (N - q).choose (d - #β) := by
  have hbij := bijOn_splitAt d hqN (N := N)
  have hc : (N - q).choose (d - #β) = #(powersetCard (d - #β) (Icc 1 (N - q))) := by
    rw [card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hc]
  · refine card_le_card_of_injOn (fun S => (splitAt q S).2) ?_ ?_
    · intro S hS
      simp only [coe_filter, Set.mem_ofPred_eq] at hS
      have hS' : S ∈ (powersetCard d (Icc 1 N) : Set (Finset ℕ)) := hs hS.1
      obtain ⟨-, h2, h3⟩ := hbij.mapsTo hS'
      simp only [splitAt_fst, hS.2] at h3
      rw [mem_coe, mem_powersetCard]
      refine ⟨h2, ?_⟩
      change #(splitAt q S).2 = d - #β
      omega
    · intro S hS S' hS' h
      simp only [coe_filter, Set.mem_ofPred_eq] at hS hS'
      refine hbij.injOn (hs hS.1) (hs hS'.1) (Prod.ext ?_ h)
      simp only [splitAt_fst, hS.2, hS'.2]

/-- **The exposed part of the offset.** Let `q < N`, `d ≤ N`, and `Λ` real with
`max(d, N - d)^q ≤ Λ 2^{-q} (N - q)^q`, and let `y ≥ 0`. Then the number of `d`-subsets `S` of
`{1, …, N}` with `Of(S ∩ {1, …, q}) ≥ y` is at most `7 Λ / (y + 2) · C(N, d)`. -/
@[collatz_pos_dens "lem_mx_sh_exposed_part"]
theorem card_setOffset_inter_Icc_ge_le {N d q : ℕ} {Λ y : ℝ} (hqN : q < N) (hdN : d ≤ N)
    (hΛ : ((max d (N - d) : ℕ) : ℝ) ^ q ≤ Λ * (2 : ℝ)⁻¹ ^ q * ((N - q : ℕ) : ℝ) ^ q)
    (hy : 0 ≤ y) :
    (#{S ∈ powersetCard d (Icc 1 N) | y ≤ (setOffset (S ∩ Icc 1 q) : ℝ)} : ℝ) ≤
      7 * Λ / (y + 2) * N.choose d := by
  set s := {S ∈ powersetCard d (Icc 1 N) | y ≤ (setOffset (S ∩ Icc 1 q) : ℝ)} with hs_def
  set F := {β ∈ (Icc 1 q).powerset | y ≤ (setOffset β : ℝ)} with hF
  have hNq : (0 : ℝ) < ((N - q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - q)
  have hNqq : (0 : ℝ) < ((N - q : ℕ) : ℝ) ^ q := pow_pos hNq q
  have h2q : (0 : ℝ) < (2 : ℝ)⁻¹ ^ q := by positivity
  have hΛ0 : 0 ≤ Λ := by
    by_contra h
    have : Λ * (2 : ℝ)⁻¹ ^ q * ((N - q : ℕ) : ℝ) ^ q < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (not_le.1 h) h2q) hNqq
    have h0 : (0 : ℝ) ≤ ((max d (N - d) : ℕ) : ℝ) ^ q := by positivity
    linarith
  have hC : (0 : ℝ) ≤ N.choose d := Nat.cast_nonneg _
  -- each fibre has at most `Λ 2^{-q} C(N, d)` elements
  have hfib : ∀ β ∈ F, (#{S ∈ s | S ∩ Icc 1 q = β} : ℝ) ≤ Λ * (2 : ℝ)⁻¹ ^ q * N.choose d := by
    intro β hβ
    have hβq : β ⊆ Icc 1 q := mem_powerset.1 (mem_filter.1 hβ).1
    rcases (filter (fun S => S ∩ Icc 1 q = β) s).eq_empty_or_nonempty with he | ⟨S, hS⟩
    · rw [he, card_empty, Nat.cast_zero]
      positivity
    have hS := mem_filter.1 hS
    have hSd := mem_powersetCard.1 (mem_filter.1 hS.1).1
    have hbd : #β ≤ d := hSd.2 ▸ hS.2 ▸ card_le_card inter_subset_left
    have hbq : #β ≤ q := by simpa using card_le_card hβq
    have hcard := card_filter_inter_Icc_eq_le hqN.le β s (filter_subset _ _)
    have hpat := choose_sub_mul_pow_le_choose_mul_pow (M := ((max d (N - d) : ℕ) : ℝ)) hqN hdN
      hbq hbd (by exact_mod_cast le_max_left _ _) (by exact_mod_cast le_max_right _ _)
    have key : ((N - q).choose (d - #β) : ℝ) * ((N - q : ℕ) : ℝ) ^ q ≤
        Λ * (2 : ℝ)⁻¹ ^ q * N.choose d * ((N - q : ℕ) : ℝ) ^ q := by
      calc _ ≤ (N.choose d : ℝ) * ((max d (N - d) : ℕ) : ℝ) ^ q := hpat
        _ ≤ (N.choose d : ℝ) * (Λ * (2 : ℝ)⁻¹ ^ q * ((N - q : ℕ) : ℝ) ^ q) := by gcongr
        _ = _ := by ring
    exact (Nat.cast_le.2 hcard).trans (le_of_mul_le_mul_right key hNqq)
  -- sum over the fibres
  have hmaps : ∀ S ∈ s, S ∩ Icc 1 q ∈ F := by
    intro S hS
    exact mem_filter.2 ⟨mem_powerset.2 inter_subset_right, (mem_filter.1 hS).2⟩
  have hfair := card_setOffset_ge_le q hy
  rw [← hF] at hfair
  calc (#s : ℝ) = ∑ β ∈ F, (#{S ∈ s | S ∩ Icc 1 q = β} : ℝ) := by
        exact_mod_cast card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _β ∈ F, Λ * (2 : ℝ)⁻¹ ^ q * N.choose d := sum_le_sum hfib
    _ = Λ * N.choose d * ((2 : ℝ)⁻¹ ^ q * #F) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ Λ * N.choose d * (7 / (y + 2)) := by gcongr
    _ = 7 * Λ / (y + 2) * N.choose d := by ring

end CollatzPosDens
