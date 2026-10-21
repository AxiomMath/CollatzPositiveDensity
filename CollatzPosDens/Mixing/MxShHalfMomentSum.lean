/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShHypergeomPgf
public import CollatzPosDens.Mixing.MxShSubsetOffset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.BigOperators

/-!
# The half moment of the offset over `d`-subsets

For integers `N ≥ 2` and `1 ≤ d ≤ N` we bound the sum of `√Of(S)` over the `d`-subsets `S` of
`{1, …, N}`, where `Of(S) = ∑_{s ∈ S} 3^{c_S(s)} 2^{-s}` with `c_S(s) = #{t ∈ S : t < s}` is the
offset `CollatzPosDens.setOffset`:
$$\sum_{S \subseteq \{1, \dots, N\},\ |S| = d} \sqrt{\operatorname{Of}(S)}
  \le \binom{N-1}{d-1} \frac1{\sqrt2} \sum_{i=0}^{N-1}
  \Bigl(\frac{1 + (\sqrt3 - 1)\frac{d-1}{N-1}}{\sqrt2}\Bigr)^i.$$

Since `√(∑ xᵢ) ≤ ∑ √xᵢ` for nonnegative reals, `√Of(S) ≤ ∑_{s ∈ S} (√3)^{c_S(s)} 2^{-s/2}`.
Exchanging the sums, it remains to bound, for each position `s`, the sum of `(√3)^{c_S(s)}` over
the `d`-subsets `S ∋ s`. Removing `s` and closing the gap it leaves (the increasing bijection
`{1, …, N} \ {s} → {1, …, N - 1}`) identifies these subsets with the `(d - 1)`-subsets `X` of
`{1, …, N - 1}`, with `c_S(s) = |X ∩ {1, …, s - 1}|`; the factorial-moment bound
`CollatzPosDens.sum_powersetCard_Icc_pow_card_inter_le` then bounds the inner sum by
`binom (N - 1) (d - 1) γ^{s - 1}` with `γ = 1 + (√3 - 1)(d - 1)/(N - 1)`.

## Main results

* `CollatzPosDens.sqrt_sum_le_sum_sqrt`: `√(∑ xᵢ) ≤ ∑ √xᵢ` for nonnegative reals.
* `CollatzPosDens.sqrt_setOffset_le`: `√Of(S) ≤ ∑_{s ∈ S} (√3)^{c_S(s)} (1/√2)^s`.
* `CollatzPosDens.sum_powersetCard_filter_mem_eq`: the `d`-subsets of `{1, …, N}` containing `s`
  correspond to the `(d - 1)`-subsets of `{1, …, N - 1}`, with `c_S(s) = |X ∩ {1, …, s - 1}|`.
* `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le'`: the bound for all `N` and `d`, with natural
  subtraction in `d - 1` and `N - 1`.
* `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le`: the bound for `N ≥ 1` and `d ≥ 1`, with
  real subtraction.

## Implementation notes

The general form `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le'` needs no hypothesis: with
natural subtraction it also holds for `d = 0` (the left-hand side is `√Of(∅) = 0`) and for `N ≤ 1`
(where `(d - 1)/(N - 1)` is read as `0`). The bound is usually stated for `N ≥ 2` and
`1 ≤ d ≤ N`; `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le` keeps real subtraction and needs
only `N ≥ 1` and `d ≥ 1`, the hypotheses under which the two subtractions agree.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- The square root of a finite sum of nonnegative reals is at most the sum of the square roots. -/
theorem sqrt_sum_le_sum_sqrt {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    √(∑ i ∈ s, f i) ≤ ∑ i ∈ s, √(f i) := by
  rw [Real.sqrt_le_left (sum_nonneg fun i _ => Real.sqrt_nonneg _)]
  calc ∑ i ∈ s, f i = ∑ i ∈ s, √(f i) ^ 2 :=
        sum_congr rfl fun i hi => (Real.sq_sqrt (hf i hi)).symm
    _ ≤ (∑ i ∈ s, √(f i)) ^ 2 :=
        sum_sq_le_sq_sum_of_nonneg fun i _ => Real.sqrt_nonneg _

/-- The square root of the offset is at most `∑_{s ∈ S} (√3)^{#{t ∈ S : t < s}} (1/√2)^s`. -/
theorem sqrt_setOffset_le (S : Finset ℕ) :
    √(setOffset S : ℝ) ≤ ∑ s ∈ S, √3 ^ #(S.filter (· < s)) * (√2)⁻¹ ^ s := by
  have hcast : (setOffset S : ℝ) = ∑ s ∈ S, (3 : ℝ) ^ #(S.filter (· < s)) * ((2 : ℝ) ^ s)⁻¹ := by
    simp only [setOffset, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
  rw [hcast]
  refine (sqrt_sum_le_sum_sqrt S fun s _ => by positivity).trans_eq (sum_congr rfl fun s _ => ?_)
  rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_inv, inv_pow]
  congr 1
  · rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by norm_num)]
  · congr 1
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by norm_num)]

/-- **Removing a position.** For `1 ≤ s ≤ N` and `1 ≤ d`, the `d`-subsets `S` of `{1, …, N}`
containing `s` correspond to the `(d - 1)`-subsets `X` of `{1, …, N - 1}` (remove `s` and shift the
elements above `s` down by one), and `#{t ∈ S : t < s} = |X ∩ {1, …, s - 1}|`. -/
theorem sum_powersetCard_filter_mem_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) {N d s : ℕ}
    (hs : s ∈ Icc 1 N) (hd : 1 ≤ d) :
    ∑ S ∈ (Icc 1 N).powersetCard d with s ∈ S, f #(S.filter (· < s)) =
      ∑ X ∈ (Icc 1 (N - 1)).powersetCard (d - 1), f #(X ∩ Icc 1 (s - 1)) := by
  rw [mem_Icc] at hs
  set φ : ℕ → ℕ := fun t => if t < s then t else t - 1 with hφ
  set ψ : ℕ → ℕ := fun t => if t < s then t else t + 1 with hψ
  have hφψ (t : ℕ) : φ (ψ t) = t := by
    simp only [hφ, hψ]; split_ifs <;> omega
  have hψφ (t : ℕ) (ht : t ≠ s) : ψ (φ t) = t := by
    simp only [hφ, hψ]; split_ifs <;> omega
  have hψs (t : ℕ) : ψ t ≠ s := by
    simp only [hψ]; split_ifs <;> omega
  have hsψ (X : Finset ℕ) : s ∉ X.image ψ := by
    simp only [mem_image, not_exists, not_and]
    exact fun t _ => hψs t
  refine sum_nbij' (fun S => (S.erase s).image φ) (fun X => insert s (X.image ψ)) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSN, hSd⟩, hsS⟩ := hS
    rw [mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
      obtain ⟨hts, htS⟩ := mem_erase.1 ht
      have := mem_Icc.1 (hSN htS)
      rw [mem_Icc]
      simp only [hφ]
      split_ifs <;> omega
    · rw [card_image_of_injOn, card_erase_of_mem hsS, hSd]
      intro t ht t' ht' htt'
      have h1 := (mem_erase.1 (mem_coe.1 ht)).1
      have h2 := (mem_erase.1 (mem_coe.1 ht')).1
      simp only [hφ] at htt'
      split_ifs at htt' <;> omega
  · intro X hX
    rw [mem_powersetCard] at hX
    obtain ⟨hXN, hXd⟩ := hX
    simp only [mem_filter, mem_powersetCard, mem_insert_self, and_true]
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases mem_insert.1 hx with rfl | hx
      · exact mem_Icc.2 hs
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
        have := mem_Icc.1 (hXN ht)
        rw [mem_Icc]
        simp only [hψ]
        split_ifs <;> omega
    · rw [card_insert_of_notMem (hsψ X), card_image_of_injective _ ?_, hXd]
      · omega
      · intro t t' htt'
        simpa [hφψ] using congrArg φ htt'
  · intro S hS
    have hsS : s ∈ S := (mem_filter.1 hS).2
    rw [image_image, image_congr (f := ψ ∘ φ) (g := id) (fun t ht => hψφ t (mem_erase.1 ht).1),
      image_id, insert_erase hsS]
  · intro X _
    rw [erase_insert (hsψ X), image_image]
    simp [Function.comp_def, hφψ]
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSN, -⟩, -⟩ := hS
    congr 2
    ext x
    simp only [mem_filter, mem_inter, mem_image, mem_erase, mem_Icc]
    constructor
    · rintro ⟨hxS, hxs⟩
      have := mem_Icc.1 (hSN hxS)
      refine ⟨⟨x, ⟨by omega, hxS⟩, by simp [hφ, hxs]⟩, by omega, by omega⟩
    · rintro ⟨⟨t, ⟨hts, htS⟩, rfl⟩, h1, h2⟩
      by_cases h : t < s
      · simpa [hφ, h] using htS
      · simp only [hφ, h, ↓reduceIte] at h2
        omega

/-- **Half moment of the offset, general form.** For all natural numbers `N` and `d`, with
natural subtraction in `d - 1` and `N - 1`,
`∑_{S ⊆ {1, …, N}, |S| = d} √Of(S) ≤ binom (N - 1) (d - 1) (1/√2) ∑_{i < N} (γ/√2)^i` where
`γ = 1 + (√3 - 1)(d - 1)/(N - 1)`. -/
theorem sum_powersetCard_sqrt_setOffset_le' (N d : ℕ) :
    ∑ S ∈ (Icc 1 N).powersetCard d, √(setOffset S : ℝ) ≤
      (N - 1).choose (d - 1) * (1 / √2) *
        ∑ i ∈ range N,
          ((1 + (√3 - 1) * (((d - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ))) / √2) ^ i := by
  set γ : ℝ := 1 + (√3 - 1) * (((d - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) with hγ
  set C : ℝ := ((N - 1).choose (d - 1) : ℝ) with hC
  have h3 : (1 : ℝ) ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hγ0 : 0 ≤ γ := by
    have : (0 : ℝ) ≤ (√3 - 1) * (((d - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  have hinner (s : ℕ) (hs : s ∈ Icc 1 N) :
      ∑ S ∈ (Icc 1 N).powersetCard d with s ∈ S, √3 ^ #(S.filter (· < s)) ≤ C * γ ^ (s - 1) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : ((Icc 1 N).powersetCard 0).filter (s ∈ ·) = ∅ := by
        refine filter_eq_empty_iff.2 fun S hS => ?_
        rw [powersetCard_zero, mem_singleton] at hS
        simp [hS]
      rw [this, sum_empty]
      positivity
    · rw [sum_powersetCard_filter_mem_eq (fun c => √3 ^ c) hs hd, hγ, ← mul_div_assoc]
      exact sum_powersetCard_Icc_pow_card_inter_le (N - 1) (d - 1) (s - 1) h3
  calc ∑ S ∈ (Icc 1 N).powersetCard d, √(setOffset S : ℝ)
      ≤ ∑ S ∈ (Icc 1 N).powersetCard d, ∑ s ∈ S, √3 ^ #(S.filter (· < s)) * (√2)⁻¹ ^ s :=
        sum_le_sum fun S _ => sqrt_setOffset_le S
    _ = ∑ s ∈ Icc 1 N, (√2)⁻¹ ^ s *
          ∑ S ∈ (Icc 1 N).powersetCard d with s ∈ S, √3 ^ #(S.filter (· < s)) := by
        rw [sum_comm' (t' := Icc 1 N) (s' := fun s => ((Icc 1 N).powersetCard d).filter (s ∈ ·))]
        · refine sum_congr rfl fun s _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun S _ => mul_comm _ _
        · intro S s
          simp only [mem_filter, mem_powersetCard]
          constructor
          · rintro ⟨⟨hSN, hSd⟩, hsS⟩
            exact ⟨⟨⟨hSN, hSd⟩, hsS⟩, hSN hsS⟩
          · rintro ⟨⟨⟨hSN, hSd⟩, hsS⟩, -⟩
            exact ⟨⟨hSN, hSd⟩, hsS⟩
    _ ≤ ∑ s ∈ Icc 1 N, (√2)⁻¹ ^ s * (C * γ ^ (s - 1)) :=
        sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hinner s hs) (by positivity)
    _ = C * (1 / √2) * ∑ i ∈ range N, (γ / √2) ^ i := by
        rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Nat.add_sub_cancel_left, add_comm, pow_succ, div_pow]
        ring

/-- **Half moment of the offset over `d`-subsets.** For integers `N ≥ 1` and `d ≥ 1` (in
particular for `N ≥ 2` and `1 ≤ d ≤ N`),
$$\sum_{S \subseteq \{1, \dots, N\},\ |S| = d} \sqrt{\operatorname{Of}(S)}
  \le \binom{N-1}{d-1} \frac1{\sqrt2} \sum_{i=0}^{N-1}
  \Bigl(\frac{1 + (\sqrt3 - 1)\frac{d-1}{N-1}}{\sqrt2}\Bigr)^i.$$ -/
@[collatz_pos_dens "lem_mx_sh_half_moment_sum"]
theorem sum_powersetCard_sqrt_setOffset_le {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    ∑ S ∈ (Icc 1 N).powersetCard d, √(setOffset S : ℝ) ≤
      (N - 1).choose (d - 1) * (1 / √2) *
        ∑ i ∈ range N, ((1 + (√3 - 1) * (((d : ℝ) - 1) / ((N : ℝ) - 1))) / √2) ^ i := by
  have h := sum_powersetCard_sqrt_setOffset_le' N d
  rwa [Nat.cast_sub hd, Nat.cast_sub hN, Nat.cast_one] at h

end CollatzPosDens
