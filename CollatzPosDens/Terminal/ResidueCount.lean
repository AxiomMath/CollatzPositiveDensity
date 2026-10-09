/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.CardIntervalMod
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# Counting residues on a dyadic-scale interval

Let `k ≥ 0`, let `X ≥ 3^k` be real, let `δ ≥ 0` be a function on `G_k = ℤ/3^kℤ` and let `σ` be a
permutation of `G_k`, and write `⟨δ⟩_k = 3^{-k} ∑_y δ y` for the average
`CollatzPosDens.residueAvg k δ`. Each residue class modulo `3^k` meets the integers of `[X, 32X)`
in at most `31X/3^k + 1 ≤ 32X/3^k` points, so summing `δ(σ(x mod 3^k))` over those integers gives
at most `(32X/3^k) ∑_y δ(σ y) = 32X⟨δ⟩_k ≤ 33X⟨δ⟩_k`.

## Main results

* `CollatzPosDens.card_filter_residue_mul_le`: a residue class modulo `3^k` contains at most
  `32X/3^k` integers of `[X, 32X)`.
* `CollatzPosDens.sum_residue_perm_le`: the residue-count bound
  `∑_{x ∈ ℤ ∩ [X, 32X)} δ(σ(x mod 3^k)) ≤ 33X⟨δ⟩_k`.

## Implementation notes

The integers of the real interval `[X, 32X)` are written as `Finset.Ico ⌈X⌉ ⌈32 * X⌉`, which has
exactly these elements since `⌈X⌉ ≤ x ↔ X ≤ x` and `x < ⌈32X⌉ ↔ x < 32X` for integers `x`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §18.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `X ≥ 3^k`, a residue class modulo `3^k` contains at most `32X/3^k` integers of the real
interval `[X, 32X)`. -/
theorem card_filter_residue_mul_le (k : ℕ) {X : ℝ} (hX : (3 : ℝ) ^ k ≤ X)
    (y : ResidueGroup k) :
    (#{x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | ((x : ℤ) : ResidueGroup k) = y} : ℝ) * 3 ^ k ≤ 32 * X := by
  have hr : (0 : ℤ) < 3 ^ k := by positivity
  have hfil : {x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | ((x : ℤ) : ResidueGroup k) = y} =
      {x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | x ≡ (y.val : ℤ) [ZMOD (3 ^ k : ℕ)]} := by
    refine Finset.filter_congr fun x _ => ?_
    rw [← ZMod.intCast_eq_intCast_iff]
    simp
  have h := Int.Ico_filter_modEq_card ⌈X⌉ ⌈32 * X⌉ (r := ((3 ^ k : ℕ) : ℤ))
    (by exact_mod_cast hr) (y.val : ℤ)
  rw [hfil]
  set n := #{x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | x ≡ (y.val : ℤ) [ZMOD (3 ^ k : ℕ)]}
  set p := ⌈((⌈X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ k : ℕ) : ℤ)⌉
  set q := ⌈((⌈32 * X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ k : ℕ) : ℤ)⌉
  have hrq : (0 : ℚ) < ((3 ^ k : ℕ) : ℤ) := by positivity
  have hp : ((⌈X⌉ : ℤ) : ℚ) ≤ p * ((3 ^ k : ℕ) : ℤ) + (y.val : ℤ) := by
    have := Int.le_ceil (((⌈X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ k : ℕ) : ℤ))
    rw [div_le_iff₀ hrq] at this
    linarith
  have hq : (q - 1 : ℚ) * ((3 ^ k : ℕ) : ℤ) + (y.val : ℤ) < ((⌈32 * X⌉ : ℤ) : ℚ) := by
    have := Int.ceil_lt_add_one (((⌈32 * X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ k : ℕ) : ℤ))
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hrq] at this
    linarith
  have hp' : ⌈X⌉ ≤ p * (3 ^ k : ℕ) + (y.val : ℤ) := by exact_mod_cast hp
  have hq' : (q - 1) * (3 ^ k : ℕ) + (y.val : ℤ) < ⌈32 * X⌉ := by exact_mod_cast hq
  have hpR : X ≤ (p : ℝ) * 3 ^ k + (y.val : ℝ) := by
    have h2 : ((⌈X⌉ : ℤ) : ℝ) ≤ ((p * (3 ^ k : ℕ) + (y.val : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hp'
    push_cast at h2
    linarith [Int.le_ceil X]
  have hqR : ((q : ℝ) - 1) * 3 ^ k + (y.val : ℝ) < 32 * X := by
    have := Int.lt_ceil.mp hq'
    push_cast at this
    exact this
  have hX0 : (0 : ℝ) ≤ X := le_trans (by positivity) hX
  have hn : (n : ℤ) ≤ max (q - p) 0 := h.le
  rcases le_total (q - p) 0 with hqp | hqp
  · rw [max_eq_right hqp] at hn
    have : n = 0 := by omega
    simp [this]
    linarith
  · rw [max_eq_left hqp] at hn
    have hnR : (n : ℝ) ≤ (q : ℝ) - p := by exact_mod_cast hn
    have h3 : (0 : ℝ) < 3 ^ k := by positivity
    nlinarith

/-- For `X ≥ 3^k`, a nonnegative `δ` on `G_k` and a permutation `σ` of `G_k`,
`∑_{x ∈ ℤ ∩ [X, 32X)} δ(σ(x mod 3^k)) ≤ 33X⟨δ⟩_k`, where `⟨δ⟩_k = residueAvg k δ`. -/
@[collatz_pos_dens "lem_residue_count"]
theorem sum_residue_perm_le (k : ℕ) {X : ℝ} (hX : (3 : ℝ) ^ k ≤ X)
    (δ : ResidueGroup k → ℝ) (hδ : 0 ≤ δ) (σ : Equiv.Perm (ResidueGroup k)) :
    ∑ x ∈ Ico ⌈X⌉ ⌈32 * X⌉, δ (σ ((x : ℤ) : ResidueGroup k)) ≤ 33 * X * residueAvg k δ := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hX0 : (0 : ℝ) ≤ X := le_trans h3.le hX
  have havg : 0 ≤ residueAvg k δ := by
    rw [residueAvg_def]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hδ y)
  rw [← Finset.sum_fiberwise (Ico ⌈X⌉ ⌈32 * X⌉) (fun x : ℤ => ((x : ℤ) : ResidueGroup k))]
  calc ∑ y, ∑ x ∈ Ico ⌈X⌉ ⌈32 * X⌉ with ((x : ℤ) : ResidueGroup k) = y,
          δ (σ ((x : ℤ) : ResidueGroup k))
      = ∑ y, (#{x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | ((x : ℤ) : ResidueGroup k) = y} : ℝ) * δ (σ y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y, 32 * X / 3 ^ k * δ (σ y) := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_ (hδ _)
        rw [le_div_iff₀ h3]
        exact card_filter_residue_mul_le k hX y
    _ = 32 * X * residueAvg k δ := by
        rw [← Finset.mul_sum, Equiv.sum_comp σ δ, residueAvg_def]
        field_simp
    _ ≤ 33 * X * residueAvg k δ := by nlinarith

end CollatzPosDens
