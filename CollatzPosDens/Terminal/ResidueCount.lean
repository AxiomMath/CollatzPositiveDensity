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

Let `q ≥ 0`, let `X ≥ 3^q` be real, let `Φ ≥ 0` be a function on `G_q = ℤ/3^qℤ` and let `σ` be a
permutation of `G_q`. Each residue class modulo `3^q` meets the integers of `[X, 32X)` in at most
`31X/3^q + 1 ≤ 32X/3^q` points, so summing `Φ(σ(x mod 3^q))` over those integers gives at most
`(32X/3^q) ∑_y Φ(σ y) = 32X⟨Φ⟩_q ≤ 33X⟨Φ⟩_q`.

## Main results

* `CollatzPosDens.card_filter_residue_mul_le`: a residue class modulo `3^q` contains at most
  `32X/3^q` integers of `[X, 32X)`.
* `CollatzPosDens.sum_residue_perm_le`: the residue-count bound
  `∑_{x ∈ ℤ ∩ [X, 32X)} Φ(σ(x mod 3^q)) ≤ 33X⟨Φ⟩_q`.

## Implementation notes

The integers of the real interval `[X, 32X)` are written as `Finset.Ico ⌈X⌉ ⌈32 * X⌉`, which has
exactly these elements since `⌈X⌉ ≤ x ↔ X ≤ x` and `x < ⌈32X⌉ ↔ x < 32X` for integers `x`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `X ≥ 3^q`, a residue class modulo `3^q` contains at most `32X/3^q` integers of the real
interval `[X, 32X)`. -/
theorem card_filter_residue_mul_le (q : ℕ) {X : ℝ} (hX : (3 : ℝ) ^ q ≤ X)
    (y : ResidueGroup q) :
    (#{x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | ((x : ℤ) : ResidueGroup q) = y} : ℝ) * 3 ^ q ≤ 32 * X := by
  have hr : (0 : ℤ) < 3 ^ q := by positivity
  have hfil : {x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | ((x : ℤ) : ResidueGroup q) = y} =
      {x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | x ≡ (y.val : ℤ) [ZMOD (3 ^ q : ℕ)]} := by
    refine Finset.filter_congr fun x _ => ?_
    rw [← ZMod.intCast_eq_intCast_iff]
    simp
  have h := Int.Ico_filter_modEq_card ⌈X⌉ ⌈32 * X⌉ (r := ((3 ^ q : ℕ) : ℤ))
    (by exact_mod_cast hr) (y.val : ℤ)
  rw [hfil]
  set n := #{x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | x ≡ (y.val : ℤ) [ZMOD (3 ^ q : ℕ)]}
  set a := ⌈((⌈X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ q : ℕ) : ℤ)⌉
  set b := ⌈((⌈32 * X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ q : ℕ) : ℤ)⌉
  have hrQ : (0 : ℚ) < ((3 ^ q : ℕ) : ℤ) := by positivity
  have ha : ((⌈X⌉ : ℤ) : ℚ) ≤ a * ((3 ^ q : ℕ) : ℤ) + (y.val : ℤ) := by
    have := Int.le_ceil (((⌈X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ q : ℕ) : ℤ))
    rw [div_le_iff₀ hrQ] at this
    linarith
  have hb : (b - 1 : ℚ) * ((3 ^ q : ℕ) : ℤ) + (y.val : ℤ) < ((⌈32 * X⌉ : ℤ) : ℚ) := by
    have := Int.ceil_lt_add_one (((⌈32 * X⌉ : ℤ) - (y.val : ℤ) : ℚ) / ((3 ^ q : ℕ) : ℤ))
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hrQ] at this
    linarith
  have ha' : ⌈X⌉ ≤ a * (3 ^ q : ℕ) + (y.val : ℤ) := by exact_mod_cast ha
  have hb' : (b - 1) * (3 ^ q : ℕ) + (y.val : ℤ) < ⌈32 * X⌉ := by exact_mod_cast hb
  have haR : X ≤ (a : ℝ) * 3 ^ q + (y.val : ℝ) := by
    have h2 : ((⌈X⌉ : ℤ) : ℝ) ≤ ((a * (3 ^ q : ℕ) + (y.val : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast ha'
    push_cast at h2
    linarith [Int.le_ceil X]
  have hbR : ((b : ℝ) - 1) * 3 ^ q + (y.val : ℝ) < 32 * X := by
    have := Int.lt_ceil.mp hb'
    push_cast at this
    exact this
  have hX0 : (0 : ℝ) ≤ X := le_trans (by positivity) hX
  have hn : (n : ℤ) ≤ max (b - a) 0 := h.le
  rcases le_total (b - a) 0 with hba | hba
  · rw [max_eq_right hba] at hn
    have : n = 0 := by omega
    simp [this]
    linarith
  · rw [max_eq_left hba] at hn
    have hnR : (n : ℝ) ≤ (b : ℝ) - a := by exact_mod_cast hn
    have h3 : (0 : ℝ) < 3 ^ q := by positivity
    nlinarith

/-- **Residue count.** For `X ≥ 3^q`, a nonnegative `Φ` on `G_q` and a permutation `σ` of `G_q`,
`∑_{x ∈ ℤ ∩ [X, 32X)} Φ(σ(x mod 3^q)) ≤ 33X⟨Φ⟩_q`. -/
@[collatz_pos_dens "lem_residue_count"]
theorem sum_residue_perm_le (q : ℕ) {X : ℝ} (hX : (3 : ℝ) ^ q ≤ X)
    (Φ : ResidueGroup q → ℝ) (hΦ : 0 ≤ Φ) (σ : Equiv.Perm (ResidueGroup q)) :
    ∑ x ∈ Ico ⌈X⌉ ⌈32 * X⌉, Φ (σ ((x : ℤ) : ResidueGroup q)) ≤ 33 * X * residueAvg q Φ := by
  have h3 : (0 : ℝ) < 3 ^ q := by positivity
  have hX0 : (0 : ℝ) ≤ X := le_trans h3.le hX
  have havg : 0 ≤ residueAvg q Φ := by
    rw [residueAvg_def]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hΦ y)
  rw [← Finset.sum_fiberwise (Ico ⌈X⌉ ⌈32 * X⌉) (fun x : ℤ => ((x : ℤ) : ResidueGroup q))]
  calc ∑ y, ∑ x ∈ Ico ⌈X⌉ ⌈32 * X⌉ with ((x : ℤ) : ResidueGroup q) = y,
          Φ (σ ((x : ℤ) : ResidueGroup q))
      = ∑ y, (#{x ∈ Ico ⌈X⌉ ⌈32 * X⌉ | ((x : ℤ) : ResidueGroup q) = y} : ℝ) * Φ (σ y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y, 32 * X / 3 ^ q * Φ (σ y) := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_ (hΦ _)
        rw [le_div_iff₀ h3]
        exact card_filter_residue_mul_le q hX y
    _ = 32 * X * residueAvg q Φ := by
        rw [← Finset.mul_sum, Equiv.sum_comp σ Φ, residueAvg_def]
        field_simp
    _ ≤ 33 * X * residueAvg q Φ := by nlinarith

end CollatzPosDens
