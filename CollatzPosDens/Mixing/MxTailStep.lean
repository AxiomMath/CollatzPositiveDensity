/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr

/-!
# One step of the offset tail recursion

For every real `x ≥ 5`,
$$3\sum_{a\ge1}\frac{2^{-a}}{2^a x+5}\le\frac1{x+2}.$$

## Main results

* `CollatzPosDens.tailStep_le`: the series converges and satisfies the bound; the index
  `a ≥ 1` is written `a + 1` with `a ∈ ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **One step of the offset tail recursion.** For every real `x ≥ 5` the series
`∑_{a ≥ 1} 2^{-a} / (2^a x + 5)` converges and `3 ∑_{a ≥ 1} 2^{-a} / (2^a x + 5) ≤ 1 / (x + 2)`. -/
@[collatz_pos_dens "lem_mx_tail_step"]
theorem tailStep_le {x : ℝ} (hx : 5 ≤ x) :
    Summable (fun a : ℕ => (2 : ℝ)⁻¹ ^ (a + 1) / (2 ^ (a + 1) * x + 5)) ∧
      3 * ∑' a : ℕ, (2 : ℝ)⁻¹ ^ (a + 1) / (2 ^ (a + 1) * x + 5) ≤ 1 / (x + 2) := by
  have hx0 : 0 < x := by linarith
  set f : ℕ → ℝ := fun a => (2 : ℝ)⁻¹ ^ (a + 1) / (2 ^ (a + 1) * x + 5) with hf
  set g : ℕ → ℝ := fun a => 15 * (4 : ℝ)⁻¹ ^ (a + 1) / (x * (2 ^ (a + 1) * x + 5)) with hg
  set h : ℕ → ℝ := fun a => 3 * (4 : ℝ)⁻¹ ^ (a + 1) / x with hh
  have hden : ∀ a : ℕ, 0 < (2 : ℝ) ^ (a + 1) * x + 5 := fun a => by positivity
  -- `3 · 2^{-a} / (2^a x + 5) = 3 · 4^{-a} / x - 15 · 4^{-a} / (x (2^a x + 5))`
  have hfg : ∀ a, 3 * f a = h a - g a := by
    intro a
    simp only [hf, hg, hh]
    have h4 : (4 : ℝ)⁻¹ ^ (a + 1) = ((2 : ℝ) ^ (a + 1))⁻¹ ^ 2 := by
      rw [inv_pow, inv_pow, ← pow_mul, mul_comm, pow_mul]
      norm_num
    have h2 : (2 : ℝ)⁻¹ ^ (a + 1) = ((2 : ℝ) ^ (a + 1))⁻¹ := inv_pow _ _
    have := hden a
    have hu : (0 : ℝ) < 2 ^ (a + 1) := by positivity
    rw [h4, h2]
    generalize (2 : ℝ) ^ (a + 1) = u at *
    field_simp
    ring
  -- `∑_{a ≥ 1} 3 · 4^{-a} / x = 1 / x`
  have hhs : HasSum h (1 / x) := by
    have := hasSum_geometric_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num) (by norm_num)
    convert this.mul_left (3 * (4 : ℝ)⁻¹ / x) using 1
    · funext a
      simp only [hh]
      rw [pow_succ]
      ring
    · field_simp
      norm_num
  have hg0 : ∀ a, 0 ≤ g a := fun a => by have := hden a; positivity
  have hf0 : ∀ a, 0 ≤ f a := fun a => by have := hden a; positivity
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun a => ?_) hhs.summable
    linarith [hfg a, hf0 a]
  have hfs : Summable f := by
    convert (hhs.summable.sub hgs).div_const 3 using 1
    funext a
    rw [← hfg]
    ring
  refine ⟨hfs, ?_⟩
  have hsum : 3 * ∑' a, f a = 1 / x - ∑' a, g a := by
    rw [← tsum_mul_left, ← hhs.tsum_eq, ← hhs.summable.tsum_sub hgs]
    exact tsum_congr hfg
  -- keep only the terms `a = 1, 2` of the positive series `∑ g`
  have hg01 : g 0 + g 1 ≤ ∑' a, g a := by
    simpa [Finset.sum_range_succ] using hgs.sum_le_tsum (Finset.range 2) (fun a _ => hg0 a)
  have key : 1 / x - 1 / (x + 2) ≤ g 0 + g 1 := by
    rw [← sub_nonneg]
    have e : g 0 + g 1 - (1 / x - 1 / (x + 2)) =
        (14 * x ^ 2 - 45 * x - 50) / (16 * x * (x + 2) * (2 * x + 5) * (4 * x + 5)) := by
      simp only [hg]
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    nlinarith
  linarith

end CollatzPosDens
