/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.FcComplement
public import CollatzPosDens.FirstCrossing.FcLateSurvival
public import CollatzPosDens.FirstCrossing.FcStartupProduct
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint

/-!
# Surviving mass of the central families

Write `p_j = 𝐩(𝒞(b_j, K_j))` for the geometric mass of the central family at the scale `b_j`
with cap `K_j`. Then for every `s ∈ ℕ`,
$$\prod_{j<s} p_j > 2^{-22}.$$

Each `p_j` lies in `[0, 1]`: `𝒞(b_j, K_j) ⊆ 𝒲(b_j, r_{b_j}, K_j)` is prefix-disjoint with word
lengths at most `h_{b_j}`, so `1 - p_j` is itself a geometric mass. Hence the product over
`j < s` is at least the product over `j < 444` times the product over `444 ≤ j < s` (the latter
empty when `s ≤ 444`), which exceeds `(72/5) 2^{-25} · 5/9 = 2^{-22}` by the startup product and
the late survival bound.

## Main results

* `CollatzPosDens.geomMass_centralFamily_le_one`: `𝐩(𝒞(b, K)) ≤ 1`.
* `CollatzPosDens.two_inv_pow_lt_prod_geomMass_centralFamily`: the survival product bound.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open InformationTheory

namespace CollatzPosDens

/-- The central family `𝒞(b, K)` is prefix-disjoint, as a subset of `𝒲(b, r_b, K)`. -/
theorem isPrefixFree_centralFamily_of_firstCrossing (b K : ℕ) :
    IsPrefixFree (centralFamily b K) := fun x hx y hy hxy =>
  isPrefixFree_firstCrossing b (rb b) K x (centralFamily_subset_firstCrossing b K hx) y
    (centralFamily_subset_firstCrossing b K hy) hxy

/-- The central family has geometric mass at most `1`. -/
theorem geomMass_centralFamily_le_one (b K : ℕ) : geomMass (centralFamily b K) ≤ 1 := by
  rw [← geomMass_add_geomMass_setOf_not_prefix_mem
    (isPrefixFree_centralFamily_of_firstCrossing b K) (h := hb b)
    fun _ hw => length_le_hb_of_mem_firstCrossing (centralFamily_subset_firstCrossing b K hw)]
  exact le_self_add

/-- **Surviving mass of the central families**. For every `s`,
`∏_{j<s} 𝐩(𝒞(b_j, K_j)) > 2^{-22}`. -/
@[collatz_pos_dens "lem_survival_product"]
theorem two_inv_pow_lt_prod_geomMass_centralFamily (s : ℕ) :
    (2⁻¹ : ℝ≥0∞) ^ 22 < ∏ j ∈ Finset.range s, geomMass (centralFamily (scale j) (cap j)) := by
  set p : ℕ → ℝ≥0∞ := fun j => geomMass (centralFamily (scale j) (cap j))
  have hp1 : ∀ j, p j ≤ 1 := fun j => geomMass_centralFamily_le_one _ _
  have hsplit : (∏ j ∈ Finset.range 444, p j) * ∏ j ∈ Finset.Ico 444 s, p j ≤
      ∏ j ∈ Finset.range s, p j := by
    rcases le_total s 444 with hs | hs
    · rw [Finset.Ico_eq_empty_of_le hs, Finset.prod_empty, mul_one]
      rw [← Finset.prod_range_mul_prod_Ico p hs]
      exact mul_le_of_le_one_right' (Finset.prod_le_one fun j _ => hp1 j)
    · rw [Finset.prod_range_mul_prod_Ico p hs]
  refine lt_of_lt_of_le ?_ hsplit
  have h1 := geomMass_centralFamily_startup_prod_gt
  have h2 := five_ninths_lt_prod_geomMass_centralFamily s
  have heq : (2⁻¹ : ℝ≥0∞) ^ 22 = (72 / 5 : ℝ≥0∞) * 2⁻¹ ^ 25 * (5 / 9) := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_div,
      ENNReal.toReal_ofNat]
    norm_num
  rw [heq]
  exact ENNReal.mul_lt_mul h1 h2

end CollatzPosDens
