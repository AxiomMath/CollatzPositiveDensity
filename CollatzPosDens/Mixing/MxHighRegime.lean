/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FourierDecay.ChPrimCoeff
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxSubmassLe
public import CollatzPosDens.Mixing.MxSubmassUnion
public import CollatzPosDens.Mixing.MxOscPerturb
public import CollatzPosDens.Mixing.MxOscSubadditive
public import CollatzPosDens.Mixing.MxSliceGate
public import CollatzPosDens.Mixing.MxGateUnion
public import CollatzPosDens.Mixing.MxGateDisjoint
public import CollatzPosDens.Mixing.MxGateMassSum
public import CollatzPosDens.Mixing.MxGateWeightSum
public import CollatzPosDens.Mixing.MxCoverDeficit
public import CollatzPosDens.Mixing.MxSliceOsc
public import Mathlib.Analysis.Real.Sqrt

/-!
# Oscillation of the reference law in the high regime

Let `n ≥ 2 ^ 131072` and `m ≤ n` with `9 n ≤ 10 m`. Then the reference law `μ_n` has small
oscillation at scale `m`:
$$\mathrm{Osc}_{m,n}(\mu_n) \le \bigl(3 C_* 20^{A_*} + 2\bigr) n^{-9/8},
\qquad A_* = \tfrac{10241}{4096}.$$

By the covering deficit, `∑_y |μ_n(y) - Sub^n_{𝒰_n}(y)| ≤ n^{-9/8}`, so the perturbation bound
gives `Osc_{m,n}(μ_n) ≤ Osc_{m,n}(Sub^n_{𝒰_n}) + 2 n^{-9/8}`. The slice gates `Sl(n, k, l)`
are pairwise disjoint, so `Sub^n_{𝒰_n}` is the sum of the slice submasses and, by
subadditivity, its oscillation is at most the sum of theirs. Each slice contributes at most
`δ √(x_{k,l} a_{k,l})` with `δ = C_* 20^{A_*} n^{-A_*}`, `x_{k,l} = 3^n 2^{-l}` and
`a_{k,l} = 𝐩(Hd(n, k, l))`; only pairs with nonempty head gate contribute. The Cauchy–Schwarz
inequality, the entropy-weight bound `∑ x_{k,l} ≤ 8 n^{5633/2048}` and the mass bound
`∑ a_{k,l} ≤ 1` give `Osc_{m,n}(Sub^n_{𝒰_n}) ≤ √8 δ n^{5633/4096} ≤ 3 C_* 20^{A_*} n^{-9/8}`.

## Main results

* `CollatzPosDens.oscillation_refLaw_le_of_nine_mul_le`: the bound above.

## Implementation notes

As elsewhere, the `[0, ∞]`-valued law `μ_n` and the submasses enter the oscillation through
`ENNReal.toReal`; every value is at most one, so this loses nothing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.9.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open Finset

/-- The oscillation of the gate-union submass, for `n ≥ 2 ^ 131072` and `9 n ≤ 10 m`. -/
private theorem oscillation_subMass_mxGateUnion_le {n m : ℕ} (hn : 2 ^ 131072 ≤ n)
    (hmn : m ≤ n) (h9 : 9 * n ≤ 10 * m) :
    oscillation hmn (fun y => (subMass n (mxGateUnion n) y).toReal) ≤
      3 * Cstar * 20 ^ (10241 / 4096 : ℝ) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
  classical
  set s : Finset (ℕ × ℕ) := range n ×ˢ range (2 * n) with hs
  set I : Finset (ℕ × ℕ) := s.filter (fun p => (mxHeadGate n p.1 p.2).Nonempty) with hI
  set δ : ℝ := Cstar * 20 ^ (10241 / 4096 : ℝ) / (n : ℝ) ^ (10241 / 4096 : ℝ) with hδ
  set x : ℕ × ℕ → ℝ := fun p => (3 : ℝ) ^ n * (2⁻¹ : ℝ) ^ p.2 with hx
  set a : ℕ × ℕ → ℝ := fun p => (geomMass (mxHeadGate n p.1 p.2)).toReal with ha
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (by positivity) hn
    exact_mod_cast this
  have hδ0 : 0 ≤ δ := by
    have := Cstar_pos
    positivity
  have hx0 : ∀ p, 0 ≤ x p := fun p => by simp only [hx]; positivity
  have ha0 : ∀ p, 0 ≤ a p := fun p => ENNReal.toReal_nonneg
  have hsum : (fun y => (subMass n (mxGateUnion n) y).toReal) =
      ∑ p ∈ s, fun y => (subMass n (mxSliceGate n p.1 p.2) y).toReal := by
    funext y
    rw [Finset.sum_apply, mxGateUnion_eq_biUnion_product,
      subMass_biUnion_finset n s (pairwiseDisjoint_mxSliceGate n _) y, ENNReal.toReal_sum]
    exact fun p _ => subMass_ne_top_of_subset_length n
      (fun _ hw => length_of_mem_mxSliceGate hw) y
  have hrestr : ∑ p ∈ s, δ * Real.sqrt (x p * a p) = ∑ p ∈ I, δ * Real.sqrt (x p * a p) := by
    rw [hI, Finset.sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with hne
    · rfl
    · have h0 : a p = 0 := by
        simp only [ha]
        rw [Set.not_nonempty_iff_eq_empty.1 hne, geomMass_empty, ENNReal.toReal_zero]
      rw [h0, mul_zero, Real.sqrt_zero, mul_zero]
  have hCS : ∑ p ∈ I, Real.sqrt (x p * a p) ≤
      Real.sqrt (∑ p ∈ I, x p) * Real.sqrt (∑ p ∈ I, a p) := by
    simp_rw [Real.sqrt_mul (hx0 _)]
    exact Real.sum_sqrt_mul_sqrt_le I hx0 ha0
  have hxsum : ∑ p ∈ I, x p ≤ 8 * (n : ℝ) ^ ((5633 : ℝ) / 2048) := by
    refine le_of_eq_of_le (sum_congr rfl fun p _ => ?_) (mxGateWeightSum_le hn)
    simp only [hx, zpow_neg, zpow_natCast, inv_pow]
  have hasum : ∑ p ∈ I, a p ≤ 1 := by
    have h1 := mxGateMassSum_finset_le n I fun p hp =>
      mem_range.1 (mem_product.1 (mem_filter.1 hp).1).1
    have hne : ∀ p ∈ I, geomMass (mxHeadGate n p.1 p.2) ≠ ⊤ := fun p hp =>
      ne_top_of_le_ne_top ENNReal.one_ne_top
        ((single_le_sum (f := fun q => geomMass (mxHeadGate n q.1 q.2))
          (fun _ _ => zero_le) hp).trans h1)
    simp only [ha]
    rw [← ENNReal.toReal_sum hne]
    exact (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.2 hne) ENNReal.one_ne_top).2 h1
      |>.trans_eq ENNReal.toReal_one
  have hsqrt8 : Real.sqrt 8 ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hfinal : δ * (Real.sqrt (8 * (n : ℝ) ^ ((5633 : ℝ) / 2048)) * Real.sqrt 1) ≤
      3 * Cstar * 20 ^ (10241 / 4096 : ℝ) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
    rw [Real.sqrt_one, mul_one, Real.sqrt_mul (by norm_num),
      Real.sqrt_eq_rpow ((n : ℝ) ^ _), ← Real.rpow_mul hnpos.le, hδ]
    have hpow : (n : ℝ) ^ ((5633 : ℝ) / 2048 * (1 / 2)) / (n : ℝ) ^ (10241 / 4096 : ℝ) =
        (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
      rw [← Real.rpow_sub hnpos]
      norm_num
    have hC : 0 ≤ Cstar * 20 ^ (10241 / 4096 : ℝ) := by
      have := Cstar_pos
      positivity
    have hN : 0 ≤ (n : ℝ) ^ (-(9 / 8 : ℝ)) := by positivity
    calc Cstar * 20 ^ (10241 / 4096 : ℝ) / (n : ℝ) ^ (10241 / 4096 : ℝ) *
          (Real.sqrt 8 * (n : ℝ) ^ ((5633 : ℝ) / 2048 * (1 / 2)))
        = Real.sqrt 8 * (Cstar * 20 ^ (10241 / 4096 : ℝ)) *
            ((n : ℝ) ^ ((5633 : ℝ) / 2048 * (1 / 2)) / (n : ℝ) ^ (10241 / 4096 : ℝ)) := by
          ring
      _ = Real.sqrt 8 * (Cstar * 20 ^ (10241 / 4096 : ℝ)) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
          rw [hpow]
      _ ≤ 3 * (Cstar * 20 ^ (10241 / 4096 : ℝ)) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
          gcongr
      _ = 3 * Cstar * 20 ^ (10241 / 4096 : ℝ) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by ring
  rw [hsum]
  calc oscillation hmn (∑ p ∈ s, fun y => (subMass n (mxSliceGate n p.1 p.2) y).toReal)
      ≤ ∑ p ∈ s, oscillation hmn (fun y => (subMass n (mxSliceGate n p.1 p.2) y).toReal) :=
        oscillation_sum_le hmn s _
    _ ≤ ∑ p ∈ s, δ * Real.sqrt (x p * a p) := sum_le_sum fun p hp =>
        oscillation_subMass_mxSliceGate_le_sqrt hn (mem_range.1 (mem_product.1 hp).1) hmn h9
    _ = δ * ∑ p ∈ I, Real.sqrt (x p * a p) := by rw [hrestr, mul_sum]
    _ ≤ δ * (Real.sqrt (∑ p ∈ I, x p) * Real.sqrt (∑ p ∈ I, a p)) :=
        mul_le_mul_of_nonneg_left hCS hδ0
    _ ≤ δ * (Real.sqrt (8 * (n : ℝ) ^ ((5633 : ℝ) / 2048)) * Real.sqrt 1) := by
        gcongr
    _ ≤ _ := hfinal

/-- **Oscillation in the high regime.** Let `n ≥ 2 ^ 131072` and `m ≤ n` with `9 n ≤ 10 m`.
Then `Osc_{m,n}(μ_n) ≤ (3 C_* 20^{10241/4096} + 2) n^{-9/8}`. -/
@[collatz_pos_dens "lem_mx_high_regime"]
theorem oscillation_refLaw_le_of_nine_mul_le {n m : ℕ} (hn : 2 ^ 131072 ≤ n) (hmn : m ≤ n)
    (h9 : 9 * n ≤ 10 * m) :
    oscillation hmn (fun y => (refLaw n y).toReal) ≤
      (3 * Cstar * 20 ^ (10241 / 4096 : ℝ) + 2) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
  have hoscU := oscillation_subMass_mxGateUnion_le hn hmn h9
  have hdefect := sum_abs_refLaw_sub_subMass_mxGateUnion_le n hn
  calc oscillation hmn (fun y => (refLaw n y).toReal)
      ≤ oscillation hmn (fun y => (subMass n (mxGateUnion n) y).toReal) +
          2 * ∑ y, |(refLaw n y).toReal - (subMass n (mxGateUnion n) y).toReal| :=
        oscillation_le_add_two_mul_sum_abs_sub hmn _ _
    _ ≤ 3 * Cstar * 20 ^ (10241 / 4096 : ℝ) * (n : ℝ) ^ (-(9 / 8 : ℝ)) +
          2 * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
        gcongr
    _ = (3 * Cstar * 20 ^ (10241 / 4096 : ℝ) + 2) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by ring

end CollatzPosDens
