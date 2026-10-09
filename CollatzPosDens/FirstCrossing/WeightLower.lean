/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.BarrierPower
public import CollatzPosDens.Maps.Weight

/-!
# A lower bound on the weight of a first-crossing word

Every word `w` of the first-crossing family `𝒲(b, u, K)` has weight
$$\omega(w) \ge 2^{-K-1+r_b-u}\,(3/4)^b.$$
Indeed, with `s = |w|`, the crossing condition gives `A(w) ≤ H_{b,u}(s) + K`, and the upper
bound `2^{H_{b,u}(s)} ≤ 2 · 4^b 3^{s-b} 2^{u-r_b}` turns `ω(w) = 3^s 2^{-A(w)}` into the
claimed bound.

## Main results

* `CollatzPosDens.le_weight_of_mem_firstCrossing`: the lower bound on `ω(w)`.

## Implementation notes

The bound is stated for every natural number `b`, not only for `b ≥ 1`. The weight is rational
and the power of `2` has an integer exponent (`zpow`).

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- Every word `w ∈ 𝒲(b, u, K)` has weight `ω(w) ≥ 2^(-K-1+r_b-u) (3/4)^b`. -/
@[collatz_pos_dens "lem_weight_lower"]
theorem le_weight_of_mem_firstCrossing {b : ℕ} {u : ℤ} {K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b u K) :
    (2 : ℚ) ^ (-(K : ℤ) - 1 + rb b - u) * (3 / 4) ^ b ≤ w.weight := by
  set s := w.length with hs
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hAle : (2 : ℝ) ^ w.valSum ≤
      2 * 4 ^ b * (3 : ℝ) ^ ((s : ℤ) - b) * 2 ^ (u - rb b) * 2 ^ (K : ℤ) := by
    rw [← zpow_natCast]
    refine (zpow_le_zpow_right₀ one_le_two
      (valSum_le_barrier_add_of_mem_firstCrossing hw)).trans ?_
    rw [zpow_add₀ h2]
    exact mul_le_mul_of_nonneg_right (barrier_power_bounds b s u).2 (by positivity)
  have e1 : (2 : ℝ) ^ (-(K : ℤ) - 1 + rb b - u) * 2 * 2 ^ (u - rb b) * 2 ^ (K : ℤ) = 1 := by
    rw [← zpow_add_one₀ h2, ← zpow_add₀ h2, ← zpow_add₀ h2, ← zpow_zero (2 : ℝ)]
    congr 1
    ring
  have e2 : (3 / 4 : ℝ) ^ b * 4 ^ b * (3 : ℝ) ^ ((s : ℤ) - b) = 3 ^ s := by
    rw [← mul_pow, show (3 / 4 : ℝ) * 4 = 3 by norm_num, ← zpow_natCast, ← zpow_add₀
      (by norm_num : (3 : ℝ) ≠ 0), ← zpow_natCast]
    congr 1
    ring
  rw [← Rat.cast_le (K := ℝ)]
  simp only [Word.weight, ← hs]
  push_cast
  rw [le_div_iff₀ (by positivity)]
  refine (mul_le_mul_of_nonneg_left hAle (by positivity)).trans_eq ?_
  calc _ = ((2 : ℝ) ^ (-(K : ℤ) - 1 + rb b - u) * 2 * 2 ^ (u - rb b) * 2 ^ (K : ℤ)) *
        ((3 / 4 : ℝ) ^ b * 4 ^ b * (3 : ℝ) ^ ((s : ℤ) - b)) := by ring
    _ = 3 ^ s := by rw [e1, e2, one_mul]

end CollatzPosDens
