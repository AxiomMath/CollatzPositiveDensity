/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.CeilBounds

/-!
# Two-sided bounds on `2 ^ H_{b,u}(s)`

For natural numbers `b`, `s` and an integer `u`, the barrier `H_{b,u}(s) = barrier b u s`
satisfies, with `r_b = rb b`,
$$\tfrac12\,4^b\,3^{s-b}\,2^{u-r_b} \le 2^{H_{b,u}(s)} \le 2\cdot 4^b\,3^{s-b}\,2^{u-r_b}.$$
Writing `B(j) = ceilLog3 j`, if `s ≥ b` then `2^{H_{b,u}(s)} = 4^b 2^{B(s-b)} 2^{u-r_b}` and
`3^j ≤ 2^{B(j)} ≤ 2·3^j` with `j = s - b`; if `s < b` then
`2^{H_{b,u}(s)} = 4^b 2^{-B(b-s)} 2^{u-r_b}` and the same bounds with `j = b - s` give
`½·3^{-j} ≤ 2^{-B(j)} ≤ 3^{-j}`.

## Main results

* `CollatzPosDens.barrier_power_bounds`: the two-sided bound on `2 ^ H_{b,u}(s)` in `ℝ`.

## Implementation notes

The powers with integer exponent are `zpow` in `ℝ`; the exponent `s - b` is taken in `ℤ`.
The indices `b` and `s` are natural numbers, matching the signature of `barrier`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `b, s ∈ ℕ` and `u ∈ ℤ`,
`½ · 4^b · 3^(s-b) · 2^(u-r_b) ≤ 2^H_{b,u}(s) ≤ 2 · 4^b · 3^(s-b) · 2^(u-r_b)`. -/
@[collatz_pos_dens "lem_s03_barrier_power"]
theorem barrier_power_bounds (b s : ℕ) (u : ℤ) :
    (1 / 2 : ℝ) * 4 ^ b * (3 : ℝ) ^ ((s : ℤ) - b) * (2 : ℝ) ^ (u - rb b) ≤
        (2 : ℝ) ^ barrier b u s ∧
      (2 : ℝ) ^ barrier b u s ≤
        2 * 4 ^ b * (3 : ℝ) ^ ((s : ℤ) - b) * (2 : ℝ) ^ (u - rb b) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hK : (0 : ℝ) < (2 : ℝ) ^ (u - rb b) := zpow_pos two_pos _
  have h4 : (0 : ℝ) < 4 ^ b := by positivity
  have h4' : (2 : ℝ) ^ (2 * (b : ℤ)) = 4 ^ b := by
    rw [zpow_mul, zpow_ofNat, zpow_natCast]
    norm_num
  rcases le_total b s with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨hl, hu⟩ := ceilLog3_bounds j
    have hl' : (3 : ℝ) ^ j ≤ 2 ^ ceilLog3 j := by exact_mod_cast hl
    have hu' : (2 : ℝ) ^ ceilLog3 j ≤ 2 * 3 ^ j := by exact_mod_cast hu
    have hH : (2 : ℝ) ^ barrier b u (b + j) =
        4 ^ b * 2 ^ ceilLog3 j * 2 ^ (u - rb b) := by
      rw [barrier_of_le u h, Nat.add_sub_cancel_left, add_sub_assoc, zpow_add₀ h2,
        zpow_add₀ h2, h4', zpow_natCast]
    have he : ((b + j : ℕ) : ℤ) - b = j := by push_cast; ring
    rw [hH, he, zpow_natCast]
    have h3 : (0 : ℝ) < 3 ^ j := by positivity
    constructor <;> nlinarith [mul_pos h4 hK]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨hl, hu⟩ := ceilLog3_bounds j
    have hl' : (3 : ℝ) ^ j ≤ 2 ^ ceilLog3 j := by exact_mod_cast hl
    have hu' : (2 : ℝ) ^ ceilLog3 j ≤ 2 * 3 ^ j := by exact_mod_cast hu
    have hH : (2 : ℝ) ^ barrier (s + j) u s =
        4 ^ (s + j) * (2 ^ ceilLog3 j)⁻¹ * 2 ^ (u - rb (s + j)) := by
      rw [barrier_of_ge u h, Nat.add_sub_cancel_left, add_sub_assoc, sub_eq_add_neg,
        zpow_add₀ h2, zpow_add₀ h2, h4', zpow_neg, zpow_natCast]
    have he : ((s : ℕ) : ℤ) - ((s + j : ℕ) : ℤ) = -(j : ℤ) := by push_cast; ring
    rw [hH, he, zpow_neg, zpow_natCast]
    have h3 : (0 : ℝ) < 3 ^ j := by positivity
    have hB : (0 : ℝ) < 2 ^ ceilLog3 j := by positivity
    have i1 : (1 / 2 : ℝ) * (3 ^ j)⁻¹ ≤ (2 ^ ceilLog3 j)⁻¹ := by
      rw [← one_div, ← one_div, div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) hB]
      linarith
    have i2 : ((2 : ℝ) ^ ceilLog3 j)⁻¹ ≤ (3 ^ j)⁻¹ := inv_anti₀ h3 hl'
    have hC := (mul_pos h4 hK).le
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left i1 hC,
      mul_le_mul_of_nonneg_left i2 hC, inv_pos.mpr h3]

end CollatzPosDens
