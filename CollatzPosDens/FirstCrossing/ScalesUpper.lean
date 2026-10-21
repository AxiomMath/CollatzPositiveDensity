/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.Linarith

/-!
# Upper growth of the scales

The scales `b_j`, given by `b_0 = 16544` and `b_{j+1} = b_j + e_{b_j}`, grow at most like
`16644 𝗀^j` with `𝗀 = 101/100`: for every `j ∈ ℕ`,
$$b_j < 16644\,\mathsf g^{\,j}.$$

One proves the stronger `b_j + 100 ≤ 16644 𝗀^j` by induction on `j`: at `j = 0` it is the
equality `b_0 + 100 = 16644`, and since `e_b = ⌈b/100⌉ ≤ (b + 99)/100`,
`b_{j+1} + 100 ≤ b_j + (b_j + 99)/100 + 100 < 𝗀 (b_j + 100)`.

## Main results

* `CollatzPosDens.scale_add_hundred_le_mul_growthRatio_pow`: `b_j + 100 ≤ 16644 𝗀^j`.
* `CollatzPosDens.scale_lt_mul_growthRatio_pow`: `b_j < 16644 𝗀^j` for every `j`.

## Implementation notes

The inequality is stated in `ℝ`, with the rational ratio `𝗀` cast to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `j`, the scales satisfy the stronger bound `b_j + 100 ≤ 16644 𝗀^j`. -/
theorem scale_add_hundred_le_mul_growthRatio_pow (j : ℕ) :
    (scale j : ℝ) + 100 ≤ 16644 * (growthRatio : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have he : ((eb (scale j) : ℕ) : ℝ) ≤ ((scale j : ℝ) + 99) / 100 := by
      rw [eb_eq]
      exact_mod_cast Nat.cast_div_le (α := ℝ) (m := scale j + 99) (n := 100)
    rw [scale_succ, Nat.cast_add, pow_succ, growthRatio_cast]
    rw [growthRatio_cast] at ih
    linarith

/-- **Upper growth of the scales**: for every `j ∈ ℕ`, `b_j < 16644 𝗀^j`. -/
@[collatz_pos_dens "lem_scales_upper"]
theorem scale_lt_mul_growthRatio_pow (j : ℕ) :
    (scale j : ℝ) < 16644 * (growthRatio : ℝ) ^ j := by
  linarith [scale_add_hundred_le_mul_growthRatio_pow j]

end CollatzPosDens
