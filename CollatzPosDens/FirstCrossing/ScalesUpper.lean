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
public import CollatzPosDens.FirstCrossing.ScalesB444
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.Linarith

/-!
# Upper growth of the scales

The scales `b_j`, given by `b_0 = 9` and `b_{j+1} = b_j + e_{b_j}`, grow at most like
`201 𝗀^j` with `𝗀 = 101/100`: for every `j ∈ ℕ`,
$$b_j < 201\,\mathsf g^{\,j}.$$

For `j ≤ 444` this is the finite list of exact comparisons `100^j b_j < 201 · 101^j`. For
`j ≥ 444` one proves the stronger `b_j + 100 < 201 𝗀^j` by induction: at `j = 444` it is the
exact comparison `16544 + 100 < 201 𝗀^444`, using `b_444 = 16544`; and once `b_j ≥ 256` the
increment is `e_{b_j} = ⌈b_j/100⌉ ≤ (b_j + 99)/100`, so
`b_{j+1} + 100 ≤ b_j + (b_j + 99)/100 + 100 ≤ 𝗀 (b_j + 100)`.

## Main results

* `CollatzPosDens.scale_lt_mul_growthRatio_pow`: `b_j < 201 𝗀^j` for every `j`.
* `CollatzPosDens.scale_add_hundred_lt_mul_growthRatio_pow`: `b_j + 100 < 201 𝗀^j` for
  `j ≥ 444`.

## Implementation notes

The inequality is stated in `ℝ`, with the rational ratio `𝗀` cast to `ℝ`. The finite range
`j ≤ 444` is checked as the natural-number inequality `100^j b_j < 201 · 101^j` by kernel
evaluation.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The finite range: `100^j b_j < 201 · 101^j` for `j ≤ 444`. -/
private theorem scale_mul_pow_lt_of_le {j : ℕ} (hj : j ≤ 444) :
    100 ^ j * scale j < 201 * 101 ^ j := by
  have h : ∀ j < 445, 100 ^ j * scale j < 201 * 101 ^ j := by decide +kernel
  exact h j (by omega)

/-- Cast form: `(𝗀 : ℝ)^j = 101^j / 100^j`. -/
private theorem growthRatio_cast_pow (j : ℕ) :
    (growthRatio : ℝ) ^ j = (101 : ℝ) ^ j / 100 ^ j := by
  rw [growthRatio_cast, div_pow]

/-- For `j ≥ 444`, the scales satisfy the stronger bound `b_j + 100 < 201 𝗀^j`. -/
theorem scale_add_hundred_lt_mul_growthRatio_pow {j : ℕ} (hj : 444 ≤ j) :
    (scale j : ℝ) + 100 < 201 * (growthRatio : ℝ) ^ j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [scale_444, growthRatio_cast_pow, mul_div_assoc', lt_div_iff₀ (by positivity)]
    exact_mod_cast (by decide +kernel :
      (16544 + 100) * 100 ^ 444 < 201 * 101 ^ 444)
  | succ j hj ih =>
    have hb : 256 ≤ scale j := by
      have := scale_monotone hj
      rw [scale_444] at this
      omega
    have he : ((eb (scale j) : ℕ) : ℝ) ≤ ((scale j : ℝ) + 99) / 100 := by
      rw [eb_of_le hb]
      have := Nat.cast_div_le (α := ℝ) (m := scale j + 99) (n := 100)
      push_cast at this
      exact this
    rw [scale_succ, Nat.cast_add, pow_succ, growthRatio_cast]
    rw [growthRatio_cast] at ih
    nlinarith

/-- **Upper growth of the scales**: for every `j ∈ ℕ`, `b_j < 201 𝗀^j`. -/
@[collatz_pos_dens "lem_scales_upper"]
theorem scale_lt_mul_growthRatio_pow (j : ℕ) :
    (scale j : ℝ) < 201 * (growthRatio : ℝ) ^ j := by
  rcases le_or_gt j 444 with hj | hj
  · rw [growthRatio_cast_pow, mul_div_assoc', lt_div_iff₀ (by positivity), mul_comm]
    exact_mod_cast scale_mul_pow_lt_of_le hj
  · have := scale_add_hundred_lt_mul_growthRatio_pow hj.le
    linarith

end CollatzPosDens
