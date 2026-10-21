/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.OrdinaryTime.S07Bstar
public import Mathlib.Basic.Real.Basic

/-!
# The last scale against the scale sum

Write `b_n = scale n` and `B_*(n) = scaleSum n`. The increment `eb b = ⌈b/100⌉` satisfies
`eb b < b/100 + 1` for every `b ∈ ℕ`. Telescoping the recursion `b_0 = 16544`,
`b_{j+1} = b_j + eb b_j` gives, for every `n ∈ ℕ`,
$$b_n = b_0 + \sum_{j=0}^{n-1} e_{b_j} \le 16544 + \frac1{100}\sum_{j=0}^{n-1} b_j + n
  \le 16544 + \frac{B_*(n)}{100} + n.$$

## Main results

* `CollatzPosDens.scale_le_scaleSum_div_hundred`: `b_n ≤ 16544 + B_*(n)/100 + n` in `ℝ`.
* `CollatzPosDens.hundred_mul_scale_le_scaleSum`: the cleared-denominator form
  `100 b_n ≤ 1654400 + B_*(n) + 100 n`, in `ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Telescoped recursion from `b_0 = 16544`:
`100 b_n ≤ 1654400 + 100 n + ∑_{j=0}^{n-1} b_j`. -/
private theorem hundred_mul_scale_le_sum_range (n : ℕ) :
    100 * scale n ≤ 1654400 + 100 * n + ∑ j ∈ Finset.range n, scale j := by
  induction n with
  | zero => rw [scale_zero]; simp
  | succ n ih =>
    rw [scale_succ, eb_eq, Finset.sum_range_succ]
    have := Nat.div_mul_le_self (scale n + 99) 100
    omega

/-- For every `n`, `100 b_n ≤ 1654400 + B_*(n) + 100 n`. -/
theorem hundred_mul_scale_le_scaleSum (n : ℕ) :
    100 * scale n ≤ 1654400 + scaleSum n + 100 * n := by
  have h := hundred_mul_scale_le_sum_range n
  have hsum : ∑ j ∈ Finset.range n, scale j ≤ scaleSum n :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 n.le_succ)
  omega

/-- **The last scale against the scale sum.** For every `n ∈ ℕ`,
`b_n ≤ 16544 + B_*(n)/100 + n`. -/
@[collatz_pos_dens "lem_ck_scale_last"]
theorem scale_le_scaleSum_div_hundred (n : ℕ) :
    (scale n : ℝ) ≤ 16544 + (scaleSum n : ℝ) / 100 + n := by
  have h : (100 * scale n : ℝ) ≤ 1654400 + scaleSum n + 100 * n := by
    exact_mod_cast hundred_mul_scale_le_scaleSum n
  linarith

end CollatzPosDens
