/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Width
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Seed.DepthWidth
public import CollatzPosDens.OrdinaryTime.Bstar
public import CollatzPosDens.OrdinaryTime.Wstar
public import CollatzPosDens.OrdinaryTime.CkEarlySum
public import CollatzPosDens.OrdinaryTime.CkLateGrowth
public import CollatzPosDens.OrdinaryTime.CkScale2254
public import CollatzPosDens.OrdinaryTime.CkWidthLate

/-!
# The width sum is small against the scale sum

For every integer $n \ge 2 \cdot 10^{10}$,
$$9000\, W_*(n) \le B_*(n),$$
where $W_*(n) = \sum_{j<n} \mathrm{dw}(b_j)$ is the width sum and
$B_*(n) = \sum_{j \le n} b_j$ is the scale sum.

The proof splits $W_*(n)$ at $j = 2254$. For $j < 2254$ one uses $\mathrm{dw}(b_j) \le b_j$, and
the early scale sum is bounded numerically by $9000 \sum_{j<2254} b_j \le \frac{11}{20} 2^{41}
10^{10}$. For $j \ge 2254$ the scale satisfies $b_j \ge b_{2254} \ge 2^{40} \ge 256$, so
$\mathrm{dw}(b_j) = \mathrm{wd}(b_j) \le b_j / 20000$. Finally
$2^{41} \cdot 10^{10} \le 2^{40} n \le b_n \le B_*(n)$.

## Main results

* `CollatzPosDens.nine_thousand_mul_widthSum_le_scaleSum`: `9000 W_*(n) ≤ B_*(n)` for
  `n ≥ 2 · 10^10`.

## Implementation notes

The argument is carried out in `ℕ` after multiplying through by `20`: the claim becomes
`180000 W_*(n) ≤ 20 B_*(n)`, which avoids all fractions.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §19.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **Width sum.** For every `n ≥ 2 · 10^10`, `9000 W_*(n) ≤ B_*(n)`. -/
@[collatz_pos_dens "lem_width_sum"]
theorem nine_thousand_mul_widthSum_le_scaleSum (n : ℕ) (hn : 2 * 10 ^ 10 ≤ n) :
    9000 * widthSum n ≤ scaleSum n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2254 + m := ⟨n - 2254, by omega⟩
  rw [widthSum_def, sum_range_add]
  set S := ∑ j ∈ range 2254, scale j
  set W₁ := ∑ j ∈ range 2254, dw (scale j)
  set W₂ := ∑ k ∈ range m, dw (scale (2254 + k))
  set T := ∑ k ∈ range m, scale (2254 + k)
  have hW₁ : W₁ ≤ S := sum_le_sum fun _ _ => dw_le_self _
  have hW₂ : 20000 * W₂ ≤ T := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have h40 : 2 ^ 40 ≤ scale (2254 + k) :=
      two_pow_forty_le_scale_2254.trans (scale_monotone (Nat.le_add_right _ _))
    rw [dw_of_le (le_trans (by norm_num) h40)]
    exact twenty_thousand_mul_wd_le h40
  have hST : S + T ≤ scaleSum (2254 + m) := by
    have : S + T = ∑ j ∈ range (2254 + m), scale j := (sum_range_add _ _ _).symm
    rw [this, scaleSum_def]
    exact sum_le_sum_of_subset (range_subset_range.2 (Nat.le_succ _))
  have hS := scale_early_sum_le
  have hB : 2 ^ 40 * (2254 + m) ≤ scaleSum (2254 + m) :=
    (two_pow_forty_mul_le_scale _ hn).trans (scale_le_scaleSum _)
  have hn' : 2 ^ 40 * (2 * 10 ^ 10) ≤ 2 ^ 40 * (2254 + m) := Nat.mul_le_mul_left _ hn
  change 180000 * S ≤ 11 * 2 ^ 41 * 10 ^ 10 at hS
  omega

end CollatzPosDens
