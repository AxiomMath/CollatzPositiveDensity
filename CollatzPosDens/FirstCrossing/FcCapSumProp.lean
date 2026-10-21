/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.Recipe.Nstar
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The sum of the shifted caps above the generation threshold

The shifted caps satisfy `K_j + 3 = 32 + ⌊j/56⌋ ≤ 32 + j/56`, so
$$1 + \sum_{j<n} (K_j + 3) \le 1 + 32 n + \frac{n(n-1)}{112} =: G(n).$$
Since `1/82 - 1/112 = 15/4592` and `-32 + 1/112 = -3583/112`,
$$\frac{n^2}{82} - G(n) = n\Bigl(\frac{15}{4592}\,n - \frac{3583}{112}\Bigr) - 1,$$
and at the generation threshold `N_* = 9853` the bracket is `223/1148 > 0`. Hence, for every
`n ≥ N_*`, `n^2/82 - G(n) ≥ 223 n/1148 - 1 ≥ 2196071/1148 > 0`, that is
$$1 + \sum_{j=0}^{n-1} (K_j + 3) < \frac{n^2}{82} \qquad (n \ge N_*).$$

## Main results

* `CollatzPosDens.one_add_sum_cap_add_three_lt_sq_div_82`: for every `n ≥ N_*`,
  `1 + ∑_{j<n} (K_j + 3) < n^2/82`.

## Implementation notes

The bound `112 (K_j + 3) ≤ 3584 + 2j` and induction on `n` give the natural-number estimate
`112 ∑_{j<n}(K_j+3) + n ≤ 3584 n + n^2`, which is `∑_{j<n}(K_j+3) ≤ G(n) - 1` with denominators
cleared. The inequality `82 (1 + ∑) < n^2` follows from `30 n^2 - 293806 n - 9184 > 0` for
`n ≥ 9853`, which is `n^2/82 - G(n) > 0` multiplied by `9184 = 82 · 112`.
-/

@[expose] public section

namespace CollatzPosDens

/-- With denominators cleared, `∑_{j<n} (K_j + 3) ≤ 32 n + n(n-1)/112`: for every `n`,
`112 ∑_{j<n} (K_j + 3) + n ≤ 3584 n + n^2`. -/
private theorem sum_range_cap_add_three_le_quadratic (n : ℕ) :
    112 * ∑ j ∈ Finset.range n, (cap j + 3) + n ≤ 3584 * n + n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have : 112 * cap n ≤ 112 * 29 + 2 * n := by unfold cap; omega
    nlinarith

/-- For every integer `n` at least `generationThreshold = 9853`,
`1 + ∑_{j<n} (K_j + 3) < n^2/82`. -/
@[collatz_pos_dens "lem_fc_cap_sum_prop"]
theorem one_add_sum_cap_add_three_lt_sq_div_82 {n : ℕ} (hn : generationThreshold ≤ n) :
    (1 + ∑ j ∈ Finset.range n, ((cap j : ℝ) + 3)) < (n : ℝ) ^ 2 / 82 := by
  rw [generationThreshold_def] at hn
  have h := sum_range_cap_add_three_le_quadratic n
  have hnat : 82 * (1 + ∑ j ∈ Finset.range n, (cap j + 3)) < n ^ 2 := by
    nlinarith
  have hreal : (82 : ℝ) * (1 + ∑ j ∈ Finset.range n, ((cap j : ℝ) + 3)) < (n : ℝ) ^ 2 := by
    exact_mod_cast hnat
  rw [lt_div_iff₀ (by norm_num)]
  linarith

end CollatzPosDens
