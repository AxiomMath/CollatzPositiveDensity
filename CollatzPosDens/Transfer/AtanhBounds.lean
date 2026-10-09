/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Inverse hyperbolic tangent enclosure of the logarithm

For `0 ≤ t < 1` the series `log (1 + t) - log (1 - t) = 2 ∑_{j ≥ 0} t^(2j+1) / (2j+1)` has
nonnegative terms, so every partial sum is a lower bound. The tail after `n` terms is at most
`2 t^(2n+1) / (2n+1) · ∑_{k ≥ 0} t^(2k) = 2 t^(2n+1) / ((2n+1)(1 - t²))`, since
`1/(2(n+k)+1) ≤ 1/(2n+1)`. Substituting `t = (y - 1)/(y + 1)` for a real `y ≥ 1`, for which
`(1 + t)/(1 - t) = y`, gives a two-sided enclosure of `log y`.

## Main results

* `CollatzPosDens.log_mem_atanh_partialSum_of_lt_one`: the enclosure of
  `log (1 + t) - log (1 - t)` for `0 ≤ t < 1`.
* `CollatzPosDens.log_mem_atanh_partialSum`: the enclosure of `log y` for `y ≥ 1`.

## Implementation notes

The bounds are read off the power series `Real.hasSum_log_sub_log_of_abs_lt_one`: the tail
after `n` terms is nonnegative and is dominated termwise by a geometric series, rather than
obtained by integrating the finite geometric identity for `1/(1 - s²)` over `[0, t]`. Mathlib's
`Real.log_div_le_sum_range_add` gives the upper bound without the factor `1/(2n+1)`.
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- For `0 ≤ t < 1`, the partial sums of the series of `log (1 + t) - log (1 - t)` bound it from
below, and the partial sum plus `2 t^(2n+1) / ((2n+1)(1 - t²))` bounds it from above. -/
theorem log_mem_atanh_partialSum_of_lt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1)
    (n : ℕ) :
    2 * ∑ j ∈ range n, 1 / (2 * (j : ℝ) + 1) * t ^ (2 * j + 1) ≤ log (1 + t) - log (1 - t) ∧
    log (1 + t) - log (1 - t) ≤ 2 * ∑ j ∈ range n, 1 / (2 * (j : ℝ) + 1) * t ^ (2 * j + 1) +
      2 / ((2 * n + 1) * (1 - t ^ 2)) * t ^ (2 * n + 1) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := t) ((abs_of_nonneg h0).trans_lt h1)
  have ht := (hasSum_nat_add_iff' n).mpr hs
  have hsum : ∑ i ∈ range n, 2 * (1 / (2 * (i : ℝ) + 1)) * t ^ (2 * i + 1) =
      2 * ∑ j ∈ range n, 1 / (2 * (j : ℝ) + 1) * t ^ (2 * j + 1) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [hsum] at ht
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - t ^ 2 := by linarith
  constructor
  · have := hasSum_le (fun k => by positivity) hasSum_zero ht
    linarith
  · have hg := (hasSum_geometric_of_lt_one (by positivity) ht2).mul_left
      (2 / (2 * (n : ℝ) + 1) * t ^ (2 * n + 1))
    have := hasSum_le (fun k => ?_) ht hg
    · have e : 2 / ((2 * (n : ℝ) + 1) * (1 - t ^ 2)) * t ^ (2 * n + 1) =
          2 / (2 * (n : ℝ) + 1) * t ^ (2 * n + 1) * (1 - t ^ 2)⁻¹ := by
        field_simp
      linarith
    · have e : t ^ (2 * (k + n) + 1) = t ^ (2 * n + 1) * (t ^ 2) ^ k := by ring
      rw [e]
      have hk : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * (n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
      calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * (t ^ (2 * n + 1) * (t ^ 2) ^ k)
          ≤ 2 * (1 / (2 * (n : ℝ) + 1)) * (t ^ (2 * n + 1) * (t ^ 2) ^ k) := by gcongr
        _ = _ := by ring

/-- **Inverse hyperbolic tangent enclosure.** For real `y ≥ 1` and `n : ℕ`, with
`t = (y - 1)/(y + 1)`,
`2 ∑_{j<n} t^(2j+1)/(2j+1) ≤ log y ≤ 2 ∑_{j<n} t^(2j+1)/(2j+1) + 2 t^(2n+1)/((2n+1)(1 - t²))`. -/
@[collatz_pos_dens "lem_s02_atanh_bounds"]
theorem log_mem_atanh_partialSum {y : ℝ} (hy : 1 ≤ y) (n : ℕ) :
    2 * ∑ j ∈ range n, 1 / (2 * (j : ℝ) + 1) * ((y - 1) / (y + 1)) ^ (2 * j + 1) ≤ log y ∧
    log y ≤ 2 * ∑ j ∈ range n, 1 / (2 * (j : ℝ) + 1) * ((y - 1) / (y + 1)) ^ (2 * j + 1) +
      2 / ((2 * n + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) * ((y - 1) / (y + 1)) ^ (2 * n + 1) := by
  have hy1 : 0 < y + 1 := by linarith
  have h0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) hy1.le
  have h1 : (y - 1) / (y + 1) < 1 := (div_lt_one hy1).mpr (by linarith)
  have hlog : log (1 + (y - 1) / (y + 1)) - log (1 - (y - 1) / (y + 1)) = log y := by
    have ha : 1 + (y - 1) / (y + 1) = 2 * y / (y + 1) := by
      field_simp
      ring
    have hb : 1 - (y - 1) / (y + 1) = 2 / (y + 1) := by
      field_simp
      ring
    rw [ha, hb, ← log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [← hlog]
  exact log_mem_atanh_partialSum_of_lt_one h0 h1 n

end CollatzPosDens
