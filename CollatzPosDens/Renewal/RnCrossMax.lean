/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnCrossE
public import CollatzPosDens.Renewal.RnCrossP
public import CollatzPosDens.Renewal.RnBinomRow
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Maxima of the crossing weights

For every integer `G ≥ 1024` and all `j, j' ∈ ℤ`, the straddle and boundary weights at height
`t = G - 4` satisfy
$$\mathsf p_{G-4}(j) + \mathsf e_{G-4}(j') < \frac{17}{10\sqrt G}.$$

Both weights are binomial probabilities of a single row, so the maximal binomial weight of a row
bounds their squares: `p_t(j)² ≤ 8 / (3G - 7)` (row `t + 1`) and
`e_t(j')² ≤ 2 / (256 (3G - 13))` (row `t - 1`). For `G ≥ 1024` these give
`G p_t(j)² < (41/25)²` and `G e_t(j')² < (3/50)²`, and `41/25 + 3/50 = 17/10`.

## Main results

* `CollatzPosDens.straddleWeight_lt_of_le`: `p_{G-4}(j) < 41 / (25 √G)` for `G ≥ 1024`.
* `CollatzPosDens.boundaryWeight_lt_of_le`: `e_{G-4}(j') < 3 / (50 √G)` for `G ≥ 1024`.
* `CollatzPosDens.straddleWeight_add_boundaryWeight_lt`: the sum bound.

## Implementation notes

The integer `G ≥ 1024` is taken in `ℕ`, so that `G - 4` is the natural-number height of the
weights; truncated subtraction is harmless since `G ≥ 4`. The square roots are removed by
comparing squares: for `c > 0`, `G x² < c²` implies `x < c / √G`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `0 < c`, `0 < G` and `G x² < c²`, then `x < c / √G`. -/
private lemma lt_div_sqrt_of_sq_mul_lt {x c G : ℝ} (hc : 0 < c) (hG : 0 < G)
    (h : x ^ 2 * G < c ^ 2) : x < c / Real.sqrt G := by
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  rw [lt_div_iff₀ hs]
  exact lt_of_pow_lt_pow_left₀ 2 hc.le (by rwa [mul_pow, Real.sq_sqrt hG.le])

/-- The straddle weight at height `G - 4` is below `41 / (25 √G)` for `G ≥ 1024`. -/
theorem straddleWeight_lt_of_le {G : ℕ} (hG : 1024 ≤ G) (j : ℤ) :
    straddleWeight (G - 4) j < 41 / (25 * Real.sqrt G) := by
  have hGR : (1024 : ℝ) ≤ G := by exact_mod_cast hG
  rw [← div_div]
  refine lt_div_sqrt_of_sq_mul_lt (by norm_num) (by linarith) ?_
  -- `p_t(j) = 2 X` with `X` a binomial probability of row `t + 1 = G - 3`.
  have hp : straddleWeight (G - 4) j ^ 2 ≤ 8 / (3 * G - 7) := by
    unfold straddleWeight
    split_ifs with hj
    · have hb := choose_div_two_pow_sq_le (G - 4 + 1) (2 * j.toNat + 1)
      have hcast : ((G - 4 + 1 : ℕ) : ℝ) = G - 3 := by
        rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast, show (2 : ℝ) ^ (G - 4 + 1) = 2 * 2 ^ (G - 4) by rw [pow_succ']] at hb
      have hpos : (0 : ℝ) < 2 ^ (G - 4) := by positivity
      set c : ℝ := (((G - 4 + 1).choose (2 * j.toNat + 1) : ℕ) : ℝ)
      have heq : (c / 2 ^ (G - 4)) ^ 2 = 4 * (c / (2 * 2 ^ (G - 4))) ^ 2 := by
        field_simp; ring
      rw [heq]
      calc 4 * (c / (2 * 2 ^ (G - 4))) ^ 2 ≤ 4 * (2 / (3 * (G - 3) + 2)) := by gcongr
        _ = 8 / (3 * G - 7) := by ring
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      have : (0 : ℝ) < 3 * G - 7 := by linarith
      positivity
  calc straddleWeight (G - 4) j ^ 2 * G ≤ 8 / (3 * G - 7) * G := by gcongr
    _ < (41 / 25) ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- The boundary weight at height `G - 4` is below `3 / (50 √G)` for `G ≥ 1024`. -/
theorem boundaryWeight_lt_of_le {G : ℕ} (hG : 1024 ≤ G) (j : ℤ) :
    boundaryWeight (G - 4) j < 3 / (50 * Real.sqrt G) := by
  have hGR : (1024 : ℝ) ≤ G := by exact_mod_cast hG
  rw [← div_div]
  refine lt_div_sqrt_of_sq_mul_lt (by norm_num) (by linarith) ?_
  -- `e_t(j) = Y / 16` with `Y` a binomial probability of row `t - 1 = G - 5`.
  have he : boundaryWeight (G - 4) j ^ 2 ≤ 2 / (256 * (3 * G - 13)) := by
    by_cases hj : 1 ≤ j
    · rw [boundaryWeight_eq_div_sixteen (by omega) hj]
      have hb := choose_div_two_pow_sq_le (G - 4 - 1) (2 * j.toNat - 1)
      have hcast : ((G - 4 - 1 : ℕ) : ℝ) = G - 5 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast] at hb
      set c : ℝ := (((G - 4 - 1).choose (2 * j.toNat - 1) : ℕ) : ℝ)
      have hpos : (0 : ℝ) < 2 ^ (G - 4 - 1) := by positivity
      have heq : (c / 16 / 2 ^ (G - 4 - 1)) ^ 2 = (c / 2 ^ (G - 4 - 1)) ^ 2 / 256 := by
        field_simp; ring
      rw [heq]
      calc (c / 2 ^ (G - 4 - 1)) ^ 2 / 256 ≤ (2 / (3 * (G - 5) + 2)) / 256 := by gcongr
        _ = 2 / (256 * (3 * G - 13)) := by
          rw [show (3 : ℝ) * (G - 5) + 2 = 3 * G - 13 by ring, div_div, mul_comm]
    · rw [boundaryWeight_of_not (by omega)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      have : (0 : ℝ) < 3 * G - 13 := by linarith
      positivity
  calc boundaryWeight (G - 4) j ^ 2 * G ≤ 2 / (256 * (3 * G - 13)) * G := by gcongr
    _ < (3 / 50) ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- **Maxima of the crossing weights**: for every integer `G ≥ 1024` and all `j, j' ∈ ℤ`,
`straddleWeight (G - 4) j + boundaryWeight (G - 4) j' < 17 / (10 √G)`. -/
@[collatz_pos_dens "lem_rn_cross_max"]
theorem straddleWeight_add_boundaryWeight_lt {G : ℕ} (hG : 1024 ≤ G) (j j' : ℤ) :
    straddleWeight (G - 4) j + boundaryWeight (G - 4) j' < 17 / (10 * Real.sqrt G) := by
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega))
  calc straddleWeight (G - 4) j + boundaryWeight (G - 4) j'
      < 41 / (25 * Real.sqrt G) + 3 / (50 * Real.sqrt G) :=
        add_lt_add (straddleWeight_lt_of_le hG j) (boundaryWeight_lt_of_le hG j')
    _ = 17 / (10 * Real.sqrt G) := by field_simp; ring

end CollatzPosDens
