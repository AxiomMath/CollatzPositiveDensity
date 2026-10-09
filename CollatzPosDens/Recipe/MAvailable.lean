/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.Clog

/-!
# The modulus exponent is an available level

If $n \ge 200\max(\mathrm{lg}(m) - 1, 0)$ then $1 \le m \le k_n$, where `m` is `modulusExponent`,
`b_n` is `scale n` and `k_n = ⌊b_n / 4⌋` is `level n`. By Bernoulli's inequality
$\mathsf g^{200} = (101/100)^{200} \ge 3 \ge 2$, so the geometric growth of the scales from
$b_0 = 9$ gives $b_n \ge 9 \cdot 2^{j}$ whenever $n \ge 200 j$. With
$j = \max(\mathrm{lg}(u)-1, 0)$ one has $u \le 2^{\mathrm{lg}(u)} \le 2^{j+1}$, hence
$4u \le 8 \cdot 2^j \le b_n$, and since `u` is an integer, $u \le \lfloor b_n/4 \rfloor = k_n$.

## Main results

* `CollatzPosDens.modulusExponentAvailable_nine_mul_two_pow_le_scale`:
  `9 * 2 ^ j ≤ b_n` whenever `200 * j ≤ n`.
* `CollatzPosDens.modulusExponentAvailable_le_level_of_lg`: for every `u : ℕ`,
  `200 * (lg u - 1) ≤ n` implies `u ≤ k_n`.
* `CollatzPosDens.modulusExponent_available`: `200 * (lg m - 1) ≤ n` implies `1 ≤ m ≤ k_n`.

## Implementation notes

The quantity $\max(\mathrm{lg}(m) - 1, 0)$ is the truncated subtraction `lg m - 1` in `ℕ`. The
upper bound is proved for an arbitrary natural number `u` in place of `m`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scales at least double every `200` steps from `b_0 = 9`: `9 * 2 ^ j ≤ b_n` whenever
`200 * j ≤ n`. -/
theorem modulusExponentAvailable_nine_mul_two_pow_le_scale {j n : ℕ} (h : 200 * j ≤ n) :
    9 * 2 ^ j ≤ scale n := by
  have hB : (2 : ℝ) ≤ (growthRatio : ℝ) ^ 200 := by
    have := one_add_mul_le_pow (a := (1 / 100 : ℝ)) (by norm_num) 200
    rw [growthRatio_cast]
    norm_num at this ⊢
  have hgeo := scale_add_ge_growthRatio_pow_mul 0 (200 * j)
  have key : (9 : ℝ) * 2 ^ j ≤ scale (200 * j) := by
    rw [zero_add] at hgeo
    refine le_trans ?_ hgeo
    rw [scale_zero, pow_mul, mul_comm]
    push_cast
    gcongr
  have hmono : (scale (200 * j) : ℝ) ≤ scale n := by exact_mod_cast scale_monotone h
  exact_mod_cast key.trans hmono

/-- Every natural number `u` is at most the level `k_n` once `n ≥ 200 max(lg u - 1, 0)`. -/
theorem modulusExponentAvailable_le_level_of_lg {u n : ℕ} (h : 200 * (lg u - 1) ≤ n) :
    u ≤ level n := by
  rw [level_def, Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : u ≤ 2 ^ ((lg u - 1) + 1) :=
    (le_two_pow_lg u).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 := modulusExponentAvailable_nine_mul_two_pow_le_scale h
  rw [pow_succ] at h1
  omega

/-- If `n ≥ 200 max(lg m - 1, 0)` then `1 ≤ m ≤ k_n`. -/
@[collatz_pos_dens "lem_m_available"]
theorem modulusExponent_available {n : ℕ} (h : 200 * (lg modulusExponent - 1) ≤ n) :
    1 ≤ modulusExponent ∧ modulusExponent ≤ level n :=
  ⟨one_le_modulusExponent, modulusExponentAvailable_le_level_of_lg h⟩

end CollatzPosDens
