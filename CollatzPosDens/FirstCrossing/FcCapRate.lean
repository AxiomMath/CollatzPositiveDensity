/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.Varsigma

/-!
# Decay of the cap term

The overshoot caps `K_j = 16 + ⌊j/32⌋` grow slowly enough that the cap term `2^{-(K_j+1)}`
decays at least as fast as the deficit rate: for every `j`,
$$2^{-(K_j+1)} \le 2^{-16}\,\varsigma^j,$$
where `ς = 𝗀^{-9/8}` and `𝗀 = 101/100`. The key numerical input is `ς^{32} = (100/101)^{36} ≥ 1/2`,
i.e. the exact comparison `101^{36} < 2 · 100^{36}`.

## Main results

* `CollatzPosDens.two_zpow_neg_cap_succ_le`: `2^{-(K_j+1)} ≤ 2^{-16} ς^j`.

## Implementation notes

Write `j = 32 q + r` with `r < 32`, so `K_j + 1 = 17 + q`. Since `ς ≤ 1`,
`ς^j ≥ ς^{32(q+1)} = (ς^{32})^{q+1} ≥ 2^{-(q+1)}`, which avoids real exponents `2^{-j/32}`
altogether.
-/

@[expose] public section

namespace CollatzPosDens

/-- `1/2 ≤ ς ^ 32`, i.e. `101 ^ 36 ≤ 2 · 100 ^ 36`. -/
theorem two_zpow_neg_cap_succ_le_aux : (1 / 2 : ℝ) ≤ deficitRate ^ 32 := by
  rw [show 32 = 8 * 4 from rfl, pow_mul, deficitRate_pow_eight]; norm_num

/-- **Decay of the cap term.** For every `j`, `2^{-(K_j+1)} ≤ 2^{-16} ς^j`. -/
@[collatz_pos_dens "lem_fc_cap_rate"]
theorem two_zpow_neg_cap_succ_le (j : ℕ) :
    (2 : ℝ) ^ (-((cap j : ℤ) + 1)) ≤ (2 : ℝ) ^ (-16 : ℤ) * deficitRate ^ j := by
  have hj : deficitRate ^ (32 * (j / 32 + 1)) ≤ deficitRate ^ j :=
    pow_le_pow_of_le_one deficitRate_nonneg deficitRate_le_one (by omega)
  have hq : (1 / 2 : ℝ) ^ (j / 32 + 1) ≤ deficitRate ^ (32 * (j / 32 + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) two_zpow_neg_cap_succ_le_aux _
  have hL : (2 : ℝ) ^ (-((cap j : ℤ) + 1)) =
      (1 / 2 : ℝ) ^ 16 * (1 / 2 : ℝ) ^ (j / 32 + 1) := by
    rw [← pow_add, show -((cap j : ℤ) + 1) = -((16 + (j / 32 + 1) : ℕ) : ℤ) by
      rw [cap_def]; push_cast; ring, zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [hL, show (2 : ℝ) ^ (-16 : ℤ) = (1 / 2) ^ 16 by norm_num]
  exact mul_le_mul_of_nonneg_left (hq.trans hj) (by positivity)

end CollatzPosDens
