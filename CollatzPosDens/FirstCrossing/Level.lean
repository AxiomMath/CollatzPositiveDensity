/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The residue levels `k_n`

This file defines the residue levels: for `n ∈ ℕ`,
$$k_n = \lfloor b_n / 4 \rfloor,$$
where `b_n` is the `n`-th scale. The level is a natural number.

## Main definitions

* `CollatzPosDens.level`: the residue levels `k_n = ⌊b_n / 4⌋`.

## Main results

* `CollatzPosDens.level_def`: the unfolding `k_n = b_n / 4`.
* `CollatzPosDens.four_mul_level_le`: `4 k_n ≤ b_n`.
* `CollatzPosDens.scale_lt_four_mul_level_add_four`: `b_n < 4 k_n + 4`.
* `CollatzPosDens.scale_le_eight_mul_level`: `b_n ≤ 8 k_n`.
* `CollatzPosDens.level_monotone`: the levels are nondecreasing.
* `CollatzPosDens.level_zero`: `k_0 = 4136`.
* `CollatzPosDens.four136_le_level`, `CollatzPosDens.two_le_level`, `CollatzPosDens.level_pos`:
  `4136 ≤ k_n`, so every level is at least `2` and positive.

## Implementation notes

Division is natural-number division, which is the floor `⌊b_n / 4⌋`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Residue level** `k_n = ⌊b_n / 4⌋`, where `b_n` is the `n`-th scale. -/
@[collatz_pos_dens "def_level"]
def level (n : ℕ) : ℕ := scale n / 4

/-- The level `k_n` unfolds to `b_n / 4`. -/
theorem level_def (n : ℕ) : level n = scale n / 4 := rfl

/-- Four times the level is at most the scale: `4 k_n ≤ b_n`. -/
theorem four_mul_level_le (n : ℕ) : 4 * level n ≤ scale n :=
  Nat.mul_div_le (scale n) 4

/-- The scale is less than `4 k_n + 4`. -/
theorem scale_lt_four_mul_level_add_four (n : ℕ) : scale n < 4 * level n + 4 := by
  rw [level_def]
  omega

/-- The levels are nondecreasing. -/
theorem level_monotone : Monotone level :=
  fun _ _ h => Nat.div_le_div_right (scale_monotone h)

/-- The first level is `k_0 = ⌊16544/4⌋ = 4136`. -/
theorem level_zero : level 0 = 4136 := by
  rw [level_def, scale_zero]

/-- Every level is at least `k_0 = 4136`. -/
theorem four136_le_level (n : ℕ) : 4136 ≤ level n :=
  level_zero ▸ level_monotone (Nat.zero_le n)

/-- Every level is at least `2`. -/
theorem two_le_level (n : ℕ) : 2 ≤ level n :=
  le_trans (by norm_num) (four136_le_level n)

/-- Every level is positive. -/
theorem level_pos (n : ℕ) : 0 < level n :=
  zero_lt_two.trans_le (two_le_level n)

/-- The scale is at most eight times the level: `b_n ≤ 8 k_n`. -/
theorem scale_le_eight_mul_level (n : ℕ) : scale n ≤ 8 * level n := by
  have := sixteen544_le_scale n
  rw [level_def]
  omega

end CollatzPosDens
