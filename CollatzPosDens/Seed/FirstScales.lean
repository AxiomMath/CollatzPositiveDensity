/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The first six scales

We compute the first six values of the scale sequence `b_j = CollatzPosDens.scale j`, defined
by `b_0 = 9` and `b_{j+1} = b_j + e_{b_j}`, where `e_b = CollatzPosDens.eb b` is the scale
increment. Since `e_9 = e_10 = e_11 = e_12 = 1`, and `e_13 = 1` (the only `k ≥ ⌈13/100⌉ = 1`
with `9 · 3^13 · 16^k < 4^14` is `k = 1`, as `9 · 3^13 · 16 = 229582512 < 268435456 = 4^14`
while `9 · 3^13 · 16^2 > 4^14`), the first six scales are
`(b_0, …, b_5) = (9, 10, 11, 12, 13, 14)`.

## Main results

* `CollatzPosDens.eb_thirteen`: `e_13 = 1`.
* `CollatzPosDens.scale_first_six`: `(b_0, b_1, b_2, b_3, b_4, b_5) = (9, 10, 11, 12, 13, 14)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale increment at `b = 13` is `e_13 = 1`. -/
theorem eb_thirteen : eb 13 = 1 := by
  obtain ⟨⟨_, _, h1⟩, hmax⟩ :=
    eb_isGreatest le_rfl (by norm_num) ⟨1, by norm_num, by norm_num, by norm_num⟩
  have hge : 1 ≤ eb 13 := hmax ⟨by norm_num, by norm_num, by norm_num⟩
  by_contra hne
  have : 9 * 3 ^ 13 * 16 ^ 2 ≤ 9 * 3 ^ 13 * 16 ^ eb 13 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- The first six scales are `(b_0, b_1, b_2, b_3, b_4, b_5) = (9, 10, 11, 12, 13, 14)`. -/
@[collatz_pos_dens "lem_s05_first_scales"]
theorem scale_first_six :
    (scale 0, scale 1, scale 2, scale 3, scale 4, scale 5) = (9, 10, 11, 12, 13, 14) := by
  have h1 : scale 1 = 10 := by rw [scale_succ, scale_zero, eb_of_le_twelve (by norm_num)]
  have h2 : scale 2 = 11 := by rw [scale_succ, h1, eb_of_le_twelve (by norm_num)]
  have h3 : scale 3 = 12 := by rw [scale_succ, h2, eb_of_le_twelve (by norm_num)]
  have h4 : scale 4 = 13 := by rw [scale_succ, h3, eb_of_le_twelve (by norm_num)]
  have h5 : scale 5 = 14 := by rw [scale_succ, h4, eb_thirteen]
  rw [scale_zero, h1, h2, h3, h4, h5]

end CollatzPosDens
