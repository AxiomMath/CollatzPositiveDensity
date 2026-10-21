/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnJointPgf
public import CollatzPosDens.Renewal.RnJointPgfValue

/-!
# Value of the vertical generating function of a hold

For real `0 < y < 2` with `y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵ < 1`, the vertical generating
function `𝖵(y) = ∑_{(j, l) ∈ 𝒫} η(j, l) y^l` has the finite value
`((3/16) y⁴ + (1/8) y⁵) / (1 - y² / (2 - y)² + (3/16) y⁴ + (1/8) y⁵)`.

The series defining `𝖵(y)` and the joint generating function `𝖦(1, y)` have the same terms
`η(j, l) y^l = η(j, l) 1^j y^l`, so `𝖵(y) = 𝖦(1, y)`, and the value is that of `𝖦(X, y)` at
`X = 1`.

## Main results

* `CollatzPosDens.holdVpgf_eq_holdJointPgf_one`: `𝖵(y) = 𝖦(1, y)`.
* `CollatzPosDens.holdVpgf_eq`: the closed form of `𝖵(y)`.
* `CollatzPosDens.holdVpgf_ne_top`: under the same hypotheses, `𝖵(y) ≠ ∞`.

## Implementation notes

The closed form is stated as the `ENNReal.ofReal` of the real value, which in particular shows
that the series is finite.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The vertical generating function is the joint generating function at `X = 1`:
`𝖵(y) = 𝖦(1, y)`. -/
theorem holdVpgf_eq_holdJointPgf_one (y : ℝ) : holdVpgf y = holdJointPgf 1 y := by
  simp only [holdVpgf_def, holdJointPgf_def, one_pow, mul_one]

/-- **Value of the vertical generating function.** For `0 < y < 2` with
`y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵ < 1`, the series `𝖵(y)` has the finite sum
`((3/16) y⁴ + (1/8) y⁵) / (1 - y² / (2 - y)² + (3/16) y⁴ + (1/8) y⁵)`. -/
@[collatz_pos_dens "lem_rn_hold_vpgf"]
theorem holdVpgf_eq {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2)
    (h : y ^ 2 / (2 - y) ^ 2 - 3 / 16 * y ^ 4 - 1 / 8 * y ^ 5 < 1) :
    holdVpgf y = ENNReal.ofReal ((3 / 16 * y ^ 4 + 1 / 8 * y ^ 5) /
      (1 - y ^ 2 / (2 - y) ^ 2 + 3 / 16 * y ^ 4 + 1 / 8 * y ^ 5)) := by
  rw [holdVpgf_eq_holdJointPgf_one, holdJointPgf_eq one_pos hy0 hy2 (by rwa [one_mul])]
  congr 2 <;> ring

/-- Under the hypotheses of `holdVpgf_eq`, the series `𝖵(y)` is finite. -/
theorem holdVpgf_ne_top {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2)
    (h : y ^ 2 / (2 - y) ^ 2 - 3 / 16 * y ^ 4 - 1 / 8 * y ^ 5 < 1) : holdVpgf y ≠ ∞ := by
  rw [holdVpgf_eq hy0 hy2 h]
  exact ENNReal.ofReal_ne_top

end CollatzPosDens
