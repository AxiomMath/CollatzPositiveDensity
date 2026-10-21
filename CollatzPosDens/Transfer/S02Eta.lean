/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02StageRate
public import CollatzPosDens.Transfer.S02Theta

/-!
# The event coefficients `η_i(ι)`

For each Fourier parameter index `ι ∈ {o, b}` (`FIndex`) and each `0 ≤ i ≤ r_*(ι)` (`rStar`),
the event coefficient `η_i(ι) ∈ ℚ` is the factor by which the surviving mass is multiplied after
the first `i` trace intervals. At the original index it is the entry weight (`thetaEn`),
`η_i(o) := θ^en_i = (77/100)^i`. At the bootstrap index, where `r_*(b) = 3`, it is the entry of
`(η_0(b), η_1(b), η_2(b), η_3(b)) := (1, 77/100, b_*, b_*²)`, with `b_* = 333407/10⁶` the
stopped-stage mass (`stageRate`): the intervals `0` and `1` keep the entry weights `θ^en_0` and
`θ^en_1`, the interval `2` carries one full stopped stage and the terminal interval two.

## Main definitions

* `CollatzPosDens.eventCoeff`: the event coefficient `η_i(ι) : ℚ`.

## Main results

* `CollatzPosDens.eventCoeff_o`: `η_i(o) = θ^en_i`.
* `CollatzPosDens.eventCoeff_b_zero`, …, `CollatzPosDens.eventCoeff_b_three`: the four values
  `1, 77/100, b_*, b_*²` at the bootstrap index.
* `CollatzPosDens.eventCoeff_rStar_o`, `CollatzPosDens.eventCoeff_rStar_b`: the terminal
  coefficients `η_{r_*(o)}(o) = (77/100)^10` and `η_{r_*(b)}(b) = b_*²`.
* `CollatzPosDens.eventCoeff_pos`, `CollatzPosDens.eventCoeff_le_one`: `0 < η_i(ι) ≤ 1`.

## Implementation notes

The coefficients are only meaningful for `0 ≤ i ≤ r_*(ι)`. The definition is total on `ℕ`: at
the bootstrap index it is extended by `η_{i+2}(b) := b_*^{i+1}`, which gives the values `b_*`
and `b_*²` at `i = 2, 3`; the extension is never used for `i > r_*(b)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The event coefficients `η_i(ι) ∈ ℚ`: `η_i(o) := θ^en_i` (`thetaEn i`), and
`(η_0(b), η_1(b), η_2(b), η_3(b)) := (1, 77/100, b_*, b_*²)` with `b_* = stageRate`, extended by
`η_{i+2}(b) := b_*^{i+1}`. -/
@[collatz_pos_dens "def_s02_eta"]
def eventCoeff : FIndex → ℕ → ℚ
  | .o, i => thetaEn i
  | .b, 0 => 1
  | .b, 1 => 77 / 100
  | .b, i + 2 => stageRate ^ (i + 1)

/-- At the original index the event coefficient is the entry weight: `η_i(o) = θ^en_i`. -/
@[simp] theorem eventCoeff_o (i : ℕ) : eventCoeff .o i = thetaEn i := rfl

/-- At the original index, `η_i(o) = (77/100)^i`. -/
theorem eventCoeff_o_eq (i : ℕ) : eventCoeff .o i = (77 / 100) ^ i := thetaEn_eq i

/-- The event coefficient `η_0(b) = 1`. -/
@[simp] theorem eventCoeff_b_zero : eventCoeff .b 0 = 1 := rfl

/-- The event coefficient `η_1(b) = 77/100`. -/
@[simp] theorem eventCoeff_b_one : eventCoeff .b 1 = 77 / 100 := rfl

/-- The event coefficient `η_2(b) = b_*`. -/
@[simp] theorem eventCoeff_b_two : eventCoeff .b 2 = stageRate := pow_one _

/-- The event coefficient `η_3(b) = b_*²`. -/
@[simp] theorem eventCoeff_b_three : eventCoeff .b 3 = stageRate ^ 2 := rfl

/-- The terminal event coefficient at the original index: `η_{r_*(o)}(o) = (77/100)^10`. -/
theorem eventCoeff_rStar_o : eventCoeff .o (rStar .o) = (77 / 100) ^ 10 := by
  rw [rStar_o, eventCoeff_o_eq]

/-- The terminal event coefficient at the bootstrap index: `η_{r_*(b)}(b) = b_*²`. -/
theorem eventCoeff_rStar_b : eventCoeff .b (rStar .b) = stageRate ^ 2 := by
  rw [rStar_b, eventCoeff_b_three]

/-- The event coefficients are positive. -/
theorem eventCoeff_pos (ι : FIndex) (i : ℕ) : 0 < eventCoeff ι i := by
  match ι, i with
  | .o, i => exact thetaEn_pos i
  | .b, 0 => norm_num
  | .b, 1 => norm_num
  | .b, i + 2 => exact pow_pos stageRate_pos _

/-- The event coefficients are nonnegative. -/
theorem eventCoeff_nonneg (ι : FIndex) (i : ℕ) : 0 ≤ eventCoeff ι i :=
  (eventCoeff_pos ι i).le

/-- The event coefficients are at most one. -/
theorem eventCoeff_le_one (ι : FIndex) (i : ℕ) : eventCoeff ι i ≤ 1 := by
  match ι, i with
  | .o, i => exact thetaEn_le_one i
  | .b, 0 => norm_num
  | .b, 1 => norm_num
  | .b, i + 2 => exact pow_le_one₀ stageRate_nonneg stageRate_lt_one.le

end CollatzPosDens
