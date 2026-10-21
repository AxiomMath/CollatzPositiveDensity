/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Dentry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The entry weights `θ^en_i`

For `i ∈ ℕ` the entry weight is the rational number `θ^en_i := (1 - d_entry)^i`, where
`d_entry = CollatzPosDens.dEntry`. It is a geometric sequence with ratio `1 - d_entry = 77/100`;
it is positive, at most one, and strictly decreasing in `i`.

## Main definitions

* `CollatzPosDens.thetaEn`: the entry weight `θ^en_i := (1 - d_entry)^i : ℚ`.

## Main results

* `CollatzPosDens.thetaEn_eq`: `θ^en_i = (77/100)^i`.
* `CollatzPosDens.thetaEn_zero`, `CollatzPosDens.thetaEn_succ`, `CollatzPosDens.thetaEn_add`:
  `θ^en_0 = 1`, `θ^en_{i+1} = (1 - d_entry) θ^en_i`, `θ^en_{i+j} = θ^en_i θ^en_j`.
* `CollatzPosDens.thetaEn_pos`, `CollatzPosDens.thetaEn_le_one`: `0 < θ^en_i ≤ 1`.
* `CollatzPosDens.thetaEn_strictAnti`: `i ↦ θ^en_i` is strictly decreasing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The entry weight `θ^en_i := (1 - d_entry)^i ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_theta"]
def thetaEn (i : ℕ) : ℚ := (1 - dEntry) ^ i

/-- The entry weight as an explicit power of `77/100`. -/
theorem thetaEn_eq (i : ℕ) : thetaEn i = (77 / 100) ^ i := by
  rw [thetaEn, one_sub_dEntry]

/-- The entry weight at stage zero is one. -/
@[simp]
theorem thetaEn_zero : thetaEn 0 = 1 := by simp [thetaEn]

/-- The entry weights satisfy `θ^en_{i+1} = (1 - d_entry) θ^en_i`. -/
theorem thetaEn_succ (i : ℕ) : thetaEn (i + 1) = (1 - dEntry) * thetaEn i := by
  simp only [thetaEn, pow_succ']

/-- The entry weights are multiplicative: `θ^en_{i+j} = θ^en_i θ^en_j`. -/
theorem thetaEn_add (i j : ℕ) : thetaEn (i + j) = thetaEn i * thetaEn j := by
  simp only [thetaEn, pow_add]

/-- The entry weights are positive. -/
theorem thetaEn_pos (i : ℕ) : 0 < thetaEn i := by
  rw [thetaEn_eq]; positivity

/-- The entry weights are at most one. -/
theorem thetaEn_le_one (i : ℕ) : thetaEn i ≤ 1 := by
  rw [thetaEn_eq]; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The entry weights are strictly decreasing in the stage. -/
theorem thetaEn_strictAnti : StrictAnti thetaEn := by
  intro i j hij
  simp only [thetaEn_eq]
  exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hij

end CollatzPosDens
