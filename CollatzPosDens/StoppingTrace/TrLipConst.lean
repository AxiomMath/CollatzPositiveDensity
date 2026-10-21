/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Lipschitz constants of the capped factors

For an integer `c`, write `a_j = 2^j - 1` for `j ∈ ℕ`, and define the rational constant
`ℓ_c = 44 / (7 (c - 1)) · ∑_{j=0}^{c-2} |a_j - a_{⌊(c-2)/2⌋}|` for `3 ≤ c ≤ 16`, and `ℓ_c = 0`
otherwise. The sum is the total deviation of the frequencies `a_0, …, a_{c-2}` from the central
frequency `a_{⌊(c-2)/2⌋}`, and the factor `44/7` is a rational upper bound for `2π`.

## Main definitions

* `CollatzPosDens.trLipConst`: the rational constant `ℓ_c`.

## Main results

* `CollatzPosDens.trLipConst_of_mem`, `CollatzPosDens.trLipConst_of_not_mem`: the two cases.
* `CollatzPosDens.trLipConst_nonneg`: `0 ≤ ℓ_c`.
* `CollatzPosDens.trLipConst_four`, …, `CollatzPosDens.trLipConst_seven`: the values
  `ℓ_4 = 44/7`, `ℓ_5 = 99/7`, `ℓ_6 = 132/5`, `ℓ_7 = 154/3`.

## Implementation notes

The constant is computable and rational-valued, so that each value is evaluated by `norm_num`
after unfolding the finite sum.
The index `j` runs over `Finset.range (c.toNat - 1)`, which is `{0, …, c - 2}` for `c ≥ 2`, and the
central index `⌊(c-2)/2⌋` is the natural-number quotient `(c.toNat - 2) / 2`, which agrees with it
for `c ≥ 2`; in particular both agree with the formula above on the range `3 ≤ c ≤ 16`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The Lipschitz constant of the capped factor:
`ℓ_c = 44 / (7 (c - 1)) · ∑_{j=0}^{c-2} |a_j - a_{⌊(c-2)/2⌋}|` with `a_j = 2^j - 1` if
`3 ≤ c ≤ 16`, and `0` otherwise. -/
@[collatz_pos_dens "def_tr_lip_const"]
def trLipConst (c : ℤ) : ℚ :=
  if 3 ≤ c ∧ c ≤ 16 then
    44 / (7 * ((c : ℚ) - 1)) *
      ∑ j ∈ Finset.range (c.toNat - 1),
        |((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ ((c.toNat - 2) / 2) - 1)|
  else 0

/-- For `3 ≤ c ≤ 16`, `trLipConst c` is given by the defining formula. -/
theorem trLipConst_of_mem {c : ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) :
    trLipConst c = 44 / (7 * ((c : ℚ) - 1)) *
      ∑ j ∈ Finset.range (c.toNat - 1),
        |((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ ((c.toNat - 2) / 2) - 1)| :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h₁, h₂⟩)

/-- Outside the range `3 ≤ c ≤ 16`, `trLipConst c = 0`. -/
theorem trLipConst_of_not_mem {c : ℤ} (h : ¬(3 ≤ c ∧ c ≤ 16)) : trLipConst c = 0 :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- The Lipschitz constant is nonnegative. -/
theorem trLipConst_nonneg (c : ℤ) : 0 ≤ trLipConst c := by
  unfold trLipConst
  split_ifs with h
  · have : (0 : ℚ) < (c : ℚ) - 1 := by
      have : (3 : ℚ) ≤ c := by exact_mod_cast h.1
      linarith
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · exact le_rfl

/-- `ℓ_4 = 44/7`. -/
theorem trLipConst_four : trLipConst 4 = 44 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- `ℓ_5 = 99/7`. -/
theorem trLipConst_five : trLipConst 5 = 99 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- `ℓ_6 = 132/5`. -/
theorem trLipConst_six : trLipConst 6 = 132 / 5 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- `ℓ_7 = 154/3`. -/
theorem trLipConst_seven : trLipConst 7 = 154 / 3 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

end CollatzPosDens
