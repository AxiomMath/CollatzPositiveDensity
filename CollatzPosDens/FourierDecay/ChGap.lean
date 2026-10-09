/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Linarith
public import CollatzPosDens.Attr

/-!
# A truncated-subtraction gap inequality

For natural numbers `n` and `j ≥ 1` we have `n ≤ 8 j max(⌊n/2⌋ ∸ j, 1)`.

## Main results

* `CollatzPosDens.le_eight_mul_max_half_sub`: the inequality `n ≤ 8 * j * max (n / 2 - j) 1`.

## Implementation notes

The inequality holds trivially for `n = 0`, so no hypothesis `n ≥ 1` is imposed.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `j ≥ 1`, `n ≤ 8 j max(⌊n/2⌋ ∸ j, 1)`. -/
@[collatz_pos_dens "lem_ch_gap"]
theorem le_eight_mul_max_half_sub (n : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    n ≤ 8 * j * max (n / 2 - j) 1 := by
  obtain ⟨J, hJ⟩ : ∃ J, J = n / 2 := ⟨_, rfl⟩
  have hnJ : n ≤ 2 * J + 1 := by omega
  rw [← hJ]
  rcases lt_or_ge j J with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, J = j + k + 1 := ⟨J - j - 1, by omega⟩
    rw [show j + k + 1 - j = k + 1 by omega, max_eq_left (by omega)]
    nlinarith
  · rw [Nat.sub_eq_zero_of_le h, max_eq_right zero_le_one]
    omega

end CollatzPosDens
