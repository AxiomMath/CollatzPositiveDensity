/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The exceptional allowance of a block of offsets

For `v ∈ ℕ` the exceptional allowance is
`Exc(v) = 9 (25/27)^(136 (v+1)) + [v ≥ 1] (8^v (25/27)^(136 (v+1)) + e^(-14 (v+1)))`,
where `[v ≥ 1]` is `1` if `v ≥ 1` and `0` if `v = 0`. It bounds the probability of the
exceptional events met within a block of `v` offsets, and these allowances are summable.

## Main definitions

* `CollatzPosDens.c3Exc`: the allowance `Exc(v)`, a real number.

## Main results

* `CollatzPosDens.c3Exc_zero`: `Exc(0) = 9 (25/27)^136`.
* `CollatzPosDens.c3Exc_of_one_le`: the closed form of `Exc(v)` for `v ≥ 1`.
* `CollatzPosDens.c3Exc_succ`: the closed form of `Exc(v + 1)`.
* `CollatzPosDens.c3Exc_pos`: `0 < Exc(v)`.

## Implementation notes

The Iverson bracket `[v ≥ 1]` is rendered as an `if 1 ≤ v then … else 0`. The value is taken
in `ℝ`, since it is summed over finite sets of offsets and compared with probabilities.

## References

* [Mazur, *Collatz positive density*], §10.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exceptional allowance
`Exc(v) = 9 (25/27)^(136 (v+1)) + [v ≥ 1] (8^v (25/27)^(136 (v+1)) + e^(-14 (v+1)))`. -/
@[collatz_pos_dens "def_c3_exc"]
noncomputable def c3Exc (v : ℕ) : ℝ :=
  9 * (25 / 27 : ℝ) ^ (136 * (v + 1)) +
    if 1 ≤ v then
      8 ^ v * (25 / 27 : ℝ) ^ (136 * (v + 1)) + Real.exp (-14 * ((v : ℝ) + 1))
    else 0

/-- `Exc(0) = 9 (25/27)^136`. -/
theorem c3Exc_zero : c3Exc 0 = 9 * (25 / 27 : ℝ) ^ 136 := by
  simp [c3Exc]

/-- For `v ≥ 1`, `Exc(v) = 9 (25/27)^(136 (v+1)) + 8^v (25/27)^(136 (v+1)) + e^(-14 (v+1))`. -/
theorem c3Exc_of_one_le {v : ℕ} (hv : 1 ≤ v) :
    c3Exc v = 9 * (25 / 27 : ℝ) ^ (136 * (v + 1)) +
      (8 ^ v * (25 / 27 : ℝ) ^ (136 * (v + 1)) + Real.exp (-14 * ((v : ℝ) + 1))) := by
  simp [c3Exc, hv]

/-- The closed form of `Exc(v + 1)`. -/
theorem c3Exc_succ (v : ℕ) :
    c3Exc (v + 1) = 9 * (25 / 27 : ℝ) ^ (136 * (v + 2)) +
      (8 ^ (v + 1) * (25 / 27 : ℝ) ^ (136 * (v + 2)) +
        Real.exp (-14 * ((v : ℝ) + 2))) := by
  have h : ((v + 1 : ℕ) : ℝ) + 1 = (v : ℝ) + 2 := by push_cast; ring
  rw [c3Exc_of_one_le (Nat.le_add_left 1 v), h]

/-- `0 < Exc(v)`. -/
theorem c3Exc_pos (v : ℕ) : 0 < c3Exc v := by
  unfold c3Exc
  split_ifs <;> positivity

/-- `0 ≤ Exc(v)`. -/
theorem c3Exc_nonneg (v : ℕ) : 0 ≤ c3Exc v :=
  (c3Exc_pos v).le

end CollatzPosDens
