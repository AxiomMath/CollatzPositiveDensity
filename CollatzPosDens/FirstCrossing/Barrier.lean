/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.FirstCrossing.Rb

/-!
# The barrier `H_{b,u}(s)`

For natural numbers `b`, `s` and an integer `u` this file defines the integer
$$H_{b,u}(s) = 2b + \mathsf{B}\bigl((s-b)_+\bigr) - \mathsf{B}\bigl((b-s)_+\bigr) + u - r_b,$$
where `v₊ = max(v, 0)`, `B(j) = ⌈j log₂ 3⌉` and `r_b` is the shift radius `CollatzPosDens.rb b`.
At most one of `(s - b)₊` and `(b - s)₊` is nonzero, so `H_{b,u}(s)` is
`2b + B(s - b) + u - r_b` for `s ≥ b` and `2b - B(b - s) + u - r_b` for `s ≤ b`.

## Main definitions

* `CollatzPosDens.barrier`: the barrier `H_{b,u}(s)`.

## Main results

* `CollatzPosDens.barrier_def`: the unfolding of `H_{b,u}(s)`.
* `CollatzPosDens.barrier_of_le`: `H_{b,u}(s) = 2b + B(s - b) + u - r_b` for `b ≤ s`.
* `CollatzPosDens.barrier_of_ge`: `H_{b,u}(s) = 2b - B(b - s) + u - r_b` for `s ≤ b`.
* `CollatzPosDens.barrier_self`: `H_{b,u}(b) = 2b + u - r_b`.
* `CollatzPosDens.barrier_rb_eq_barrierRb`: `H_{b,r_b}(s)` equals its computable form
  `barrierRb b s`.

## Implementation notes

The source takes integers `b, s ≥ 0`; here they are natural numbers, and the positive parts
`(s - b)₊` and `(b - s)₊` are the truncated subtractions `s - b` and `b - s` in `ℕ`.

## References

* [Mazur, *Collatz positive density*], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The barrier `H_{b,u}(s) = 2b + B((s - b)₊) - B((b - s)₊) + u - r_b`, where the positive
parts are truncated subtractions in `ℕ`. -/
@[collatz_pos_dens "def_barrier"]
noncomputable def barrier (b : ℕ) (u : ℤ) (s : ℕ) : ℤ :=
  2 * (b : ℤ) + ceilLog3 (s - b) - ceilLog3 (b - s) + u - rb b

/-- Unfolding lemma for `barrier`. -/
theorem barrier_def (b : ℕ) (u : ℤ) (s : ℕ) :
    barrier b u s = 2 * (b : ℤ) + ceilLog3 (s - b) - ceilLog3 (b - s) + u - rb b := rfl

/-- Above the level, `H_{b,u}(s) = 2b + B(s - b) + u - r_b`. -/
theorem barrier_of_le {b s : ℕ} (u : ℤ) (h : b ≤ s) :
    barrier b u s = 2 * (b : ℤ) + ceilLog3 (s - b) + u - rb b := by
  rw [barrier_def, Nat.sub_eq_zero_of_le h, ceilLog3_zero]
  ring

/-- Below the level, `H_{b,u}(s) = 2b - B(b - s) + u - r_b`. -/
theorem barrier_of_ge {b s : ℕ} (u : ℤ) (h : s ≤ b) :
    barrier b u s = 2 * (b : ℤ) - ceilLog3 (b - s) + u - rb b := by
  rw [barrier_def, Nat.sub_eq_zero_of_le h, ceilLog3_zero]
  ring

/-- At the level itself, `H_{b,u}(b) = 2b + u - r_b`. -/
@[simp]
theorem barrier_self (b : ℕ) (u : ℤ) : barrier b u b = 2 * (b : ℤ) + u - rb b := by
  rw [barrier_of_le u le_rfl, Nat.sub_self, ceilLog3_zero]
  ring

/-- The centred barrier `H_{b,r_b}(s)` equals its computable form `barrierRb b s`. -/
theorem barrier_rb_eq_barrierRb (b s : ℕ) : barrier b (rb b) s = barrierRb b s := by
  rw [barrier_def, ceilLog3_eq_ceilLog3Nat, ceilLog3_eq_ceilLog3Nat, barrierRb]; ring

end CollatzPosDens
