/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Qstar
public import Mathlib.Tactic.NormNum

/-!
# The seed bound `𝓜`

This file defines the seed bound
$$\mathcal{M} := 4^{\,19 + 3^{q_*}} \in \mathbb{N},$$
where `q_*` is the conductor `CollatzPosDens.conductor`. Since the scale `b_0 = scale 0` equals
`9`, the exponent is also `2 b_0 + 1 + 3^{q_*}`.

## Main definitions

* `CollatzPosDens.seedBoundOf`: the expression `4 ^ (19 + 3 ^ q)` in a parameter `q`.
* `CollatzPosDens.seedBound`: the seed bound `𝓜`, its value at `q = q_*`.

## Main results

* `CollatzPosDens.seedBound_def`: the defining formula `𝓜 = 4 ^ (19 + 3 ^ q_*)`.
* `CollatzPosDens.seedBound_eq_scale_zero`: `𝓜 = 4 ^ (2 b_0 + 1 + 3 ^ q_*)`.
* `CollatzPosDens.seedBound_pos`: `0 < 𝓜`.
* `CollatzPosDens.four_pow_nineteen_le_seedBound`: `4 ^ 19 ≤ 𝓜`.
* `CollatzPosDens.sixteen_mul_scale_zero_lt_seedBound`: `16 b_0 < 𝓜`.

## Implementation notes

The seed bound is far too large to be evaluated, so `seedBound` is irreducible and is meant to
be used through `seedBound_def`. It is the value of the parametric expression `seedBoundOf`,
whose elementary bounds are proved with the parameter left symbolic.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `4 ^ (19 + 3 ^ q)` with parameter `q`; the seed bound `𝓜` is
`seedBoundOf q_*`. -/
def seedBoundOf (q : ℕ) : ℕ := 4 ^ (19 + 3 ^ q)

/-- The defining formula of `seedBoundOf`. -/
theorem seedBoundOf_def (q : ℕ) : seedBoundOf q = 4 ^ (19 + 3 ^ q) := rfl

/-- `seedBoundOf q` is positive. -/
theorem seedBoundOf_pos (q : ℕ) : 0 < seedBoundOf q :=
  Nat.pow_pos (by norm_num)

/-- `4 ^ 19 ≤ seedBoundOf q`. -/
theorem four_pow_nineteen_le_seedBoundOf (q : ℕ) : 4 ^ 19 ≤ seedBoundOf q :=
  Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)

/-- `seedBoundOf` is monotone in the parameter. -/
theorem seedBoundOf_monotone : Monotone seedBoundOf := fun _ _ h =>
  Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) h) _)

/-- **The seed bound** `𝓜 := 4 ^ (19 + 3 ^ q_*) ∈ ℕ`, where `q_*` is the conductor.
It is irreducible so that tactics never try to evaluate it; use `seedBound_def`. -/
@[collatz_pos_dens "def_calM", irreducible]
noncomputable def seedBound : ℕ := seedBoundOf conductor

/-- `𝓜` is `seedBoundOf` at `q = q_*`. -/
theorem seedBound_eq_seedBoundOf : seedBound = seedBoundOf conductor := by
  unfold seedBound
  rfl

/-- The defining formula `𝓜 = 4 ^ (19 + 3 ^ q_*)`. -/
theorem seedBound_def : seedBound = 4 ^ (19 + 3 ^ conductor) :=
  seedBound_eq_seedBoundOf.trans (seedBoundOf_def _)

/-- `𝓜 = 4 ^ (2 b_0 + 1 + 3 ^ q_*)`, since `b_0 = 9`. -/
theorem seedBound_eq_scale_zero : seedBound = 4 ^ (2 * scale 0 + 1 + 3 ^ conductor) := by
  rw [seedBound_def, scale_zero]

/-- The seed bound is positive. -/
theorem seedBound_pos : 0 < seedBound :=
  seedBound_eq_seedBoundOf ▸ seedBoundOf_pos _

/-- `4 ^ 19 ≤ 𝓜`. -/
theorem four_pow_nineteen_le_seedBound : 4 ^ 19 ≤ seedBound :=
  seedBound_eq_seedBoundOf ▸ four_pow_nineteen_le_seedBoundOf _

/-- `16 b_0 < 𝓜`. -/
theorem sixteen_mul_scale_zero_lt_seedBound : 16 * scale 0 < seedBound :=
  lt_of_lt_of_le (by rw [scale_zero]; norm_num) four_pow_nineteen_le_seedBound

end CollatzPosDens
