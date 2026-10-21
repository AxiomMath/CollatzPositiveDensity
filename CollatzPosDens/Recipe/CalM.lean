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
# The seed allowance `𝓜(t)`

For an endpoint parameter `t ≥ 1`, the seed allowance is the natural number
$$\mathcal{M}(t) := 2^{\,5 \cdot 3^{q_*}}\, t \in \mathbb{N},$$
where `q_*` is the conductor. It is linear in `t`: `𝓜(t) = t 𝓜(1)`.

## Main definitions

* `CollatzPosDens.seedBoundOf`: the expression `2 ^ (5 * 3 ^ q) * t` in parameters `t`, `q`.
* `CollatzPosDens.seedBound`: the seed allowance `𝓜(t)`, its value at `q = q_*`.

## Main results

* `CollatzPosDens.seedBound_def`: the defining formula `𝓜(t) = 2 ^ (5 * 3 ^ q_*) * t`.
* `CollatzPosDens.seedBound_eq_two_pow`: `𝓜(t) = t * 2 ^ (5 * 3 ^ q_*)`.
* `CollatzPosDens.seedBound_eq_mul`: `𝓜(t) = t * 𝓜(1)`.
* `CollatzPosDens.seedBound_pos`: `0 < 𝓜(t)` for `0 < t`.
* `CollatzPosDens.le_seedBound`: `t ≤ 𝓜(t)`.

## Implementation notes

The seed allowance is far too large to be evaluated, so `seedBound` is irreducible and is meant
to be used through `seedBound_def`. It is the value of the parametric expression `seedBoundOf`,
whose elementary bounds are proved with the parameters left symbolic, so that the kernel is never
asked to evaluate a power of `q_*`. The endpoint `t` is any natural number; the bounds that need
`t ≥ 1` take `0 < t` as a hypothesis.
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `2 ^ (5 * 3 ^ q) * t` with parameters `t` and `q`; the seed allowance
`𝓜(t)` is `seedBoundOf t q_*`. -/
def seedBoundOf (t q : ℕ) : ℕ := 2 ^ (5 * 3 ^ q) * t

/-- The defining formula of `seedBoundOf`. -/
theorem seedBoundOf_def (t q : ℕ) : seedBoundOf t q = 2 ^ (5 * 3 ^ q) * t := rfl

/-- `seedBoundOf t q = t * seedBoundOf 1 q`. -/
theorem seedBoundOf_eq_mul (t q : ℕ) : seedBoundOf t q = t * seedBoundOf 1 q := by
  rw [seedBoundOf_def, seedBoundOf_def, mul_one, Nat.mul_comm]

/-- `seedBoundOf t q` is positive for `0 < t`. -/
theorem seedBoundOf_pos {t : ℕ} (ht : 0 < t) (q : ℕ) : 0 < seedBoundOf t q :=
  Nat.mul_pos (Nat.pow_pos (by norm_num)) ht

/-- `t ≤ seedBoundOf t q`. -/
theorem le_seedBoundOf (t q : ℕ) : t ≤ seedBoundOf t q :=
  Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))

/-- `seedBoundOf t` is monotone in the parameter `q`. -/
theorem seedBoundOf_monotone (t : ℕ) : Monotone (seedBoundOf t) := fun _ _ h =>
  Nat.mul_le_mul_right t (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by norm_num) h)))

/-- **The seed allowance** `𝓜(t) := 2 ^ (5 * 3 ^ q_*) * t ∈ ℕ`, where `q_*` is the conductor. -/
@[collatz_pos_dens "def_calM", irreducible]
def seedBound (t : ℕ) : ℕ := seedBoundOf t conductor

/-- `𝓜(t)` is `seedBoundOf` at `q = q_*`. -/
theorem seedBound_eq_seedBoundOf (t : ℕ) : seedBound t = seedBoundOf t conductor := by
  unfold seedBound
  rfl

/-- The defining formula `𝓜(t) = 2 ^ (5 * 3 ^ q_*) * t`. -/
theorem seedBound_def (t : ℕ) : seedBound t = 2 ^ (5 * 3 ^ conductor) * t :=
  (seedBound_eq_seedBoundOf t).trans (seedBoundOf_def _ _)

/-- `𝓜(t) = t * 2 ^ (5 * 3 ^ q_*)`. -/
theorem seedBound_eq_two_pow (t : ℕ) : seedBound t = t * 2 ^ (5 * 3 ^ conductor) :=
  (seedBound_def t).trans (Nat.mul_comm _ _)

/-- The seed allowance is linear in the endpoint: `𝓜(t) = t * 𝓜(1)`. -/
theorem seedBound_eq_mul (t : ℕ) : seedBound t = t * seedBound 1 := by
  rw [seedBound_eq_seedBoundOf, seedBound_eq_seedBoundOf]
  exact seedBoundOf_eq_mul t conductor

/-- The seed allowance is positive for `0 < t`. -/
theorem seedBound_pos {t : ℕ} (ht : 0 < t) : 0 < seedBound t :=
  (seedBound_eq_seedBoundOf t) ▸ seedBoundOf_pos ht _

/-- `1 ≤ 𝓜(t)` for `0 < t`. -/
theorem one_le_seedBound {t : ℕ} (ht : 0 < t) : 1 ≤ seedBound t :=
  seedBound_pos ht

/-- `t ≤ 𝓜(t)`. -/
theorem le_seedBound (t : ℕ) : t ≤ seedBound t :=
  (seedBound_eq_seedBoundOf t) ▸ le_seedBoundOf t _

end CollatzPosDens
