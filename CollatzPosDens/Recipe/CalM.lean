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
# The seed allowance `𝓜(s)`

For an endpoint parameter `s ≥ 1`, this file defines the seed allowance of the recipe,
$$\mathcal{M}(s) := s \cdot 4^{\,19 + 2 \cdot 3^{q_*}} \in \mathbb{N},$$
where `q_*` is the conductor. It is linear in `s`: `𝓜(s) = s 𝓜(1)`.

## Main definitions

* `CollatzPosDens.seedBoundOf`: the expression `s * 4 ^ (19 + 2 * 3 ^ q)` in parameters `s`, `q`.
* `CollatzPosDens.seedBound`: the seed allowance `𝓜(s)`, its value at `q = q_*`.

## Main results

* `CollatzPosDens.seedBound_def`: the defining formula `𝓜(s) = s * 4 ^ (19 + 2 * 3 ^ q_*)`.
* `CollatzPosDens.seedBound_eq_two_pow`: `𝓜(s) = s * 2 ^ (38 + 4 * 3 ^ q_*)`.
* `CollatzPosDens.seedBound_eq_mul`: `𝓜(s) = s * 𝓜(1)`.
* `CollatzPosDens.seedBound_pos`: `0 < 𝓜(s)` for `0 < s`.
* `CollatzPosDens.four_pow_nineteen_le_seedBound`: `4 ^ 19 ≤ 𝓜(s)` for `0 < s`.

## Implementation notes

The seed allowance is far too large to be evaluated, so `seedBound` is irreducible and is meant
to be used through `seedBound_def`. It is the value of the parametric expression `seedBoundOf`,
whose elementary bounds are proved with the parameters left symbolic. The endpoint `s` is any
natural number; the bounds that need `s ≥ 1` take `0 < s` as a hypothesis.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `s * 4 ^ (19 + 2 * 3 ^ q)` with parameters `s` and `q`; the seed allowance
`𝓜(s)` is `seedBoundOf s q_*`. -/
def seedBoundOf (s q : ℕ) : ℕ := s * 4 ^ (19 + 2 * 3 ^ q)

/-- The defining formula of `seedBoundOf`. -/
theorem seedBoundOf_def (s q : ℕ) : seedBoundOf s q = s * 4 ^ (19 + 2 * 3 ^ q) := rfl

/-- `seedBoundOf s q` is positive for `0 < s`. -/
theorem seedBoundOf_pos {s : ℕ} (hs : 0 < s) (q : ℕ) : 0 < seedBoundOf s q :=
  Nat.mul_pos hs (Nat.pow_pos (by norm_num))

/-- `4 ^ 19 ≤ seedBoundOf s q` for `0 < s`. -/
theorem four_pow_nineteen_le_seedBoundOf {s : ℕ} (hs : 0 < s) (q : ℕ) :
    4 ^ 19 ≤ seedBoundOf s q :=
  calc 4 ^ 19 ≤ 4 ^ (19 + 2 * 3 ^ q) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    _ ≤ s * 4 ^ (19 + 2 * 3 ^ q) := Nat.le_mul_of_pos_left _ hs

/-- `seedBoundOf s` is monotone in the parameter `q`. -/
theorem seedBoundOf_monotone (s : ℕ) : Monotone (seedBoundOf s) := fun _ _ h =>
  Nat.mul_le_mul_left s (Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) h)) _))

/-- **The seed allowance** `𝓜(s) := s * 4 ^ (19 + 2 * 3 ^ q_*) ∈ ℕ`, where `q_*` is the
conductor. It is irreducible so that tactics never try to evaluate it; use `seedBound_def`. -/
@[collatz_pos_dens "def_calM", irreducible]
noncomputable def seedBound (s : ℕ) : ℕ := seedBoundOf s conductor

/-- `𝓜(s)` is `seedBoundOf` at `q = q_*`. -/
theorem seedBound_eq_seedBoundOf (s : ℕ) : seedBound s = seedBoundOf s conductor := by
  unfold seedBound
  rfl

/-- The defining formula `𝓜(s) = s * 4 ^ (19 + 2 * 3 ^ q_*)`. -/
theorem seedBound_def (s : ℕ) : seedBound s = s * 4 ^ (19 + 2 * 3 ^ conductor) :=
  (seedBound_eq_seedBoundOf s).trans (seedBoundOf_def _ _)

/-- `𝓜(s) = s * 2 ^ (38 + 4 * 3 ^ q_*)`. -/
theorem seedBound_eq_two_pow (s : ℕ) : seedBound s = s * 2 ^ (38 + 4 * 3 ^ conductor) := by
  rw [seedBound_def, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

/-- The seed allowance is linear in the endpoint: `𝓜(s) = s * 𝓜(1)`. -/
theorem seedBound_eq_mul (s : ℕ) : seedBound s = s * seedBound 1 := by
  rw [seedBound_def, seedBound_def, one_mul]

/-- The seed allowance is positive for `0 < s`. -/
theorem seedBound_pos {s : ℕ} (hs : 0 < s) : 0 < seedBound s :=
  (seedBound_eq_seedBoundOf s) ▸ seedBoundOf_pos hs _

/-- `1 ≤ 𝓜(s)` for `0 < s`. -/
theorem one_le_seedBound {s : ℕ} (hs : 0 < s) : 1 ≤ seedBound s :=
  seedBound_pos hs

/-- `4 ^ 19 ≤ 𝓜(s)` for `0 < s`. -/
theorem four_pow_nineteen_le_seedBound {s : ℕ} (hs : 0 < s) : 4 ^ 19 ≤ seedBound s :=
  (seedBound_eq_seedBoundOf s) ▸ four_pow_nineteen_le_seedBoundOf hs _

/-- `s ≤ 𝓜(s)`. -/
theorem le_seedBound (s : ℕ) : s ≤ seedBound s := by
  rw [seedBound_def]
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num))

end CollatzPosDens
