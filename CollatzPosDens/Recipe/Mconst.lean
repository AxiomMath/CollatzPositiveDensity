/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Transfer.MixingConst

/-!
# The fixed modulus exponent `m(s)`

For an endpoint parameter `s ≥ 1`, this file defines the fixed modulus exponent of the recipe,
$$m(s) := \bigl\lfloor (2^{39}\,\mathcal{M}(s)\,C)^{2/3} \bigr\rfloor + 1 \in \mathbb{N},$$
where `𝓜(s)` is the seed allowance and `C` is the mixing coefficient. It is the least natural
number strictly exceeding `(2^{39} 𝓜(s) C)^{2/3}`.

## Main definitions

* `CollatzPosDens.modulusExponentOf`: the expression `⌊x ^ (2/3)⌋₊ + 1` in a real
  parameter `x`.
* `CollatzPosDens.modulusExponent`: the exponent `m(s)`, its value at `x = 2^39 𝓜(s) C`.

## Main results

* `CollatzPosDens.modulusExponent_def`: the defining formula of `m(s)`.
* `CollatzPosDens.lt_modulusExponent`: `(2^39 𝓜(s) C)^{2/3} < m(s)`.
* `CollatzPosDens.modulusExponent_sub_one_le`: `m(s) - 1 ≤ (2^39 𝓜(s) C)^{2/3}`.
* `CollatzPosDens.modulusExponent_le_iff`: `m(s) ≤ r ↔ (2^39 𝓜(s) C)^{2/3} < r`, i.e. `m(s)`
  is the least such `r`.
* `CollatzPosDens.one_le_modulusExponent`: `1 ≤ m(s)`.

## Implementation notes

The power is Mathlib's real power `Real.rpow`, applied to the real `2^39 𝓜(s) C` (positive for
`s ≥ 1`), and the floor is the natural floor `⌊·⌋₊`. The exponent `m(s)` is far too large to be
evaluated, so `modulusExponent` is irreducible and is meant to be used through
`modulusExponent_def` and the bounds of this file, which are proved for the parametric
expression `modulusExponentOf`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `⌊x ^ (2/3)⌋₊ + 1` with real parameter `x`; the fixed modulus exponent `m`
is `modulusExponentOf (2^39 𝓜 C)`. -/
noncomputable def modulusExponentOf (x : ℝ) : ℕ := ⌊x ^ (2 / 3 : ℝ)⌋₊ + 1

/-- The defining formula of `modulusExponentOf`. -/
theorem modulusExponentOf_def (x : ℝ) :
    modulusExponentOf x = ⌊x ^ (2 / 3 : ℝ)⌋₊ + 1 := rfl

/-- `x ^ (2/3) < modulusExponentOf x`. -/
theorem lt_modulusExponentOf (x : ℝ) : x ^ (2 / 3 : ℝ) < modulusExponentOf x := by
  rw [modulusExponentOf_def]
  push_cast
  exact Nat.lt_floor_add_one _

/-- `modulusExponentOf x - 1 ≤ x ^ (2/3)` when `0 ≤ x`. -/
theorem modulusExponentOf_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    ((modulusExponentOf x - 1 : ℕ) : ℝ) ≤ x ^ (2 / 3 : ℝ) := by
  rw [modulusExponentOf_def, Nat.add_sub_cancel]
  exact Nat.floor_le (Real.rpow_nonneg hx _)

/-- For `0 ≤ x`, `modulusExponentOf x` is the least `r : ℕ` with `x ^ (2/3) < r`. -/
theorem modulusExponentOf_le_iff {x : ℝ} (hx : 0 ≤ x) {r : ℕ} :
    modulusExponentOf x ≤ r ↔ x ^ (2 / 3 : ℝ) < r := by
  rw [modulusExponentOf_def, Nat.add_one_le_iff, Nat.floor_lt (Real.rpow_nonneg hx _)]

/-- `1 ≤ modulusExponentOf x`. -/
theorem one_le_modulusExponentOf (x : ℝ) : 1 ≤ modulusExponentOf x :=
  Nat.le_add_left _ _

/-- The base `2^39 𝓜(s) C` of the fixed modulus exponent is positive for `0 < s`. -/
theorem modulusExponent_base_pos {s : ℕ} (hs : 0 < s) :
    0 < (2 : ℝ) ^ 39 * seedBound s * mixingConst := by
  have : (0 : ℝ) < seedBound s := by exact_mod_cast seedBound_pos hs
  have := mixingConst_pos
  positivity

/-- The base `2^39 𝓜(s) C` of the fixed modulus exponent is nonnegative. -/
theorem modulusExponent_base_nonneg (s : ℕ) :
    0 ≤ (2 : ℝ) ^ 39 * seedBound s * mixingConst := by
  have := mixingConst_pos
  positivity

/-- **The fixed modulus exponent** `m(s) := ⌊(2^39 𝓜(s) C)^{2/3}⌋₊ + 1 ∈ ℕ`, where `𝓜(s)` is
the seed allowance and `C` the mixing coefficient. It is irreducible so that tactics never try to
evaluate it; use `modulusExponent_def`. -/
@[collatz_pos_dens "def_mconst", irreducible]
noncomputable def modulusExponent (s : ℕ) : ℕ :=
  modulusExponentOf ((2 : ℝ) ^ 39 * seedBound s * mixingConst)

/-- `m(s)` is `modulusExponentOf` at `x = 2^39 𝓜(s) C`. -/
theorem modulusExponent_eq_modulusExponentOf (s : ℕ) :
    modulusExponent s = modulusExponentOf ((2 : ℝ) ^ 39 * seedBound s * mixingConst) := by
  unfold modulusExponent
  rfl

/-- The defining formula `m(s) = ⌊(2^39 𝓜(s) C)^{2/3}⌋₊ + 1`. -/
theorem modulusExponent_def (s : ℕ) :
    modulusExponent s = ⌊((2 : ℝ) ^ 39 * seedBound s * mixingConst) ^ (2 / 3 : ℝ)⌋₊ + 1 :=
  (modulusExponent_eq_modulusExponentOf s).trans (modulusExponentOf_def _)

/-- `(2^39 𝓜(s) C)^{2/3} < m(s)`. -/
theorem lt_modulusExponent (s : ℕ) :
    ((2 : ℝ) ^ 39 * seedBound s * mixingConst) ^ (2 / 3 : ℝ) < modulusExponent s :=
  (modulusExponent_eq_modulusExponentOf s) ▸ lt_modulusExponentOf _

/-- `m(s) - 1 ≤ (2^39 𝓜(s) C)^{2/3}`. -/
theorem modulusExponent_sub_one_le (s : ℕ) :
    ((modulusExponent s - 1 : ℕ) : ℝ) ≤
      ((2 : ℝ) ^ 39 * seedBound s * mixingConst) ^ (2 / 3 : ℝ) :=
  (modulusExponent_eq_modulusExponentOf s) ▸
    modulusExponentOf_sub_one_le (modulusExponent_base_nonneg s)

/-- `m(s) ≤ r` if and only if `(2^39 𝓜(s) C)^{2/3} < r`. -/
theorem modulusExponent_le_iff (s : ℕ) {r : ℕ} :
    modulusExponent s ≤ r ↔ ((2 : ℝ) ^ 39 * seedBound s * mixingConst) ^ (2 / 3 : ℝ) < r :=
  (modulusExponent_eq_modulusExponentOf s) ▸
    modulusExponentOf_le_iff (modulusExponent_base_nonneg s)

/-- `1 ≤ m(s)`. -/
theorem one_le_modulusExponent (s : ℕ) : 1 ≤ modulusExponent s :=
  (modulusExponent_eq_modulusExponentOf s) ▸ one_le_modulusExponentOf _

/-- `0 < m(s)`. -/
theorem modulusExponent_pos (s : ℕ) : 0 < modulusExponent s :=
  one_le_modulusExponent s

end CollatzPosDens
