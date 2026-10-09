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
# The fixed modulus exponent `m`

This file defines the fixed modulus exponent
$$m := \bigl\lfloor (2^{39}\,\mathcal{M}\,C)^{8/9} \bigr\rfloor + 1 \in \mathbb{N},$$
where `𝓜` is the seed bound and `C` is the mixing coefficient. It is the least natural number
strictly exceeding `(2^{39} 𝓜 C)^{8/9}`.

## Main definitions

* `CollatzPosDens.modulusExponentOf`: the expression `⌊x ^ (8/9)⌋₊ + 1` in a real
  parameter `x`.
* `CollatzPosDens.modulusExponent`: the exponent `m`, its value at `x = 2^39 𝓜 C`.

## Main results

* `CollatzPosDens.modulusExponent_def`: the defining formula of `m`.
* `CollatzPosDens.lt_modulusExponent`: `(2^39 𝓜 C)^{8/9} < m`.
* `CollatzPosDens.modulusExponent_sub_one_le`: `m - 1 ≤ (2^39 𝓜 C)^{8/9}`.
* `CollatzPosDens.modulusExponent_le_iff`: `m ≤ r ↔ (2^39 𝓜 C)^{8/9} < r`, i.e. `m` is the
  least such `r`.
* `CollatzPosDens.one_le_modulusExponent`: `1 ≤ m`.

## Implementation notes

The power is Mathlib's real power `Real.rpow`, applied to the positive real `2^39 𝓜 C`, and the
floor is the natural floor `⌊·⌋₊`. The exponent `m` is far too large to be evaluated, so
`modulusExponent` is irreducible and is meant to be used through `modulusExponent_def` and the
bounds of this file, which are proved for the parametric expression `modulusExponentOf`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `⌊x ^ (8/9)⌋₊ + 1` with real parameter `x`; the fixed modulus exponent `m`
is `modulusExponentOf (2^39 𝓜 C)`. -/
noncomputable def modulusExponentOf (x : ℝ) : ℕ := ⌊x ^ (8 / 9 : ℝ)⌋₊ + 1

/-- The defining formula of `modulusExponentOf`. -/
theorem modulusExponentOf_def (x : ℝ) :
    modulusExponentOf x = ⌊x ^ (8 / 9 : ℝ)⌋₊ + 1 := rfl

/-- `x ^ (8/9) < modulusExponentOf x`. -/
theorem lt_modulusExponentOf (x : ℝ) : x ^ (8 / 9 : ℝ) < modulusExponentOf x := by
  rw [modulusExponentOf_def]
  push_cast
  exact Nat.lt_floor_add_one _

/-- `modulusExponentOf x - 1 ≤ x ^ (8/9)` when `0 ≤ x`. -/
theorem modulusExponentOf_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    ((modulusExponentOf x - 1 : ℕ) : ℝ) ≤ x ^ (8 / 9 : ℝ) := by
  rw [modulusExponentOf_def, Nat.add_sub_cancel]
  exact Nat.floor_le (Real.rpow_nonneg hx _)

/-- For `0 ≤ x`, `modulusExponentOf x` is the least `r : ℕ` with `x ^ (8/9) < r`. -/
theorem modulusExponentOf_le_iff {x : ℝ} (hx : 0 ≤ x) {r : ℕ} :
    modulusExponentOf x ≤ r ↔ x ^ (8 / 9 : ℝ) < r := by
  rw [modulusExponentOf_def, Nat.add_one_le_iff, Nat.floor_lt (Real.rpow_nonneg hx _)]

/-- `1 ≤ modulusExponentOf x`. -/
theorem one_le_modulusExponentOf (x : ℝ) : 1 ≤ modulusExponentOf x :=
  Nat.le_add_left _ _

/-- The base `2^39 𝓜 C` of the fixed modulus exponent is positive. -/
theorem modulusExponent_base_pos : 0 < (2 : ℝ) ^ 39 * seedBound * mixingConst := by
  have := seedBound_pos
  have := mixingConst_pos
  positivity

/-- **The fixed modulus exponent** `m := ⌊(2^39 𝓜 C)^{8/9}⌋₊ + 1 ∈ ℕ`, where `𝓜` is the seed
bound and `C` the mixing coefficient. -/
@[collatz_pos_dens "def_mconst", irreducible]
noncomputable def modulusExponent : ℕ :=
  modulusExponentOf ((2 : ℝ) ^ 39 * seedBound * mixingConst)

/-- `m` is `modulusExponentOf` at `x = 2^39 𝓜 C`. -/
theorem modulusExponent_eq_modulusExponentOf :
    modulusExponent = modulusExponentOf ((2 : ℝ) ^ 39 * seedBound * mixingConst) := by
  unfold modulusExponent
  rfl

/-- The defining formula `m = ⌊(2^39 𝓜 C)^{8/9}⌋₊ + 1`. -/
theorem modulusExponent_def :
    modulusExponent = ⌊((2 : ℝ) ^ 39 * seedBound * mixingConst) ^ (8 / 9 : ℝ)⌋₊ + 1 :=
  modulusExponent_eq_modulusExponentOf.trans (modulusExponentOf_def _)

/-- `(2^39 𝓜 C)^{8/9} < m`. -/
theorem lt_modulusExponent :
    ((2 : ℝ) ^ 39 * seedBound * mixingConst) ^ (8 / 9 : ℝ) < modulusExponent :=
  modulusExponent_eq_modulusExponentOf ▸ lt_modulusExponentOf _

/-- `m - 1 ≤ (2^39 𝓜 C)^{8/9}`. -/
theorem modulusExponent_sub_one_le :
    ((modulusExponent - 1 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ 39 * seedBound * mixingConst) ^ (8 / 9 : ℝ) :=
  modulusExponent_eq_modulusExponentOf ▸
    modulusExponentOf_sub_one_le modulusExponent_base_pos.le

/-- `m ≤ r` if and only if `(2^39 𝓜 C)^{8/9} < r`. -/
theorem modulusExponent_le_iff {r : ℕ} :
    modulusExponent ≤ r ↔ ((2 : ℝ) ^ 39 * seedBound * mixingConst) ^ (8 / 9 : ℝ) < r :=
  modulusExponent_eq_modulusExponentOf ▸ modulusExponentOf_le_iff modulusExponent_base_pos.le

/-- `1 ≤ m`. -/
theorem one_le_modulusExponent : 1 ≤ modulusExponent :=
  modulusExponent_eq_modulusExponentOf ▸ one_le_modulusExponentOf _

/-- `0 < m`. -/
theorem modulusExponent_pos : 0 < modulusExponent :=
  one_le_modulusExponent

end CollatzPosDens
