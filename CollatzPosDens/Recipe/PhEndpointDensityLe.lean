/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.TargetExp
public import CollatzPosDens.Recipe.Tower
public import CollatzPosDens.Recipe.TowerConstant
public import CollatzPosDens.Recipe.TowerExp

/-!
# The endpoint density in terms of the tower constant

The endpoint density `c_end(t) = 1 / (t ^ (25/11) · 2 ^ 2 ^ 2 ^ 163)` is a real number, where
`25/11 = κ_t` is the target exponent and the real number `2 ^ 2 ^ 2 ^ 163` is a natural-number
power of the real `2`. That power is the image in `ℝ` of the natural number
`D_A = tow_3(E_tow) = 2 ^ 2 ^ 2 ^ E_tow`, the tower constant, with tower exponent `E_tow = 163`,
since the cast `ℕ → ℝ` preserves powers. Hence `c_end(t) = 1 / (t ^ κ_t · D_A)`, and in
particular `c_end(t) ≤ 1 / (t ^ κ_t · D_A)`.

## Main results

* `CollatzPosDens.collatzDensityDep_eq`: `c_end(t) = 1 / (t ^ κ_t · D_A)`.
* `CollatzPosDens.collatzDensityDep_le`: `c_end(t) ≤ 1 / (t ^ κ_t · D_A)`.

## Implementation notes

The inequality holds for every natural `t`, since the two sides are equal, so no hypothesis
`t ≥ 1` is imposed.
-/

@[expose] public section

namespace CollatzPosDens

/-- The endpoint density in terms of the tower constant:
`c_end(t) = 1 / (t ^ κ_t · D_A)`, with `κ_t` the target exponent and `D_A` the tower constant. -/
theorem collatzDensityDep_eq (t : ℕ) :
    collatzDensityDep t = 1 / ((t : ℝ) ^ (targetExp : ℝ) * (towerConstant : ℝ)) := by
  have h : (towerConstant : ℝ) = (2 : ℝ) ^ 2 ^ 2 ^ 163 := by
    rw [towerConstant_def, towerExp_def, Nat.cast_pow, Nat.cast_ofNat]
  rw [h, collatzDensityDep, targetExp_cast]

/-- For every natural `t`, the endpoint density satisfies `c_end(t) ≤ 1 / (t ^ κ_t · D_A)` in
`ℝ`, with `κ_t` the target exponent and `D_A` the tower constant. -/
@[collatz_pos_dens "lem_ph_endpoint_density_le"]
theorem collatzDensityDep_le (t : ℕ) :
    collatzDensityDep t ≤ 1 / ((t : ℝ) ^ (targetExp : ℝ) * (towerConstant : ℝ)) :=
  (collatzDensityDep_eq t).le

end CollatzPosDens
