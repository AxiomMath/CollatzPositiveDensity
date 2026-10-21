/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Tower
public import CollatzPosDens.Recipe.TowerExp

/-!
# The tower constant `D_A`

This file defines the tower constant
$$D_A = \mathrm{tow}_3(E_{\mathrm{tow}}) = 2^{2^{2^{E_{\mathrm{tow}}}}} \in \mathbb{N},$$
the tower of three twos topped by the tower exponent `E_tow = towerExp` (`= 163`).

## Main definitions

* `CollatzPosDens.towerConstant`: the tower constant `D_A = tow_3(E_tow)`.

## Main results

* `CollatzPosDens.towerConstant_eq_tower`: `D_A = tow_3(E_tow)`.
* `CollatzPosDens.towerConstant_def`: `D_A = 2 ^ 2 ^ 2 ^ E_tow`.
* `CollatzPosDens.towerConstant_eq_two_pow`: `D_A = 2 ^ tow_2(E_tow)`.
* `CollatzPosDens.towerConstant_pos`: `0 < D_A`.
* `CollatzPosDens.tower_three`, `CollatzPosDens.tower_succ_pos`: the unfolded tower of three twos,
  and positivity of a tower of positive height.

## Implementation notes

The constant is far too large to be evaluated, so `towerConstant` is irreducible and is meant to
be used through `towerConstant_def` and `towerConstant_eq_two_pow`, which present it as a power
of two whose exponent is handled symbolically. Facts about `D_A` are derived from statements
about `tow_k(t)` with `t` left as a variable, since the kernel would otherwise attempt to evaluate
the closed exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The tower constant** `D_A = tow_3(E_tow) = 2 ^ 2 ^ 2 ^ E_tow ∈ ℕ`, with `E_tow = towerExp`.
-/
@[collatz_pos_dens "def_tower_constant", irreducible]
def towerConstant : ℕ := tower 3 towerExp

/-- `D_A` is the tower `tow_3(E_tow)`. -/
theorem towerConstant_eq_tower : towerConstant = tower 3 towerExp := by
  unfold towerConstant
  rfl

/-- A tower of three twos: `tow_3(t) = 2 ^ 2 ^ 2 ^ t`. -/
theorem tower_three (t : ℕ) : tower 3 t = 2 ^ 2 ^ 2 ^ t := rfl

/-- A tower of positive height is positive: `0 < tow_{k+1}(t)`. -/
theorem tower_succ_pos (k t : ℕ) : 0 < tower (k + 1) t := by
  rw [tower_succ]
  exact Nat.two_pow_pos _

/-- `D_A` is a power of two: `D_A = 2 ^ tow_2(E_tow)`. -/
theorem towerConstant_eq_two_pow : towerConstant = 2 ^ tower 2 towerExp := by
  rw [towerConstant_eq_tower, tower_succ]

/-- The defining formula `D_A = 2 ^ 2 ^ 2 ^ E_tow`. -/
theorem towerConstant_def : towerConstant = 2 ^ 2 ^ 2 ^ towerExp :=
  towerConstant_eq_tower.trans (tower_three towerExp)

/-- `D_A` is positive. -/
theorem towerConstant_pos : 0 < towerConstant := by
  rw [towerConstant_eq_tower]
  exact tower_succ_pos 2 towerExp

end CollatzPosDens
