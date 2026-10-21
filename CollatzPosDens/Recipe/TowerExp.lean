/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The tower exponent `E_tow`

This file defines the tower exponent `E_tow := 163`, the exponent at the top of the tower constant
`D_A = tow_3(E_tow) = 2 ^ 2 ^ 2 ^ E_tow` (`CollatzPosDens.towerConstant`).

## Main definitions

* `CollatzPosDens.towerExp`: the tower exponent `E_tow := 163`.

## Main results

* `CollatzPosDens.towerExp_def`: `E_tow = 163`.

## Implementation notes

The exponent is reducible, so that `tower 3 towerExp` and `tower 3 163` unify reducibly; the
tower itself stays irreducible.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The tower exponent `E_tow := 163 ∈ ℕ`. -/
@[collatz_pos_dens "def_tower_exp"]
abbrev towerExp : ℕ := 163

/-- The value of the tower exponent. -/
theorem towerExp_def : towerExp = 163 := rfl

end CollatzPosDens
