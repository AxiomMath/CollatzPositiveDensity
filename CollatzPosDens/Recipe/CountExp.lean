/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The count exponent `λ_U`

This file fixes the natural number `λ_U := 207`, the count exponent: a lower bound of the form
`2^{-λ_U}` is stated in terms of it.

## Main definitions

* `CollatzPosDens.countExp`: the count exponent `λ_U := 207`.

## Main results

* `CollatzPosDens.countExp_def`: `λ_U = 207`.

## Implementation notes

The exponent is reducible, so statements written with the literal and with the symbol unify
reducibly.
-/

@[expose] public section

namespace CollatzPosDens

/-- The count exponent `λ_U := 207 ∈ ℕ`. -/
@[collatz_pos_dens "def_count_exp"]
abbrev countExp : ℕ := 207

/-- The value of the count exponent. -/
theorem countExp_def : countExp = 207 := rfl

end CollatzPosDens
