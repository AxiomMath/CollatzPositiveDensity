/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The selector cutoff generation

This file defines the cutoff generation `j_e := 29 ∈ ℕ`, which separates the generations
`j < j_e` from the generations `j ≥ j_e`.

## Main definitions

* `CollatzPosDens.selEnd`: the cutoff generation `j_e := 29`.

## Main results

* `CollatzPosDens.selEnd_eq`: `j_e = 29`.

## Implementation notes

The constant is reducible, so that statements written with the literal `29` unify with
statements written with the symbol.
-/

@[expose] public section

namespace CollatzPosDens

/-- The cutoff generation `j_e := 29 ∈ ℕ`. -/
@[collatz_pos_dens "def_sel_end"]
abbrev selEnd : ℕ := 29

/-- The value of `j_e`. -/
theorem selEnd_eq : selEnd = 29 := rfl

end CollatzPosDens
