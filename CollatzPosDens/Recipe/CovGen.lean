/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The coverage generation `J_c`

This file defines the coverage generation `J_c := 23000`, a fixed natural number, and records its
value and its positivity.

## Main definitions

* `CollatzPosDens.covGen`: the coverage generation `J_c := 23000`.

## Main results

* `CollatzPosDens.covGen_def`: `J_c = 23000`.
* `CollatzPosDens.covGen_pos`: `0 < J_c`.

## Implementation notes

The generation is reducible, so statements written with the literal and with the symbol unify
reducibly.
-/

@[expose] public section

namespace CollatzPosDens

/-- The coverage generation `J_c := 23000 ∈ ℕ`. -/
@[collatz_pos_dens "def_cov_gen"]
abbrev covGen : ℕ := 23000

/-- The value of the coverage generation. -/
theorem covGen_def : covGen = 23000 := rfl

/-- The coverage generation is positive. -/
theorem covGen_pos : 0 < covGen := by
  rw [covGen_def]; decide

end CollatzPosDens
