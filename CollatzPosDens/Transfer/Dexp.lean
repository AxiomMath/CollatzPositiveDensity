/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.Positivity

/-!
# The moment threshold `D_exp`

The moment threshold is the natural number `D_exp = 2 ^ 33495`, the threshold beyond which the
exponential-moment estimates apply. Its value is recorded both in `ℕ` and, through its cast, in
an arbitrary semiring.

## Main definitions

* `CollatzPosDens.Dexp`: the moment threshold `D_exp = 2 ^ 33495 : ℕ`.

## Main results

* `CollatzPosDens.Dexp_def`: the value `D_exp = 2 ^ 33495`.
* `CollatzPosDens.Dexp_cast`: the value of `(D_exp : R)` in any semiring, e.g. `ℝ`.
* `CollatzPosDens.Dexp_pos`, `CollatzPosDens.Dexp_cast_pos`: positivity.

## Implementation notes

The definition is irreducible, so that the literal `2 ^ 33495` stays folded: it is neither unfolded
by the elaborator nor evaluated by the kernel. Its value is accessed through `Dexp_def`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The moment threshold `D_exp := 2 ^ 33495 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_Dexp", irreducible]
def Dexp : ℕ := 2 ^ 33495

/-- The value of the moment threshold. -/
theorem Dexp_def : Dexp = 2 ^ 33495 := by
  unfold Dexp
  rfl

/-- The value of the moment threshold cast into a semiring. -/
theorem Dexp_cast {R : Type*} [Semiring R] : (Dexp : R) = 2 ^ 33495 := by
  rw [Dexp_def, Nat.cast_pow, Nat.cast_ofNat]

/-- The moment threshold is positive. -/
theorem Dexp_pos : 0 < Dexp := by
  rw [Dexp_def]
  positivity

/-- The cast of the moment threshold is positive. -/
theorem Dexp_cast_pos {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    0 < (Dexp : R) := by
  rw [Dexp_cast]
  positivity

end CollatzPosDens
