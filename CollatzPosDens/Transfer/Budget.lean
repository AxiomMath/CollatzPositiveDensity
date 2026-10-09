/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Cont
public import CollatzPosDens.Transfer.H
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.PT
public import CollatzPosDens.Transfer.PW
public import CollatzPosDens.Transfer.Qpack

/-!
# The six-term budget `Bud`

This file defines the rational number
`Bud = 1/8000 + ccont (2 + 272 (Hstar + 1) Qpack) / Kstar + ccont / PT + 1/60 + 1/PW
  + ccont 2^{-43}`,
the sum of six explicit contributions, built from the constants `ccont`, `Hstar`, `Qpack`,
`Kstar`, `PT` and `PW`. In order, the terms bound the bad initial advance, both polynomial block
unions, the trace, the four exponential exceptions, the many-white damping, and the deterministic
clearing.

## Main definitions

* `CollatzPosDens.Bud`: the six-term budget, a rational number.

## Main results

* `CollatzPosDens.Bud_def`: the unfolding of `Bud`.
* `CollatzPosDens.Bud_cast`: the cast of `Bud` into a division ring of characteristic zero,
  e.g. `ℝ`, is the same expression in the cast constants.
* `CollatzPosDens.Bud_pos`: `0 < Bud`.

## Implementation notes

The natural-number constants `Hstar` and `Kstar` are cast to `ℚ`, and the factor `2^{-43}` is
written as a division by `2 ^ 43`, so that `Bud` is a closed rational expression.
-/

@[expose] public section

namespace CollatzPosDens

/-- The six-term budget
`Bud := 1/8000 + ccont (2 + 272 (Hstar + 1) Qpack) / Kstar + ccont / PT + 1/60 + 1/PW
  + ccont 2^{-43} ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_budget"]
def Bud : ℚ :=
  1 / 8000 + ccont * ((2 + 272 * ((Hstar : ℚ) + 1) * Qpack) / (Kstar : ℚ)) + ccont / PT
    + 1 / 60 + 1 / PW + ccont / 2 ^ 43

/-- Unfolding lemma for the six-term budget. -/
theorem Bud_def : Bud =
    1 / 8000 + ccont * ((2 + 272 * ((Hstar : ℚ) + 1) * Qpack) / (Kstar : ℚ)) + ccont / PT
      + 1 / 60 + 1 / PW + ccont / 2 ^ 43 := rfl

/-- The cast of the six-term budget into a division ring of characteristic zero. -/
theorem Bud_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (Bud : K) =
      1 / 8000 + (ccont : K) * ((2 + 272 * ((Hstar : K) + 1) * (Qpack : K)) / (Kstar : K))
        + (ccont : K) / (PT : K) + 1 / 60 + 1 / (PW : K) + (ccont : K) / 2 ^ 43 := by
  simp only [Bud_def, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_natCast, Rat.cast_pow]

/-- The six-term budget is positive. -/
theorem Bud_pos : 0 < Bud := by
  have := ccont_pos; have := Qpack_pos; have := PT_pos; have := PW_pos
  rw [Bud_def]
  positivity

end CollatzPosDens
