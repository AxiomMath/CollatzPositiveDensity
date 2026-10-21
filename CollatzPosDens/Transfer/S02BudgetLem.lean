/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Budget
public import CollatzPosDens.Transfer.S02BudgetLe
public import CollatzPosDens.Transfer.S02BudgetPlus

/-!
# The budget is less than one

For each Fourier index `ι : FIndex`, the budget `Bud ι` is bounded above by the rounded budget
`budPlus ι` (`Bud_le_budPlus`), and `budPlus ι < 1` (`budPlus_lt_one`), with slack
`1 - budPlus ι` exceeding `19300993707926 / 10^15` at `FIndex.o` and `2435391461730 / 10^15` at
`FIndex.b`. Hence `Bud ι < 1`.

## Main results

* `CollatzPosDens.Bud_lt_one`: the budget is less than one at every Fourier index.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The budget is less than one: `Bud(ι) < 1` for every Fourier index `ι`. -/
@[collatz_pos_dens "lem_s02_budget"]
theorem Bud_lt_one (ι : FIndex) : Bud ι < 1 :=
  (Bud_le_budPlus ι).trans_lt (budPlus_lt_one ι)

end CollatzPosDens
