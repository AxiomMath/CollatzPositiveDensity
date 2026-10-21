/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 5`

For `1 ≤ o ≤ 5` the check `rowCheck 5 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(5, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_5_o`, `1 ≤ o ≤ 5`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(5, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_5_1 :
    rowCheck 5 1 100001 200000 708 1243
      163841638400000000 2684381403545600000000 2684381403545600000000
      163841638400000000 2684381403545600000000 2684381403545600000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(5, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_5_2 :
    rowCheck 5 2 8839 25000 354 608
      14481692262400000 237268046027161600000 237268046027161600000
      14481692262400000 237268046027161600000 237268046027161600000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(5, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_5_3 :
    rowCheck 5 3 461943 1000000 177 297
      756845019136000000 12400148793524224000000 12400148793524224000000
      313497174016000000 5136337699078144000000 5136337699078144000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(5, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_5_4 :
    rowCheck 5 4 120911 200000 89 145
      163081738649600000 2671946953657548800000 2671931206035046400000
      159140780441600000 2607362546755174400000 2607323587149824000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(5, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_5_5 :
    rowCheck 5 5 433771 500000 45 71
      417759432704000000 6844925299392512000000 6844570545422336000000
      320273797120000000 5247423122743296000000 5247309883002880000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
