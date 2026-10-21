/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 4`

For `1 ≤ o ≤ 4` the check `rowCheck 4 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(4, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_4_o`, `1 ≤ o ≤ 4`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(4, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_4_1 :
    rowCheck 4 1 16667 50000 315 850
      27306925260800000 447396663472947200000 447396663472947200000
      27306925260800000 447396663472947200000 447396663472947200000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(4, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_4_2 :
    rowCheck 4 2 333337 1000000 158 412
      546135932928000000 8947891125092352000000 8947891125092352000000
      546135932928000000 8947891125092352000000 8947891125092352000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(4, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_4_3 :
    rowCheck 4 3 72169 125000 79 199
      118241497088000000 1937268688289792000000 1937268688289792000000
      118241497088000000 1937268688289792000000 1937268688289792000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(4, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_4_4 :
    rowCheck 4 4 441819 500000 40 96
      545172312064000000 8932281864794112000000 8932103160856576000000
      319892312064000000 5241115640856576000000 5240989490442240000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
