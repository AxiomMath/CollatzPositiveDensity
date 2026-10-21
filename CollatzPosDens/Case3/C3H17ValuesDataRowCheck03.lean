/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 3`

For `1 ≤ o ≤ 3` the check `rowCheck 3 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(3, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_3_o`, `1 ≤ o ≤ 3`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(3, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_3_1 :
    rowCheck 3 1 1 65536 158 693
      1280753420288 20984818395590656 20982476966971392
      1333887117312 21855711716818944 21852133838714880 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(3, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_3_2 :
    rowCheck 3 2 176777 250000 79 333
      102914240875000000 1686321532435752000000 1685715783402454000000
      102874058886750000 1685777923958544000000 1684907409288475000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(3, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_3_3 :
    rowCheck 3 3 23097 25000 40 160
      13890883822350000 227623771885315700000 227530359997502250000
      5768224408025000 94526839908314275000 94471934280636850000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
