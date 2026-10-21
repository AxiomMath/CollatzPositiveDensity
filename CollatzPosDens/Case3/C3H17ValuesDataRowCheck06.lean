/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 6`

For `1 ≤ o ≤ 6` the check `rowCheck 6 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(6, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_6_o`, `1 ≤ o ≤ 6`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The row check of the height-seventeen cost table holds for the row `(6, 1)`. -/
theorem rowCheck_6_1 :
    rowCheck 6 1 150001 250000 1320 1856
      81520981080750000 1335750545450920500000 1335373376917144750000
      88403829229500000 1448591597073508000000 1448036505831112500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The row check of the height-seventeen cost table holds for the row `(6, 2)`. -/
theorem rowCheck_6_2 :
    rowCheck 6 2 15089 31250 660 915
      8136445843468750 133321332809560250000 133273444146574937500
      8133269178906250 133278356790254000000 133209536577675625000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The row check of the height-seventeen cost table holds for the row `(6, 3)`. -/
theorem rowCheck_6_3 :
    rowCheck 6 3 15089 31250 330 450
      9074844950125000 148705471643474750000 148644447387042375000
      1561083254437500 25582267972817812500 25567410626444875000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The row check of the height-seventeen cost table holds for the row `(6, 4)`. -/
theorem rowCheck_6_4 :
    rowCheck 6 4 1357283593 2560000000 165 222
      641144729653760000000 10507456021006046720000000 10502328730706242560000000
      376075643471360000000 6163468467495249920000000 6158817413439541760000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The row check of the height-seventeen cost table holds for the row `(6, 5)`. -/
theorem rowCheck_6_5 :
    rowCheck 6 5 170911 250000 83 109
      69914944780500000 1145915654664209000000 1145195085007282000000
      71295004927000000 1168433076864322000000 1167457373265149000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The row check of the height-seventeen cost table holds for the row `(6, 6)`. -/
theorem rowCheck_6_6 :
    rowCheck 6 6 864601 1000000 42 54
      315585108062000000 5173316653187142000000 5169549328146400000000
      251902296271000000 4128923489221242000000 4125165566270573000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
