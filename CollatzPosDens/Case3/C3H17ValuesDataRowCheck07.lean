/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 7`

For `1 ≤ o ≤ 7` the check `rowCheck 7 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(7, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_7_o`, `1 ≤ o ≤ 7`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(7, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_1 :
    rowCheck 7 1 66667 100000 2567 3103
      36233251930600000 593694840245750000000 593527209822452200000
      39292295522200000 643846418246772800000 643599710999283400000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(7, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_2 :
    rowCheck 7 2 7113 12500 1284 1538
      3835651459825000 62849820845111800000 62827245909838050000
      3834153966162500 62829561764690400000 62797119597048650000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(7, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_3 :
    rowCheck 7 3 7113 12500 642 762
      4010089930462500 65711570439240975000 65684604750837787500
      1665280161387500 27289796182262262500 27273946293244375000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(7, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_4 :
    rowCheck 7 4 843953 1500000 321 377
      384100266145500000 6294902354146828500000 6291819263363145000000
      168108324475500000 2755158797479846500000 2753131342637170500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(7, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_5 :
    rowCheck 7 5 1776741641 3072000000 161 187
      687068317307904000000 11261986727105095680000000 11254177649772982272000000
      526473582016512000000 8628705151964688384000000 8621251990994085888000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(7, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_6 :
    rowCheck 7 6 1103953 1500000 81 93
      387126745669500000 6346008900696487500000 6341329850232960000000
      413724114910500000 6781035845828679000000 6775048554221767500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(7, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_7_7 :
    rowCheck 7 7 868067 1000000 41 46
      298003707417000000 4885704271133293000000 4881158723350448000000
      247692939217000000 4060059379585471000000 4055472483493275000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
