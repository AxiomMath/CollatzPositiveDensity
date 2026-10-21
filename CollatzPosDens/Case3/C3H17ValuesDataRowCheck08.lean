/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 8`

For `1 ≤ o ≤ 8` the check `rowCheck 8 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(8, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_8_o`, `1 ≤ o ≤ 8`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(8, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_1 :
    rowCheck 8 1 250001 350000 4715 5250
      135885735408500000 2226536541184347000000 2225907927134474100000
      147357148984850000 2414604960287018800000 2413679808300125750000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_2 :
    rowCheck 8 2 27589 43750 2358 2612
      15003873035331250 245848909370135750000 245760607019950662500
      14998015555075000 245769665497115200000 245642767287845900000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_3 :
    rowCheck 8 3 27589 43750 1179 1299
      15341765750237500 251398730377993625000 251295567546085912500
      8711290530031250 142756364902032043750 142673453226356062500 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_4 :
    rowCheck 8 4 156279 250000 590 646
      71801160661500000 1176715848628840500000 1176142671071105000000
      37073117480750000 607615054770140250000 607169805629434250000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_5 :
    rowCheck 8 5 617851 1000000 295 321
      239649363778000000 3928143062697126000000 3925489080900888000000
      116093333772000000 1903081519316616000000 1901039140877360000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_6 :
    rowCheck 8 6 442678837 716800000 148 160
      161581003478630400000 2648761525381971148800000 2646832655069125017600000
      128975403832217600000 2114032225123520307200000 2112108168426289868800000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_7 :
    rowCheck 8 7 1353953 1750000 74 80
      448648119816750000 7354812208775223500000 7348314638687204000000
      471880329921000000 7734783136659600000000 7726056768639979000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(8, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_8_8 :
    rowCheck 8 8 874299 1000000 37 40
      291802646299000000 4784399675383676000000 4779938094880704000000
      250993252829000000 4113817237455843000000 4108966570233983000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
