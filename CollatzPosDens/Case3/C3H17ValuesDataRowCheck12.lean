/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 12`

For `1 ≤ o ≤ 12` the check `rowCheck 12 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(12, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_12_o`, `1 ≤ o ≤ 12`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(12, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_1 :
    rowCheck 12 1 450001 550000 55800 56336
      245047786413100000 4015195306552854600000 4014063801341485100000
      265696330570000000 4353718456379811200000 4352053182817758000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_2 :
    rowCheck 12 2 52589 68750 27900 28155
      29366396998950000 481188819918184400000 481016154871860300000
      29354943363212500 481033867527144800000 480785732697830450000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_3 :
    rowCheck 12 3 52589 68750 13950 14070
      29687675669918750 486478775813215212500 486279241005622556250
      23754596471168750 389278652030053156250 389052688964695937500 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_4 :
    rowCheck 12 4 2093953 2750000 6975 7032
      1085425658130000000 17788094378833174000000 17779377504853778000000
      844583364196000000 13842378860496780000000 13832234362284844000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_5 :
    rowCheck 12 5 8324957 11000000 3488 3514
      3950600514179000000 64750252131226585000000 64711137940108044000000
      2921306416017000000 47880722940190998000000 47840077586502212000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_6 :
    rowCheck 12 6 2069303 2750000 1744 1756
      887905825155250000 14553231409024250250000 14543920279735107250000
      619617087438250000 10157682189726054500000 10147539731867307000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_7 :
    rowCheck 12 7 4104211 5500000 872 878
      1582605234952500000 25944576425347409500000 25922443802675992000000
      1013589544979000000 16619443769779246000000 16596670408872752000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_8 :
    rowCheck 12 8 8120113 11000000 436 439
      2820735857753000000 46246380956080701000000 46206733759897920000000
      1802457371187000000 29552645238538510000000 29505260658167404000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_9 :
    rowCheck 12 9 8120113 11000000 218 219
      2619618638274000000 42948868763713000000000 42904860575102592000000
      1915390592654000000 31414832414235314000000 31352665059139996000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 10)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_10 :
    rowCheck 12 10 4157503241 5632000000 109 110
      1396896744027136000000 22905541816621775872000000 22877752087622975488000000
      1238714118844928000000 20323780687522909696000000 20279304989419784704000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 11)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_11 :
    rowCheck 12 11 2353953 2750000 55 55
      798210109944500000 13090469915189579000000 13075437328718352500000
      821070648147750000 13461964298580891500000 13434534704867009250000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(12, 12)` of the height-seventeen cost table passes. -/
theorem rowCheck_12_12 :
    rowCheck 12 12 10120093 11000000 28 28
      3740921532062000000 61344660394413484000000 61255764356320160000000
      3397633792586000000 55760669113379274000000 55627304032398098000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
