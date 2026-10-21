/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 9`

For `1 ≤ o ≤ 9` the check `rowCheck 9 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(9, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_9_o`, `1 ≤ o ≤ 9`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(9, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_1 :
    rowCheck 9 1 300001 400000 8840 9375
      163088196478000000 2672258593799495200000 2671504257041380400000
      176853892864000000 2897940698343424000000 2896830515854592000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_2 :
    rowCheck 9 2 33839 50000 4420 4674
      18556711504050000 304064639530898800000 303955436577171300000
      18549467590550000 303966639058665600000 303809704811239000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_3 :
    rowCheck 9 3 33839 50000 2210 2330
      18822744718850000 308439991332529900000 308313426443321350000
      12459280454650000 204176587076617950000 204058008542118900000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_4 :
    rowCheck 9 4 1343953 2000000 1105 1161
      639933105556000000 10487467592742268000000 10482352055124372000000
      393108230764000000 6442914316870244000000 6438194516574020000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_5 :
    rowCheck 9 5 5324957 8000000 553 579
      2172024537960000000 35601188375097272000000 35578161067679968000000
      1095580281968000000 17959441467676576000000 17941123958403520000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_6 :
    rowCheck 9 6 1319303 2000000 277 289
      466088472176000000 7640286030747568000000 7634861545699072000000
      274634941478000000 4502102486546212000000 4497303875954082000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_7 :
    rowCheck 9 7 2666717449 4096000000 139 144
      915474749526016000000 15009004115913232384000000 14995040190391844864000000
      760920069947392000000 12472623012785635328000000 12458532068309614592000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_8 :
    rowCheck 9 8 1603953 2000000 70 72
      514853585092000000 8441454018807848000000 8433099165433088000000
      535300676670000000 8773334635020836000000 8763721712348842000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(9, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_9_9 :
    rowCheck 9 9 7120093 8000000 35 36
      2362908289920000000 38740896514223744000000 38701212635392000000000
      2068603443696000000 33921324920978960000000 33858383593678672000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
