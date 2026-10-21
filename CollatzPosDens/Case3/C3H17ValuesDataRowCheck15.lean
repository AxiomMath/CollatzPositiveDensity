/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 15`

For `1 ≤ o ≤ 15` the check `rowCheck 15 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(15, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_15_o`, `1 ≤ o ≤ 15`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(15, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_1 :
    rowCheck 15 1 600001 700000 362080 362615
      330212267611800000 5410640958059856400000 5409132284255477400000
      357743659702800000 5862005155640278400000 5859784790947262000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_2 :
    rowCheck 15 2 71339 87500 181040 181294
      40448665751112500 662779127005195900000 662542574456862225000
      40432974183437500 662566841081056800000 662226894279312950000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_3 :
    rowCheck 15 3 71339 87500 90520 90640
      40884438424987500 669954885168794925000 669680822489434962500
      35165100910275000 576268016899567825000 575934526183759750000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_4 :
    rowCheck 15 4 406279 500000 45260 45316
      221116543192000000 3623660861778184000000 3621883875023064000000
      187418715277000000 3071707772157087000000 3069459448470439000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_5 :
    rowCheck 15 5 1617851 2000000 22630 22656
      837246462618000000 13722154500640046000000 13714048702718772000000
      694442293836000000 11381726176911032000000 11372317063229744000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_6 :
    rowCheck 15 6 2819303 3500000 11315 11327
      1383510716119000000 22675521573600427000000 22661380463915991000000
      1119403243885500000 18349966153706327000000 18332865063036706000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_7 :
    rowCheck 15 7 5604211 7000000 5658 5663
      2605219053430000000 42706984171628546000000 42671308524914720000000
      2040257229941000000 33449962751612981000000 33408678578537808000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_8 :
    rowCheck 15 8 11120113 14000000 2829 2832
      4882846774484000000 80043796402819620000000 79980103442675912000000
      3674992262872000000 60250705660677616000000 60163222296526944000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_9 :
    rowCheck 15 9 11120113 14000000 1415 1416
      4563566196896000000 74810774582659808000000 74736262823225920000000
      3264540459838000000 53545313068579206000000 53440586577729792000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 10)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_10 :
    rowCheck 15 10 11120113 14000000 708 708
      4257788766658000000 69811436394743652000000 69719785699562432000000
      2955175795866000000 48490075512612132000000 48381727957269966000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 11)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_11 :
    rowCheck 15 11 11120113 14000000 354 354
      4027472452850000000 66049770441973444000000 65965233086376960000000
      2882810827820000000 47291336887848312000000 47191479678512260000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 12)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_12 :
    rowCheck 15 12 11120113 14000000 177 177
      4048862841394000000 66393320202992930000000 66300528382738272000000
      3230756646922000000 53036795090911324000000 52906346390901514000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 13)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_13 :
    rowCheck 15 13 5693503241 7168000000 89 89
      2236051779247104000000 36671693054274833408000000 36616970264930320384000000
      2044246919938048000000 33519423129374228480000000 33412542223851585536000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 14)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_14 :
    rowCheck 15 14 3103953 3500000 45 45
      1255776397561000000 20585804859951471000000 20562104466025472000000
      1284997304717000000 21091591949899079000000 21032938848198046000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(15, 15)` of the height-seventeen cost table passes. -/
theorem rowCheck_15_15 :
    rowCheck 15 15 1874299 2000000 23 23
      814038303400000000 13346376292031520000000 13329702706913280000000
      754492049232000000 12377563632365552000000 12352246894914336000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
