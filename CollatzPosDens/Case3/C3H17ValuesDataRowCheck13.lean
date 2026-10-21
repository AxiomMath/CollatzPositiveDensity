/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 13`

For `1 ≤ o ≤ 13` the check `rowCheck 13 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(13, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_13_o`, `1 ≤ o ≤ 13`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(13, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_1 :
    rowCheck 13 1 166667 200000 103950 104486
      90912799316600000 1489638405504101200000 1489219329488929400000
      98560408369600000 1615017351580531200000 1614400583582100800000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_2 :
    rowCheck 13 2 19613 25000 51975 52230
      11004125558525000 180310227316706200000 180245582527718650000
      10999837388450000 180252214096112000000 180159313875403400000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_3 :
    rowCheck 13 3 19613 25000 25988 26108
      11127899364600000 182347939916894800000 182273179794554600000
      9178514544450000 150412969228850550000 150325703100512900000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_4 :
    rowCheck 13 4 2343953 3000000 12994 13050
      1238291843940000000 20293227839791596000000 20283276956399460000000
      999360612213000000 16379097553950999000000 16367095401075807000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_5 :
    rowCheck 13 5 3108319 4000000 6497 6523
      1526681058248000000 25022043104404184000000 25007079940870032000000
      1187638354844000000 19465331179093848000000 19449077867624048000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_6 :
    rowCheck 13 6 773101 1000000 3249 3261
      350047142262000000 5737347500493950000000 5733718603047798000000
      260909976050000000 4277124657712692000000 4272984416337752000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_7 :
    rowCheck 13 7 1534737 2000000 1625 1630
      637314968784000000 10447669009084784000000 10438862881511168000000
      447006508216000000 7329072713311408000000 7319479163100032000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_8 :
    rowCheck 13 8 9120113 12000000 813 815
      3453374083116000000 56615380313269980000000 56569005672140544000000
      2295465899052000000 37636595287196280000000 37576522019175216000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_9 :
    rowCheck 13 9 9120113 12000000 407 408
      3129473150244000000 51305515573676844000000 51253180246308096000000
      2087863034556000000 34248417302394444000000 34177064763754104000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 10)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_10 :
    rowCheck 13 10 9120113 12000000 204 204
      3003931730244000000 49258056049872456000000 49194311782078464000000
      2282467139712000000 37457623748919168000000 37366774967427456000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 11)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_11 :
    rowCheck 13 11 4669503241 6144000000 102 102
      1625810317074432000000 26664801548570836992000000 26633394106102972416000000
      1464536970049536000000 24017407760233992192000000 23966700900664436736000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 12)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_12 :
    rowCheck 13 12 2603953 3000000 51 51
      936195415812000000 15350576751406248000000 15329362705191876000000
      963781857483000000 15812917023759627000000 15776589860486439000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(13, 13)` of the height-seventeen cost table passes. -/
theorem rowCheck_13_13 :
    rowCheck 13 13 11120093 12000000 26 26
      4367273298564000000 71624149276893780000000 71517268839595392000000
      3992654430156000000 65467372052278500000000 65258620277460360000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
