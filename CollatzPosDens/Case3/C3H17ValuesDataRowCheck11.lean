/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 11`

For `1 ≤ o ≤ 11` the check `rowCheck 11 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(11, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_11_o`, `1 ≤ o ≤ 11`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(11, 1)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_1 :
    rowCheck 11 1 400001 500000 30203 30739
      217620822023500000 3565794991417077000000 3564789209165447500000
      235975083719500000 3866704461761620000000 3865224218575190500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 2)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_2 :
    rowCheck 11 2 46339 62500 15102 15356
      25743943770750000 421832427224906000000 421680989966581500000
      25733898273687500 421696525105604000000 421478896438086750000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 3)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_3 :
    rowCheck 11 3 46339 62500 7551 7671
      26022503749562500 426419244352032375000 426244303086720687500
      19983215135750000 327475127498537250000 327284987163327500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 4)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_4 :
    rowCheck 11 4 1843953 2500000 3776 3832
      934101513702500000 15308230986014987500000 15300736991177062500000
      691073383905000000 11326427553998715000000 11318127272746915000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 5)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_5 :
    rowCheck 11 5 7324957 10000000 1888 1914
      3332892010950000000 54626671587326450000000 54593175929518360000000
      2288086835370000000 37503000984463580000000 37470229904272040000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 6)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_6 :
    rowCheck 11 6 1819303 2500000 944 956
      731361566667500000 11987707648619317500000 11979897837158095000000
      465779438325000000 7635970262937970000000 7628009541220220000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 7)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_7 :
    rowCheck 11 7 3604211 5000000 472 478
      1276683377655000000 20930026448166645000000 20911713561076560000000
      749247600935000000 12285069172389930000000 12267707725954160000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 8)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_8 :
    rowCheck 11 8 7120113 10000000 236 239
      2324144222290000000 38106284824439450000000 38072203897539200000000
      1620149032570000000 26558489142117540000000 26521683661115390000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 9)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_9 :
    rowCheck 11 9 3645503241 5120000000 118 120
      1209816706636800000000 19835464553643504640000000 19815146407786659840000000
      1059132627102720000000 17367843924714705920000000 17335617965783802880000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 10)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_10 :
    rowCheck 11 10 2103953 2500000 59 60
      684940510977500000 11230605087359455000000 11217894440688780000000
      708257649042500000 11616925301730400000000 11594178380077307500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(11, 11)` of the height-seventeen cost table holds. -/
theorem rowCheck_11_11 :
    rowCheck 11 11 9120093 10000000 30 30
      3175395607980000000 52079442022852760000000 52018099360532480000000
      2860408604500000000 46908751063238040000000 46809714234504220000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
