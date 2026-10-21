/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 14`

For `1 ≤ o ≤ 14` the check `rowCheck 14 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(14, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_14_o`, `1 ≤ o ≤ 14`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(14, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_1 :
    rowCheck 14 1 550001 650000 193431 193967
      300948054466800000 4931139159329021600000 4929756208468930800000
      326185164100900000 5344889677693269600000 5342854343279105900000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_2 :
    rowCheck 14 2 65089 81250 96716 96970
      36695756153956250 601285310634540350000 601070077865477512500
      36681478818562500 601092157375954400000 600782848995223050000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_3 :
    rowCheck 14 3 65089 81250 48358 48478
      37111812858006250 608134705155147137500 607885572529394818750
      31333557729581250 513478791062919093750 513181149217804762500 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_4 :
    rowCheck 14 4 2593953 3250000 24179 24235
      1392401846849000000 22818743642270771000000 22807551340983617000000
      1155110260544500000 18931750702032941500000 18917882998988993500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_5 :
    rowCheck 14 5 10324957 13000000 12090 12116
      5217325444903000000 85510480263261573000000 85459686001660750000000
      4209866392394000000 68998949406922756000000 68941690611042600000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_6 :
    rowCheck 14 6 2569303 3250000 6045 6057
      1215716835329750000 19925599381940742750000 19913097998656833750000
      949937821813500000 15572171838674087000000 15557424834575234000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_7 :
    rowCheck 14 7 5104211 6500000 3023 3028
      2254567923549500000 36959192443203712500000 36928222669445640000000
      1686260848389000000 27646765023394270000000 27611869489589840000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_8 :
    rowCheck 14 8 10120113 13000000 1512 1514
      4151694158131000000 68060544813277055000000 68006193207483102000000
      2952144651443000000 48401724019547054000000 48328192668764268000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_9 :
    rowCheck 14 9 10120113 13000000 756 757
      3811696023863000000 62487112506018174000000 62425028694864576000000
      2558514941658000000 41969085113719972000000 41881885638245120000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 10)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_10 :
    rowCheck 14 10 10120113 13000000 378 379
      3544890297273000000 58125895792509922000000 58049168365215456000000
      2458010464338000000 40338487016269780000000 40240551860099318000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 11)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_11 :
    rowCheck 14 11 10120113 13000000 189 190
      3469686352834000000 56906261221127188000000 56833902479477760000000
      2707180629946000000 44405573084911532000000 44310919485837966000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 12)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_12 :
    rowCheck 14 12 5181503241 6656000000 95 95
      1915359616495104000000 31408593787618118656000000 31363079017064996864000000
      1739596293034496000000 28549590238186361344000000 28481307315174291968000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 13)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_13 :
    rowCheck 14 13 2853953 3250000 48 48
      1094955913613250000 17956562792154044500000 17931214517257161250000
      1123856085374750000 18427492938275476250000 18369582771709188500000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(14, 14)` of the height-seventeen cost table passes. -/
theorem rowCheck_14_14 :
    rowCheck 14 14 12120093 13000000 24 24
      5005353639975000000 82054308150948211000000 81949871257220096000000
      4616683862557000000 75780778874245367000000 75563018386698479000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
