/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRowTab
public import CollatzPosDens.Case3.C3H17ValuesDataNodeSpec
public import CollatzPosDens.Case3.C3H17ValuesDataConst
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck02
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck03
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck04
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck05
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck06
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck07
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck08
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck09
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck10
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck11

/-!
# The orbit means and ranges of the rows with 2 ≤ c ≤ 11

For each row `(c, o)` with `2 ≤ c ≤ 11`, the row check, the certified constants and the
certified rounded future costs give the orbit means and ranges of the row.

## Main results

* `CollatzPosDens.C3H17Values.rowMR_c_o`: `RowMR c o`.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The orbit means and ranges of the row `(2, 1)` are the table values. -/
theorem rowMR_2_1 : RowMR 2 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 2) (o := 1)
    (pn := 1) (pd := 1) (adir := 0) (ajo := 536)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_2_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(2, 2)` are the table values. -/
theorem rowMR_2_2 : RowMR 2 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 2) (o := 2)
    (pn := 1) (pd := 1) (adir := 0) (ajo := 255)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_2_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(3, 1)` are the table values. -/
theorem rowMR_3_1 : RowMR 3 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 3) (o := 1)
    (pn := 1) (pd := 65536) (adir := 158) (ajo := 693)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_3_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(3, 2)` are the table values. -/
theorem rowMR_3_2 : RowMR 3 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 3) (o := 2)
    (pn := 176777) (pd := 250000) (adir := 79) (ajo := 333)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_3_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(3, 3)` are the table values. -/
theorem rowMR_3_3 : RowMR 3 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 3) (o := 3)
    (pn := 23097) (pd := 25000) (adir := 40) (ajo := 160)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_3_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(4, 1)` are the table values. -/
theorem rowMR_4_1 : RowMR 4 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 4) (o := 1)
    (pn := 16667) (pd := 50000) (adir := 315) (ajo := 850)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_4_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(4, 2)` are the table values. -/
theorem rowMR_4_2 : RowMR 4 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 4) (o := 2)
    (pn := 333337) (pd := 1000000) (adir := 158) (ajo := 412)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_4_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(4, 3)` are the table values. -/
theorem rowMR_4_3 : RowMR 4 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 4) (o := 3)
    (pn := 72169) (pd := 125000) (adir := 79) (ajo := 199)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_4_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(4, 4)` are the table values. -/
theorem rowMR_4_4 : RowMR 4 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 4) (o := 4)
    (pn := 441819) (pd := 500000) (adir := 40) (ajo := 96)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_4_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(5, 1)` are the table values. -/
theorem rowMR_5_1 : RowMR 5 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 5) (o := 1)
    (pn := 100001) (pd := 200000) (adir := 708) (ajo := 1243)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_5_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(5, 2)` are the table values. -/
theorem rowMR_5_2 : RowMR 5 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 5) (o := 2)
    (pn := 8839) (pd := 25000) (adir := 354) (ajo := 608)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_5_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(5, 3)` are the table values. -/
theorem rowMR_5_3 : RowMR 5 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 5) (o := 3)
    (pn := 461943) (pd := 1000000) (adir := 177) (ajo := 297)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_5_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(5, 4)` are the table values. -/
theorem rowMR_5_4 : RowMR 5 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 5) (o := 4)
    (pn := 120911) (pd := 200000) (adir := 89) (ajo := 145)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_5_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(5, 5)` are the table values. -/
theorem rowMR_5_5 : RowMR 5 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 5) (o := 5)
    (pn := 433771) (pd := 500000) (adir := 45) (ajo := 71)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_5_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(6, 1)` are the table values. -/
theorem rowMR_6_1 : RowMR 6 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 6) (o := 1)
    (pn := 150001) (pd := 250000) (adir := 1320) (ajo := 1856)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_6_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(6, 2)` are the table values. -/
theorem rowMR_6_2 : RowMR 6 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 6) (o := 2)
    (pn := 15089) (pd := 31250) (adir := 660) (ajo := 915)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_6_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(6, 3)` are the table values. -/
theorem rowMR_6_3 : RowMR 6 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 6) (o := 3)
    (pn := 15089) (pd := 31250) (adir := 330) (ajo := 450)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_6_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(6, 4)` are the table values. -/
theorem rowMR_6_4 : RowMR 6 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 6) (o := 4)
    (pn := 1357283593) (pd := 2560000000) (adir := 165) (ajo := 222)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_6_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(6, 5)` are the table values. -/
theorem rowMR_6_5 : RowMR 6 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 6) (o := 5)
    (pn := 170911) (pd := 250000) (adir := 83) (ajo := 109)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_6_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(6, 6)` are the table values. -/
theorem rowMR_6_6 : RowMR 6 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 6) (o := 6)
    (pn := 864601) (pd := 1000000) (adir := 42) (ajo := 54)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_6_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 1)` are the table values. -/
theorem rowMR_7_1 : RowMR 7 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 1)
    (pn := 66667) (pd := 100000) (adir := 2567) (ajo := 3103)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 2)` are the table values. -/
theorem rowMR_7_2 : RowMR 7 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 2)
    (pn := 7113) (pd := 12500) (adir := 1284) (ajo := 1538)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 3)` are the table values. -/
theorem rowMR_7_3 : RowMR 7 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 3)
    (pn := 7113) (pd := 12500) (adir := 642) (ajo := 762)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 4)` are the table values. -/
theorem rowMR_7_4 : RowMR 7 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 4)
    (pn := 843953) (pd := 1500000) (adir := 321) (ajo := 377)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 5)` are the table values. -/
theorem rowMR_7_5 : RowMR 7 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 5)
    (pn := 1776741641) (pd := 3072000000) (adir := 161) (ajo := 187)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 6)` are the table values. -/
theorem rowMR_7_6 : RowMR 7 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 6)
    (pn := 1103953) (pd := 1500000) (adir := 81) (ajo := 93)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(7, 7)` are the table values. -/
theorem rowMR_7_7 : RowMR 7 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 7) (o := 7)
    (pn := 868067) (pd := 1000000) (adir := 41) (ajo := 46)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_7_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 1)` are the table values. -/
theorem rowMR_8_1 : RowMR 8 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 1)
    (pn := 250001) (pd := 350000) (adir := 4715) (ajo := 5250)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 2)` are the table values. -/
theorem rowMR_8_2 : RowMR 8 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 2)
    (pn := 27589) (pd := 43750) (adir := 2358) (ajo := 2612)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 3)` are the table values. -/
theorem rowMR_8_3 : RowMR 8 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 3)
    (pn := 27589) (pd := 43750) (adir := 1179) (ajo := 1299)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 4)` are the table values. -/
theorem rowMR_8_4 : RowMR 8 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 4)
    (pn := 156279) (pd := 250000) (adir := 590) (ajo := 646)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 5)` are the table values. -/
theorem rowMR_8_5 : RowMR 8 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 5)
    (pn := 617851) (pd := 1000000) (adir := 295) (ajo := 321)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 6)` are the table values. -/
theorem rowMR_8_6 : RowMR 8 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 6)
    (pn := 442678837) (pd := 716800000) (adir := 148) (ajo := 160)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 7)` are the table values. -/
theorem rowMR_8_7 : RowMR 8 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 7)
    (pn := 1353953) (pd := 1750000) (adir := 74) (ajo := 80)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(8, 8)` are the table values. -/
theorem rowMR_8_8 : RowMR 8 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 8) (o := 8)
    (pn := 874299) (pd := 1000000) (adir := 37) (ajo := 40)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_8_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 1)` are the table values. -/
theorem rowMR_9_1 : RowMR 9 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 1)
    (pn := 300001) (pd := 400000) (adir := 8840) (ajo := 9375)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 2)` are the table values. -/
theorem rowMR_9_2 : RowMR 9 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 2)
    (pn := 33839) (pd := 50000) (adir := 4420) (ajo := 4674)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 3)` are the table values. -/
theorem rowMR_9_3 : RowMR 9 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 3)
    (pn := 33839) (pd := 50000) (adir := 2210) (ajo := 2330)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 4)` are the table values. -/
theorem rowMR_9_4 : RowMR 9 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 4)
    (pn := 1343953) (pd := 2000000) (adir := 1105) (ajo := 1161)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 5)` are the table values. -/
theorem rowMR_9_5 : RowMR 9 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 5)
    (pn := 5324957) (pd := 8000000) (adir := 553) (ajo := 579)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 6)` are the table values. -/
theorem rowMR_9_6 : RowMR 9 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 6)
    (pn := 1319303) (pd := 2000000) (adir := 277) (ajo := 289)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 7)` are the table values. -/
theorem rowMR_9_7 : RowMR 9 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 7)
    (pn := 2666717449) (pd := 4096000000) (adir := 139) (ajo := 144)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 8)` are the table values. -/
theorem rowMR_9_8 : RowMR 9 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 8)
    (pn := 1603953) (pd := 2000000) (adir := 70) (ajo := 72)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(9, 9)` are the table values. -/
theorem rowMR_9_9 : RowMR 9 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 9) (o := 9)
    (pn := 7120093) (pd := 8000000) (adir := 35) (ajo := 36)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_9_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 1)` are the table values. -/
theorem rowMR_10_1 : RowMR 10 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 1)
    (pn := 38889) (pd := 50000) (adir := 16239) (ajo := 16774)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 2)` are the table values. -/
theorem rowMR_10_2 : RowMR 10 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 2)
    (pn := 13363) (pd := 18750) (adir := 8120) (ajo := 8374)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 3)` are the table values. -/
theorem rowMR_10_3 : RowMR 10 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 3)
    (pn := 13363) (pd := 18750) (adir := 4060) (ajo := 4180)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 4)` are the table values. -/
theorem rowMR_10_4 : RowMR 10 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 4)
    (pn := 1593953) (pd := 2250000) (adir := 2030) (ajo := 2086)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 5)` are the table values. -/
theorem rowMR_10_5 : RowMR 10 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 5)
    (pn := 702773) (pd := 1000000) (adir := 1015) (ajo := 1041)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 6)` are the table values. -/
theorem rowMR_10_6 : RowMR 10 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 6)
    (pn := 174367) (pd := 250000) (adir := 508) (ajo := 520)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 7)` are the table values. -/
theorem rowMR_10_7 : RowMR 10 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 7)
    (pn := 1034737) (pd := 1500000) (adir := 254) (ajo := 260)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 8)` are the table values. -/
theorem rowMR_10_8 : RowMR 10 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 8)
    (pn := 3133503241) (pd := 4608000000) (adir := 127) (ajo := 130)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 9)` are the table values. -/
theorem rowMR_10_9 : RowMR 10 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 9)
    (pn := 1853953) (pd := 2250000) (adir := 64) (ajo := 65)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(10, 10)` are the table values. -/
theorem rowMR_10_10 : RowMR 10 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 10) (o := 10)
    (pn := 8120093) (pd := 9000000) (adir := 32) (ajo := 33)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_10_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 1)` are the table values. -/
theorem rowMR_11_1 : RowMR 11 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 1)
    (pn := 400001) (pd := 500000) (adir := 30203) (ajo := 30739)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 2)` are the table values. -/
theorem rowMR_11_2 : RowMR 11 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 2)
    (pn := 46339) (pd := 62500) (adir := 15102) (ajo := 15356)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 3)` are the table values. -/
theorem rowMR_11_3 : RowMR 11 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 3)
    (pn := 46339) (pd := 62500) (adir := 7551) (ajo := 7671)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 4)` are the table values. -/
theorem rowMR_11_4 : RowMR 11 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 4)
    (pn := 1843953) (pd := 2500000) (adir := 3776) (ajo := 3832)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 5)` are the table values. -/
theorem rowMR_11_5 : RowMR 11 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 5)
    (pn := 7324957) (pd := 10000000) (adir := 1888) (ajo := 1914)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 6)` are the table values. -/
theorem rowMR_11_6 : RowMR 11 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 6)
    (pn := 1819303) (pd := 2500000) (adir := 944) (ajo := 956)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 7)` are the table values. -/
theorem rowMR_11_7 : RowMR 11 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 7)
    (pn := 3604211) (pd := 5000000) (adir := 472) (ajo := 478)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 8)` are the table values. -/
theorem rowMR_11_8 : RowMR 11 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 8)
    (pn := 7120113) (pd := 10000000) (adir := 236) (ajo := 239)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 9)` are the table values. -/
theorem rowMR_11_9 : RowMR 11 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 9)
    (pn := 3645503241) (pd := 5120000000) (adir := 118) (ajo := 120)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 10)` are the table values. -/
theorem rowMR_11_10 : RowMR 11 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 10)
    (pn := 2103953) (pd := 2500000) (adir := 59) (ajo := 60)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(11, 11)` are the table values. -/
theorem rowMR_11_11 : RowMR 11 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 11) (o := 11)
    (pn := 9120093) (pd := 10000000) (adir := 30) (ajo := 30)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_11_11
  exact rowMR_of_rowEntry h (by decide +kernel)

end C3H17Values

end CollatzPosDens
