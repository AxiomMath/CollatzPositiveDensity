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
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck12
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck13
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck14
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck15
public import CollatzPosDens.Case3.C3H17ValuesDataRowCheck16

/-!
# The orbit means and ranges of the rows with 12 ≤ c ≤ 16

For each row `(c, o)` with `12 ≤ c ≤ 16`, the row check, the certified constants and the
certified rounded future costs give the orbit means and ranges of the row.

## Main results

* `CollatzPosDens.C3H17Values.rowMR_12_1`, …, `CollatzPosDens.C3H17Values.rowMR_16_16`:
  `RowMR c o` for each row `(c, o)` with `12 ≤ c ≤ 16` and `1 ≤ o ≤ c`.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The orbit means and ranges of the row `(12, 1)` are the table values. -/
theorem rowMR_12_1 : RowMR 12 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 1)
    (pn := 450001) (pd := 550000) (adir := 55800) (ajo := 56336)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 2)` are the table values. -/
theorem rowMR_12_2 : RowMR 12 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 2)
    (pn := 52589) (pd := 68750) (adir := 27900) (ajo := 28155)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 3)` are the table values. -/
theorem rowMR_12_3 : RowMR 12 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 3)
    (pn := 52589) (pd := 68750) (adir := 13950) (ajo := 14070)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 4)` are the table values. -/
theorem rowMR_12_4 : RowMR 12 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 4)
    (pn := 2093953) (pd := 2750000) (adir := 6975) (ajo := 7032)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 5)` are the table values. -/
theorem rowMR_12_5 : RowMR 12 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 5)
    (pn := 8324957) (pd := 11000000) (adir := 3488) (ajo := 3514)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 6)` are the table values. -/
theorem rowMR_12_6 : RowMR 12 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 6)
    (pn := 2069303) (pd := 2750000) (adir := 1744) (ajo := 1756)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 7)` are the table values. -/
theorem rowMR_12_7 : RowMR 12 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 7)
    (pn := 4104211) (pd := 5500000) (adir := 872) (ajo := 878)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 8)` are the table values. -/
theorem rowMR_12_8 : RowMR 12 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 8)
    (pn := 8120113) (pd := 11000000) (adir := 436) (ajo := 439)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 9)` are the table values. -/
theorem rowMR_12_9 : RowMR 12 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 9)
    (pn := 8120113) (pd := 11000000) (adir := 218) (ajo := 219)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 10)` are the table values. -/
theorem rowMR_12_10 : RowMR 12 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 10)
    (pn := 4157503241) (pd := 5632000000) (adir := 109) (ajo := 110)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 11)` are the table values. -/
theorem rowMR_12_11 : RowMR 12 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 11)
    (pn := 2353953) (pd := 2750000) (adir := 55) (ajo := 55)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_11
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(12, 12)` are the table values. -/
theorem rowMR_12_12 : RowMR 12 12 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 12) (o := 12)
    (pn := 10120093) (pd := 11000000) (adir := 28) (ajo := 28)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_12_12
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 1)` are the table values. -/
theorem rowMR_13_1 : RowMR 13 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 1)
    (pn := 166667) (pd := 200000) (adir := 103950) (ajo := 104486)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 2)` are the table values. -/
theorem rowMR_13_2 : RowMR 13 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 2)
    (pn := 19613) (pd := 25000) (adir := 51975) (ajo := 52230)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 3)` are the table values. -/
theorem rowMR_13_3 : RowMR 13 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 3)
    (pn := 19613) (pd := 25000) (adir := 25988) (ajo := 26108)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 4)` are the table values. -/
theorem rowMR_13_4 : RowMR 13 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 4)
    (pn := 2343953) (pd := 3000000) (adir := 12994) (ajo := 13050)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 5)` are the table values. -/
theorem rowMR_13_5 : RowMR 13 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 5)
    (pn := 3108319) (pd := 4000000) (adir := 6497) (ajo := 6523)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 6)` are the table values. -/
theorem rowMR_13_6 : RowMR 13 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 6)
    (pn := 773101) (pd := 1000000) (adir := 3249) (ajo := 3261)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 7)` are the table values. -/
theorem rowMR_13_7 : RowMR 13 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 7)
    (pn := 1534737) (pd := 2000000) (adir := 1625) (ajo := 1630)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 8)` are the table values. -/
theorem rowMR_13_8 : RowMR 13 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 8)
    (pn := 9120113) (pd := 12000000) (adir := 813) (ajo := 815)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 9)` are the table values. -/
theorem rowMR_13_9 : RowMR 13 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 9)
    (pn := 9120113) (pd := 12000000) (adir := 407) (ajo := 408)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 10)` are the table values. -/
theorem rowMR_13_10 : RowMR 13 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 10)
    (pn := 9120113) (pd := 12000000) (adir := 204) (ajo := 204)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 11)` are the table values. -/
theorem rowMR_13_11 : RowMR 13 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 11)
    (pn := 4669503241) (pd := 6144000000) (adir := 102) (ajo := 102)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_11
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 12)` are the table values. -/
theorem rowMR_13_12 : RowMR 13 12 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 12)
    (pn := 2603953) (pd := 3000000) (adir := 51) (ajo := 51)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_12
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(13, 13)` are the table values. -/
theorem rowMR_13_13 : RowMR 13 13 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 13) (o := 13)
    (pn := 11120093) (pd := 12000000) (adir := 26) (ajo := 26)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_13_13
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 1)` are the table values. -/
theorem rowMR_14_1 : RowMR 14 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 1)
    (pn := 550001) (pd := 650000) (adir := 193431) (ajo := 193967)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 2)` are the table values. -/
theorem rowMR_14_2 : RowMR 14 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 2)
    (pn := 65089) (pd := 81250) (adir := 96716) (ajo := 96970)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 3)` are the table values. -/
theorem rowMR_14_3 : RowMR 14 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 3)
    (pn := 65089) (pd := 81250) (adir := 48358) (ajo := 48478)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 4)` are the table values. -/
theorem rowMR_14_4 : RowMR 14 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 4)
    (pn := 2593953) (pd := 3250000) (adir := 24179) (ajo := 24235)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 5)` are the table values. -/
theorem rowMR_14_5 : RowMR 14 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 5)
    (pn := 10324957) (pd := 13000000) (adir := 12090) (ajo := 12116)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 6)` are the table values. -/
theorem rowMR_14_6 : RowMR 14 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 6)
    (pn := 2569303) (pd := 3250000) (adir := 6045) (ajo := 6057)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 7)` are the table values. -/
theorem rowMR_14_7 : RowMR 14 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 7)
    (pn := 5104211) (pd := 6500000) (adir := 3023) (ajo := 3028)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 8)` are the table values. -/
theorem rowMR_14_8 : RowMR 14 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 8)
    (pn := 10120113) (pd := 13000000) (adir := 1512) (ajo := 1514)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 9)` are the table values. -/
theorem rowMR_14_9 : RowMR 14 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 9)
    (pn := 10120113) (pd := 13000000) (adir := 756) (ajo := 757)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 10)` are the table values. -/
theorem rowMR_14_10 : RowMR 14 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 10)
    (pn := 10120113) (pd := 13000000) (adir := 378) (ajo := 379)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 11)` are the table values. -/
theorem rowMR_14_11 : RowMR 14 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 11)
    (pn := 10120113) (pd := 13000000) (adir := 189) (ajo := 190)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_11
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 12)` are the table values. -/
theorem rowMR_14_12 : RowMR 14 12 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 12)
    (pn := 5181503241) (pd := 6656000000) (adir := 95) (ajo := 95)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_12
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 13)` are the table values. -/
theorem rowMR_14_13 : RowMR 14 13 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 13)
    (pn := 2853953) (pd := 3250000) (adir := 48) (ajo := 48)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_13
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(14, 14)` are the table values. -/
theorem rowMR_14_14 : RowMR 14 14 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 14) (o := 14)
    (pn := 12120093) (pd := 13000000) (adir := 24) (ajo := 24)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_14_14
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 1)` are the table values. -/
theorem rowMR_15_1 : RowMR 15 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 1)
    (pn := 600001) (pd := 700000) (adir := 362080) (ajo := 362615)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 2)` are the table values. -/
theorem rowMR_15_2 : RowMR 15 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 2)
    (pn := 71339) (pd := 87500) (adir := 181040) (ajo := 181294)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 3)` are the table values. -/
theorem rowMR_15_3 : RowMR 15 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 3)
    (pn := 71339) (pd := 87500) (adir := 90520) (ajo := 90640)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 4)` are the table values. -/
theorem rowMR_15_4 : RowMR 15 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 4)
    (pn := 406279) (pd := 500000) (adir := 45260) (ajo := 45316)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 5)` are the table values. -/
theorem rowMR_15_5 : RowMR 15 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 5)
    (pn := 1617851) (pd := 2000000) (adir := 22630) (ajo := 22656)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 6)` are the table values. -/
theorem rowMR_15_6 : RowMR 15 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 6)
    (pn := 2819303) (pd := 3500000) (adir := 11315) (ajo := 11327)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 7)` are the table values. -/
theorem rowMR_15_7 : RowMR 15 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 7)
    (pn := 5604211) (pd := 7000000) (adir := 5658) (ajo := 5663)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 8)` are the table values. -/
theorem rowMR_15_8 : RowMR 15 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 8)
    (pn := 11120113) (pd := 14000000) (adir := 2829) (ajo := 2832)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 9)` are the table values. -/
theorem rowMR_15_9 : RowMR 15 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 9)
    (pn := 11120113) (pd := 14000000) (adir := 1415) (ajo := 1416)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 10)` are the table values. -/
theorem rowMR_15_10 : RowMR 15 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 10)
    (pn := 11120113) (pd := 14000000) (adir := 708) (ajo := 708)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 11)` are the table values. -/
theorem rowMR_15_11 : RowMR 15 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 11)
    (pn := 11120113) (pd := 14000000) (adir := 354) (ajo := 354)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_11
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 12)` are the table values. -/
theorem rowMR_15_12 : RowMR 15 12 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 12)
    (pn := 11120113) (pd := 14000000) (adir := 177) (ajo := 177)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_12
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 13)` are the table values. -/
theorem rowMR_15_13 : RowMR 15 13 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 13)
    (pn := 5693503241) (pd := 7168000000) (adir := 89) (ajo := 89)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_13
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 14)` are the table values. -/
theorem rowMR_15_14 : RowMR 15 14 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 14)
    (pn := 3103953) (pd := 3500000) (adir := 45) (ajo := 45)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_15_14
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(15, 15)` are the table values. -/
theorem rowMR_15_15 : RowMR 15 15 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 15) (o := 15)
    (pn := 1874299) (pd := 2000000) (adir := 23) (ajo := 23)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun h => absurd h (by norm_num)) rowCheck_15_15
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 1)` are the table values. -/
theorem rowMR_16_1 : RowMR 16 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 1)
    (pn := 216667) (pd := 250000) (adir := 678543) (ajo := 679079)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_1
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 2)` are the table values. -/
theorem rowMR_16_2 : RowMR 16 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 2)
    (pn := 25863) (pd := 31250) (adir := 339272) (ajo := 339526)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_2
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 3)` are the table values. -/
theorem rowMR_16_3 : RowMR 16 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 3)
    (pn := 25863) (pd := 31250) (adir := 169636) (ajo := 169756)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_3
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 4)` are the table values. -/
theorem rowMR_16_4 : RowMR 16 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 4)
    (pn := 3093953) (pd := 3750000) (adir := 84818) (ajo := 84874)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_4
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 5)` are the table values. -/
theorem rowMR_16_5 : RowMR 16 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 5)
    (pn := 4108319) (pd := 5000000) (adir := 42409) (ajo := 42435)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_5
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 6)` are the table values. -/
theorem rowMR_16_6 : RowMR 16 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 6)
    (pn := 1023101) (pd := 1250000) (adir := 21205) (ajo := 21217)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_6
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 7)` are the table values. -/
theorem rowMR_16_7 : RowMR 16 7 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 7)
    (pn := 2034737) (pd := 2500000) (adir := 10603) (ajo := 10608)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_7
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 8)` are the table values. -/
theorem rowMR_16_8 : RowMR 16 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 8)
    (pn := 12120113) (pd := 15000000) (adir := 5302) (ajo := 5304)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_8
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 9)` are the table values. -/
theorem rowMR_16_9 : RowMR 16 9 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 9)
    (pn := 12120113) (pd := 15000000) (adir := 2651) (ajo := 2652)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_9
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 10)` are the table values. -/
theorem rowMR_16_10 : RowMR 16 10 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 10)
    (pn := 12120113) (pd := 15000000) (adir := 1326) (ajo := 1326)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_10
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 11)` are the table values. -/
theorem rowMR_16_11 : RowMR 16 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 11)
    (pn := 12120113) (pd := 15000000) (adir := 663) (ajo := 663)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_11
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 12)` are the table values. -/
theorem rowMR_16_12 : RowMR 16 12 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 12)
    (pn := 12120113) (pd := 15000000) (adir := 332) (ajo := 332)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_12
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 13)` are the table values. -/
theorem rowMR_16_13 : RowMR 16 13 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 13)
    (pn := 12120113) (pd := 15000000) (adir := 166) (ajo := 166)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_13
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 14)` are the table values. -/
theorem rowMR_16_14 : RowMR 16 14 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 14)
    (pn := 6205503241) (pd := 7680000000) (adir := 83) (ajo := 83)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun _ => nodeSpec (by norm_num) (by norm_num)) rowCheck_16_14
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 15)` are the table values. -/
theorem rowMR_16_15 : RowMR 16 15 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 15)
    (pn := 3353953) (pd := 3750000) (adir := 42) (ajo := 42)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun h => absurd h (by norm_num)) rowCheck_16_15
  exact rowMR_of_rowEntry h (by decide +kernel)

/-- The orbit means and ranges of the row `(16, 16)` are the table values. -/
theorem rowMR_16_16 : RowMR 16 16 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rowConst_spec (c := 16) (o := 16)
    (pn := 14120093) (pd := 15000000) (adir := 21) (ajo := 21)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := rowSpec_of_rowCheck (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3
    h4 h5 
    (fun h => absurd h (by norm_num)) rowCheck_16_16
  exact rowMR_of_rowEntry h (by decide +kernel)

end C3H17Values

end CollatzPosDens
