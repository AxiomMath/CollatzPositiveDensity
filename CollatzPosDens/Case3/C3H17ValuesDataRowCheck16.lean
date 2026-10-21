/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 16`

For `1 ≤ o ≤ 16` the check `rowCheck 16 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(16, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_16_o`, `1 ≤ o ≤ 16`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(16, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_1 :
    rowCheck 16 1 216667 250000 678543 679079
      120523052463750000 1974809723487426500000 1974264924701935750000
      130464944158000000 2137802352302416000000 2137000553927770000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_2 :
    rowCheck 16 2 25863 31250 339272 339526
      14778363432718750 242153485637774250000 242067522853497437500
      14772661144281250 242076341315830000000 241952805235585125000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_3 :
    rowCheck 16 3 25863 31250 169636 169756
      14910375340281250 244329506538737187500 244229822882268843750
      13020815830687500 213378455699240562500 213255341203405375000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_4 :
    rowCheck 16 4 3093953 3750000 84818 84874
      1705007636546250000 27941639137348098750000 27927949854115586250000
      1470337512540000000 24098140336704180000000 24080528117781780000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_5 :
    rowCheck 16 5 4108319 5000000 42409 42435
      2170031849690000000 35565839622458350000000 35544934172676020000000
      1838974188685000000 30140182991045010000000 30115348899135540000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_6 :
    rowCheck 16 6 1023101 1250000 21205 21217
      517669852315000000 8484463454601375000000 8479197508579950000000
      430143241642500000 7051114425787545000000 7044607817299370000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_7 :
    rowCheck 16 7 2034737 2500000 10603 10608
      987060381820000000 16180612764117940000000 16167120563161920000000
      799827205012500000 13112950081906932500000 13097035115517000000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_8 :
    rowCheck 16 8 12120113 15000000 5302 5304
      5633001469275000000 92338784659047825000000 92265306557052270000000
      4426493558685000000 72569058109111410000000 72467377650400980000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_9 :
    rowCheck 16 9 12120113 15000000 2651 2652
      5352534100875000000 87742724783674905000000 87655176181122510000000
      4045310954580000000 66346199512662660000000 66222787480512000000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 10)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_10 :
    rowCheck 16 10 12120113 15000000 1326 1326
      5068062917175000000 83092731455566425000000 82986472501658400000000
      3676409827905000000 60313422575600730000000 60191725880151300000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 11)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_11 :
    rowCheck 16 11 12120113 15000000 663 663
      4802190630225000000 78749643658096530000000 78650322253309440000000
      3388375782675000000 55584140466057390000000 55467474885151545000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 12)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_12 :
    rowCheck 16 12 12120113 15000000 332 332
      4660845511440000000 76425659061062880000000 76323111952730880000000
      3429618873570000000 56305926713196660000000 56168165431004130000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 13)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_13 :
    rowCheck 16 13 12120113 15000000 166 166
      4695511869615000000 77003965797207435000000 76889820899970720000000
      3828399196950000000 62777543869543440000000 62591783112467100000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 14)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_14 :
    rowCheck 16 14 6205503241 7680000000 83 83
      2562748905899520000000 42011934255547891200000000 41958462568920514560000000
      2363749981324800000000 38799887291325043200000000 38688393926083699200000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 15)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_15 :
    rowCheck 16 15 3353953 3750000 42 42
      1426638952380000000 23391329302024800000000 23362629704439480000000
      1460160299445000000 23950304738036415000000 23903386905998130000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(16, 16)` of the height-seventeen cost table passes. -/
theorem rowCheck_16_16 :
    rowCheck 16 16 14120093 15000000 21 21
      5878301455830000000 96388930952310990000000 96181240611507840000000
      5475320843520000000 89914440163683840000000 89661020471750400000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
