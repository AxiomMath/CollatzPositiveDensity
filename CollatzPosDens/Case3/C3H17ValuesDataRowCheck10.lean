/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 10`

For `1 ≤ o ≤ 10` the check `rowCheck 10 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(10, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_10_o`, `1 ≤ o ≤ 10`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(10, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_1 :
    rowCheck 10 1 38889 50000 16239 16774
      21146839073000000 346498535044354800000 346400750639085800000
      22931281164400000 375753622146883200000 375609709613861200000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_2 :
    rowCheck 10 2 13363 18750 8120 8374
      7379989491712500 120926264937383100000 120882841173156225000
      7377109001231250 120887295736441200000 120824891991006525000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 3)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_3 :
    rowCheck 10 3 13363 18750 4060 4180
      7465004582775000 122325726548492250000 122275535104609125000
      5406024753750000 88591284861992850000 88539838519728300000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 4)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_4 :
    rowCheck 10 4 1593953 2250000 2030 2086
      785061431025750000 12865797659666009250000 12859508666915889750000
      539737232334750000 8846100675671006250000 8839619086222316250000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 5)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_5 :
    rowCheck 10 5 702773 1000000 1015 1041
      303857218179000000 4980351594752985000000 4977235018928908000000
      185628105049000000 3042673492892998000000 3039873747716452000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 6)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_6 :
    rowCheck 10 6 174367 250000 508 520
      65111075862000000 1067273193942686000000 1066554576536416000000
      37474421856250000 614360614053338500000 613692492982562750000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 7)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_7 :
    rowCheck 10 7 1034737 1500000 254 260
      339945244261500000 5573309159493091500000 5568199012574088000000
      224875840764000000 3686487653272296000000 3681921938378388000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 8)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_8 :
    rowCheck 10 8 3133503241 4608000000 127 130
      1045828162086912000000 17147410951228563456000000 17131420648144502784000000
      899567296321536000000 14744043500172208128000000 14726658710906800128000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 9)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_9 :
    rowCheck 10 9 1853953 2250000 64 65
      589537787073750000 9665669148704761500000 9655692759417204000000
      613689550665750000 10062068831383718250000 10044648515549459250000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(10, 10)` of the height-seventeen cost table passes. -/
theorem rowCheck_10_10 :
    rowCheck 10 10 8120093 9000000 32 33
      2728298978703000000 44737141019683653000000 44682864203782656000000
      2419348525272000000 39694638590912808000000 39607771991515128000000 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
