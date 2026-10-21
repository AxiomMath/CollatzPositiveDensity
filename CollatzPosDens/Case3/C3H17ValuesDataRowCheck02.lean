/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataRow

/-!
# Checks of the rows of the height-seventeen cost table with `c = 2`

For `1 ≤ o ≤ 2` the check `rowCheck 2 o p_n p_d a_{dir} a_{jo} T₁ M₁ m₁ T₃ M₃ m₃ = true` of the
row `(2, o)`, evaluated by the kernel: the sums `T` and the extreme values `M`, `m` of the
scans of the orbit sequences of `s = 1` and `s = 3`.

## Main results

* `CollatzPosDens.C3H17Values.rowCheck_2_o`, `1 ≤ o ≤ 2`: the checks.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the row `(2, 1)` of the height-seventeen cost table passes. -/
theorem rowCheck_2_1 :
    rowCheck 2 1 1 1 0 536
      543431285062 8904316783303748 8901802327305030
      589316938916 9656590452771424 9652889844674028 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

/-- The check of the row `(2, 2)` of the height-seventeen cost table passes. -/
theorem rowCheck_2_2 :
    rowCheck 2 2 1 1 0 255
      582167304140 9539216854061984 9535790219744152
      581940000477 9536141739236800 9531217365225332 = true :=
  rowCheck_of_rowCheckF (by decide +kernel)

end C3H17Values

end CollatzPosDens
