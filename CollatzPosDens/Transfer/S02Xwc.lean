/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Lc
public import CollatzPosDens.Transfer.S02Z
public import CollatzPosDens.Transfer.Tstar

/-!
# The many-white exponent `x_W(ι)`

For a Fourier index `ι`, the many-white exponent is the rational constant
`x_W(ι) := z_* T_*(ι) - A_*(ι) ℓ_cont`. With `z_* = 133/3125`, `ℓ_cont = 157263/100000`,
`T_*(o) = 192`, `A_*(o) = 21193/10000`, `T_*(b) = 168` and `A_*(b) = 17/10` its values are
`x_W(o) = 4838645241/1000000000` and `x_W(b) = 4476609/1000000`, both positive. Since
`ℓ_cont` bounds `log (400/83)` from above, `e^{-z_* T_*(ι)} (400/83)^{A_*(ι)} < e^{-x_W(ι)}`.

## Main definitions

* `CollatzPosDens.xW`: the many-white exponent `x_W(ι) = z_* T_*(ι) - A_*(ι) ℓ_cont : ℚ`.

## Main results

* `CollatzPosDens.xW_o`, `CollatzPosDens.xW_b`: the values of `x_W` at the two indices.
* `CollatzPosDens.xW_pos`: `0 < x_W(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The many-white exponent `x_W(ι) := z_* T_*(ι) - A_*(ι) ℓ_cont ∈ ℚ` of the Fourier index
`ι`. -/
@[collatz_pos_dens "def_s02_xwc"]
def xW (ι : FIndex) : ℚ := zStar * tStar ι - Aexp ι * lc

/-- The value of the many-white exponent at the original index. -/
theorem xW_o : xW .o = 4838645241 / 1000000000 := by
  simp only [xW, zStar, tStar_o, Aexp_o, lc]
  norm_num

/-- The value of the many-white exponent at the bootstrap index. -/
theorem xW_b : xW .b = 4476609 / 1000000 := by
  simp only [xW, zStar, tStar_b, Aexp_b, lc]
  norm_num

/-- The many-white exponent is positive. -/
theorem xW_pos (ι : FIndex) : 0 < xW ι := by
  cases ι
  · rw [xW_o]; norm_num
  · rw [xW_b]; norm_num

end CollatzPosDens
