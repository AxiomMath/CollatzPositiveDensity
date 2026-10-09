/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Basic.Real.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Dcap
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.S

/-!
# Room for the fresh scale

Every real number `m` with `Dsc ≤ m` satisfies `pStar ≤ m`. Since
`Dsc = 2 + pStar + Dcap + (100 * sStar) ^ 2` is a sum of natural numbers, in fact
`pStar + 2 ≤ Dsc ≤ m`.

## Main results

* `CollatzPosDens.pStar_add_two_le_of_Dsc_le`: if `Dsc ≤ m` for a real `m`, then
  `pStar + 2 ≤ m`.
* `CollatzPosDens.pStar_le_of_Dsc_le`: if `Dsc ≤ m` for a real `m`, then `pStar ≤ m`.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `m` is a real number with `Dsc ≤ m`, then `pStar + 2 ≤ m`. -/
theorem pStar_add_two_le_of_Dsc_le {m : ℝ} (hm : (Dsc : ℝ) ≤ m) : (pStar : ℝ) + 2 ≤ m := by
  have h : pStar + 2 ≤ Dsc := by rw [Dsc_def]; omega
  exact le_trans (by exact_mod_cast h) hm

/-- If `m` is a real number with `Dsc ≤ m`, then `pStar ≤ m`. -/
@[collatz_pos_dens "lem_c3_scale_room"]
theorem pStar_le_of_Dsc_le {m : ℝ} (hm : (Dsc : ℝ) ≤ m) : (pStar : ℝ) ≤ m := by
  linarith [pStar_add_two_le_of_Dsc_le hm]

end CollatzPosDens
