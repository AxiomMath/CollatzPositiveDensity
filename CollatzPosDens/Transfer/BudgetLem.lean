/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Budget
public import CollatzPosDens.Transfer.Lc
public import CollatzPosDens.Transfer.TraceReserve
public import CollatzPosDens.Transfer.Z
public import CollatzPosDens.Transfer.Aexp

/-!
# The six-term budget is less than one

The six-term budget
`Bud = 1/8000 + c_cont (2 + 272 (H_* + 1) Q_pack) / K_* + c_cont / P_T + 1/60 + 1/P_W
  + c_cont 2^{-43}`
is an explicit rational number, since the Taylor sums `P_T` and `P_W` are finite sums of
rationals. Exact evaluation shows `14975371 · 10^{-18} < 1 - Bud < 14975372 · 10^{-18}`; in
particular `Bud < 1`.

## Main results

* `CollatzPosDens.Bud_lt_one`: the six-term budget is less than one.
* `CollatzPosDens.Bud_lt_one_sub`, `CollatzPosDens.one_sub_lt_Bud`: the lower and
  upper bounds of the slack `1 - Bud`.

## Implementation notes

The proof is an exact rational evaluation: the definitions of `P_T` and `P_W` are unfolded into
their finitely many terms and `norm_num` evaluates the resulting closed rational expression.
-/

@[expose] public section

namespace CollatzPosDens

/-- The lower bound on the slack: `Bud < 1 - 14975371 · 10^{-18}`. -/
theorem Bud_lt_one_sub : Bud < 1 - 14975371 / 10 ^ 18 := by
  rw [Bud_def, PT_def, PW_def, PW_exponent_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Lstar_eq, ccont_eq,
    Qpack_eq, Hstar_cast, Kstar_cast]
  norm_num

/-- The upper bound on the slack: `1 - 14975372 · 10^{-18} < Bud`. -/
theorem one_sub_lt_Bud : 1 - 14975372 / 10 ^ 18 < Bud := by
  rw [Bud_def, PT_def, PW_def, PW_exponent_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Lstar_eq, ccont_eq,
    Qpack_eq, Hstar_cast, Kstar_cast]
  norm_num

/-- The six-term budget is less than one. -/
@[collatz_pos_dens "lem_s02_budget"]
theorem Bud_lt_one : Bud < 1 :=
  Bud_lt_one_sub.trans (by norm_num)

end CollatzPosDens
