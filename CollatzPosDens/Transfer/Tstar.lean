/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex

/-!
# The low-count threshold `T_*(ι)`

For a Fourier parameter index `ι ∈ {o, b}`, the low-count threshold `T_*(ι)` is the natural
number defined by `T_*(o) = 192` and `T_*(b) = 168`. An admissible start is *low* when its count
of white points along the stopping trace up to time `P_* - 1` is at most `T_*(ι)`.

## Main definitions

* `CollatzPosDens.tStar`: the natural number `T_*(ι)`.

## Main results

* `CollatzPosDens.tStar_o`, `CollatzPosDens.tStar_b`: `T_*(o) = 192` and `T_*(b) = 168`.
* `CollatzPosDens.tStar_o_succ`, `CollatzPosDens.tStar_b_succ`: `T_*(o) + 1 = 193` and
  `T_*(b) + 1 = 169`.
* `CollatzPosDens.tStar_pos`: `0 < T_*(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The low-count threshold `T_*(ι)`, equal to `192` for `ι = o` and `168` for `ι = b`. -/
@[collatz_pos_dens "def_Tstar"]
def tStar : FIndex → ℕ
  | .o => 192
  | .b => 168

/-- The low-count threshold at the original index equals `192`. -/
@[simp] theorem tStar_o : tStar .o = 192 := rfl

/-- The low-count threshold at the bootstrap index equals `168`. -/
@[simp] theorem tStar_b : tStar .b = 168 := rfl

/-- `T_*(o) + 1 = 193`. -/
theorem tStar_o_succ : tStar .o + 1 = 193 := rfl

/-- `T_*(b) + 1 = 169`. -/
theorem tStar_b_succ : tStar .b + 1 = 169 := rfl

/-- The low-count threshold is positive. -/
theorem tStar_pos (ι : FIndex) : 0 < tStar ι := by
  cases ι <;> decide

end CollatzPosDens
