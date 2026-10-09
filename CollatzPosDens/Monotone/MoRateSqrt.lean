/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CollatzPosDens.Monotone.MoRate
public import CollatzPosDens.Monotone.MoLogSqrt

/-!
# A square-root bound on `moRate`

For a real `A ≥ 0` and every integer `m ≥ 1`, the rate `moRate A m = 4A(1 + log m)/m`
satisfies `moRate A m ≤ 8A/√m`. Since `log m ≤ √m` and `1 ≤ √m`, we have
`1 + log m ≤ 2√m`, whence `moRate A m ≤ 8A√m/m = 8A/√m`.

## Main results

* `CollatzPosDens.moRate_le_div_sqrt`: `moRate A m ≤ 8 * A / √m` for `0 ≤ A`, `1 ≤ m`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For a real `A ≥ 0` and every integer `m ≥ 1`, `moRate A m ≤ 8A/√m`. -/
@[collatz_pos_dens "lem_mo_rate_sqrt"]
theorem moRate_le_div_sqrt {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m) :
    moRate A m ≤ 8 * A / Real.sqrt m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.2 hm'
  have hlog : Real.log m ≤ Real.sqrt m := log_le_sqrt (by linarith)
  rw [moRate_def, div_le_div_iff₀ (by linarith) (by linarith)]
  calc 4 * A * (1 + Real.log m) * Real.sqrt m
      ≤ 4 * A * (2 * Real.sqrt m) * Real.sqrt m := by
        gcongr
        linarith
    _ = 8 * A * m := by
      linear_combination 8 * A * Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ m)

end CollatzPosDens
