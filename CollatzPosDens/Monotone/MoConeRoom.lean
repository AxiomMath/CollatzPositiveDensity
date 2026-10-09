/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dpt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Room left after a cone exit

Let `m` be an integer with `m ≥ Dpt` and `log m ≥ 1`, let `s ∈ ℕ` with `s ≤ m / (log m)^2`, and
let `r` be an integer with `r ≤ ⌊(5s + 16)/16⌋`. Then `r + D1 < m`.

Indeed `(log m)^2 ≥ 1` gives `s ≤ m`, so `r ≤ (5s + 16)/16 ≤ 5m/16 + 1`; and since
`Dpt = 2 D1 + 344`, `D1 ≤ (m - 344)/2`. Hence `r + D1 ≤ 13m/16 - 171 < m`.

## Main results

* `CollatzPosDens.moConeRoom`: `r + D1 < m` under the hypotheses above.

## Implementation notes

The thresholds `Dpt`, `D1 ∈ ℚ` and the integers `m`, `r`, `s` are all compared in `ℝ`, where the
logarithm lives; the floor is the integer floor `Int.floor` of the real number `(5s + 16)/16`.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `m ≥ Dpt` is an integer with `log m ≥ 1`, `s ∈ ℕ` satisfies `s ≤ m / (log m)^2` and the
integer `r` satisfies `r ≤ ⌊(5s + 16)/16⌋`, then `r + D1 < m`. -/
@[collatz_pos_dens "lem_mo_cone_room"]
theorem moConeRoom {m : ℤ} (hm : (Dpt : ℝ) ≤ m) (hlog : 1 ≤ Real.log m) {s : ℕ}
    (hs : (s : ℝ) ≤ m / Real.log m ^ 2) {r : ℤ}
    (hr : r ≤ ⌊((5 * s + 16 : ℝ) / 16)⌋) :
    (r : ℝ) + D1 < m := by
  have hDpt : (Dpt : ℝ) = 2 * D1 + 344 := by
    rw [Dpt_def]
    push_cast
    ring
  have hD1 : (0 : ℝ) < D1 := by exact_mod_cast D1_pos
  have hsm : (s : ℝ) ≤ m := hs.trans (div_le_self (by linarith) (by nlinarith))
  have hr' : (r : ℝ) ≤ (5 * s + 16) / 16 := (Int.cast_le.mpr hr).trans (Int.floor_le _)
  linarith

end CollatzPosDens
