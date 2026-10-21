/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Lower bound for the scale increment `e_b`

For every integer `b ≥ 1` the scale increment satisfies `e_b ≥ max(1, b/100)`: indeed
`e_b = ⌈b/100⌉ ≥ b/100 > 0`, and a positive integer is at least `1`.

## Main results

* `CollatzPosDens.eb_ge_ceil_div_hundred`: `⌈b/100⌉ = (b + 99) / 100 ≤ e_b`.
* `CollatzPosDens.eb_lower`: `max 1 (b / 100) ≤ e_b` in `ℝ` for `b ≥ 1`.

## Implementation notes

The natural-number ceiling `⌈b/100⌉` is written `(b + 99) / 100`, matching the definition of
`eb`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `e_b ≥ ⌈b/100⌉`, with the ceiling written as `(b + 99) / 100`. -/
theorem eb_ge_ceil_div_hundred (b : ℕ) : (b + 99) / 100 ≤ eb b := le_rfl

/-- For every integer `b ≥ 1`, `e_b ≥ max(1, b/100)`. -/
@[collatz_pos_dens "lem_eb_lower"]
theorem eb_lower {b : ℕ} (hb : 1 ≤ b) : max 1 ((b : ℝ) / 100) ≤ eb b := by
  refine max_le (mod_cast one_le_eb_of_pos hb) ?_
  rw [div_le_iff₀ (by norm_num)]
  exact_mod_cast (by rw [eb_eq]; omega : b ≤ eb b * 100)

end CollatzPosDens
