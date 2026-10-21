/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Qstar

/-!
# The value of the conductor

With the generation threshold `N_* = 9853`, the conductor `q_* = ⌈1668728 · (101/100)^{N_*}⌉` is
the 49-digit integer
$$d = 632239220553191787820523 \cdot 10^{25}
  + 3964253799528824016493120.$$
Indeed the two exact integer comparisons
`(d - 1) · 100^9853 < 1668728 · 101^9853 < d · 100^9853` give
`d - 1 < 1668728 · (101/100)^9853 < d`, so the ceiling is `d`.

## Main results

* `CollatzPosDens.conductor_value`: the decimal value of `q_*`.

## Implementation notes

The two integer comparisons are checked by kernel evaluation in `ℕ` of the 49-digit literal
against `101^9853` and `100^9853` (the kernel's natural-number arithmetic is accelerated by
GMP); no rational arithmetic is evaluated by the kernel.
-/

@[expose] public section

namespace CollatzPosDens

/-- The conductor `conductor` is the 49-digit integer
`q_* =632239220553191787820523 · 10^25 + 3964253799528824016493120`. -/
@[collatz_pos_dens "lem_ph_qstar_value"]
theorem conductor_value :
    conductor = 632239220553191787820523 * 10 ^ 25 +
      3964253799528824016493120 := by
  rw [conductor_def, generationThreshold_def, Nat.ceil_eq_iff (by norm_num), div_pow,
    ← mul_div_assoc, lt_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor
  · exact_mod_cast (by decide +kernel :
      (632239220553191787820523 * 10 ^ 25 +
        3964253799528824016493120 - 1) * 100 ^ 9853 < 1668728 * 101 ^ 9853)
  · exact_mod_cast (by decide +kernel : 1668728 * 101 ^ 9853 ≤
      (632239220553191787820523 * 10 ^ 25 +
        3964253799528824016493120) * 100 ^ 9853)

end CollatzPosDens
