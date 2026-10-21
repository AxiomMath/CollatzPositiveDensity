/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkExitWidthPow
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The exit width keeps `3 ε_* 9 ^ r` below `2 ^ s`

Let `s ∈ ℕ` and `r ≤ f_s`, where `f_s = ⌊(5s + 16) / 16⌋` is the exit width. Then
`3 ε_* 9 ^ r < 2 ^ s`. Indeed `9 ^ r ≤ 9 ^ f_s ≤ 9 * 2 ^ s`, so
`3 ε_* 9 ^ r ≤ 27 ε_* 2 ^ s < 2 ^ s`, because `0 < ε_*` and `27 ε_* = 999999 / 10⁶ < 1`.

## Main results

* `CollatzPosDens.three_mul_epsStar_mul_nine_pow_lt`: `3 ε_* 9 ^ r < 2 ^ s` whenever `r ≤ f_s`,
  in any linearly ordered field.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `r ≤ f_s`, `3 ε_* 9 ^ r < 2 ^ s`, in any linearly ordered field. -/
@[collatz_pos_dens "lem_bk_exit_width_bound"]
theorem three_mul_epsStar_mul_nine_pow_lt {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {s r : ℕ} (hr : r ≤ bkExitWidth s) :
    3 * (epsStar : K) * 9 ^ r < 2 ^ s := by
  obtain ⟨h0, h1⟩ := epsStar_mem_bkRange (K := K)
  have h9 : (9 : K) ^ r ≤ 9 * 2 ^ s := by
    have := (Nat.pow_le_pow_right (by norm_num : 0 < 9) hr).trans (nine_pow_bkExitWidth_le s)
    exact_mod_cast this
  have h2 : (0 : K) < 2 ^ s := by positivity
  calc 3 * (epsStar : K) * 9 ^ r ≤ 3 * epsStar * (9 * 2 ^ s) := by gcongr
    _ = (27 * epsStar) * 2 ^ s := by ring
    _ < 1 * 2 ^ s := by gcongr; linarith
    _ = 2 ^ s := one_mul _

end CollatzPosDens
