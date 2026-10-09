/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.EpsStar
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A bound on `3 ε_* 9^{⌊(5s+16)/16⌋}`

Write `f(s) = ⌊(5s + 16)/16⌋`. For every `s ∈ ℕ` we have `3 ε_* 9^{f(s)} < 2^s`, where
`ε_* = 8/217` is `CollatzPosDens.epsStar`. Clearing denominators, this is
`24 · 9^{f(s)} < 217 · 2^s`, which follows from the integer bound `3 · 9^{f(s)} ≤ 27 · 2^s`
because `8 · 27 = 216 < 217`. The integer bound is proved by strong induction: the sixteen cases
`0 ≤ s ≤ 15` are checked directly, and for `s ≥ 16` one has `f(s) = f(s - 16) + 5` and
`9^5 = 59049 ≤ 65536 = 2^16`.

## Main results

* `CollatzPosDens.three_mul_nine_pow_le_twentyseven_mul_two_pow`: the integer bound
  `3 · 9^{⌊(5s+16)/16⌋} ≤ 27 · 2^s`.
* `CollatzPosDens.three_mul_epsStar_mul_nine_pow_lt_two_pow`: `3 ε_* 9^{⌊(5s+16)/16⌋} < 2^s`
  with `ε_*` cast into any linearly ordered field, e.g. `ℚ` or `ℝ`.

## Implementation notes

The floor `⌊(5s+16)/16⌋` of a nonnegative rational with natural numerator is written as the
natural-number division `(5 * s + 16) / 16`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `s ∈ ℕ`, `3 · 9^{⌊(5s+16)/16⌋} ≤ 27 · 2^s`. -/
theorem three_mul_nine_pow_le_twentyseven_mul_two_pow (s : ℕ) :
    3 * 9 ^ ((5 * s + 16) / 16) ≤ 27 * 2 ^ s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    by_cases hs : s < 16
    · interval_cases s <;> norm_num
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 16 := ⟨s - 16, by omega⟩
      rw [show (5 * (t + 16) + 16) / 16 = (5 * t + 16) / 16 + 5 by omega, pow_add, pow_add]
      nlinarith [ih t (by omega), pow_pos (show (0 : ℕ) < 9 by norm_num) ((5 * t + 16) / 16)]

/-- For every `s ∈ ℕ`, `3 ε_* 9^{⌊(5s+16)/16⌋} < 2^s` in any linearly ordered field, where
`ε_* = 8/217` is `CollatzPosDens.epsStar`. -/
@[collatz_pos_dens "lem_bk_exit_room"]
theorem three_mul_epsStar_mul_nine_pow_lt_two_pow {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (s : ℕ) :
    3 * (epsStar : K) * 9 ^ ((5 * s + 16) / 16) < 2 ^ s := by
  have hK : (3 : K) * 9 ^ ((5 * s + 16) / 16) ≤ 27 * 2 ^ s := by
    exact_mod_cast three_mul_nine_pow_le_twentyseven_mul_two_pow s
  have h2 : (0 : K) < 2 ^ s := by positivity
  rw [epsStar_cast]
  nlinarith

end CollatzPosDens
