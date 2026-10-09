/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Growth of `(4/3)^b` against `16^{⌈b/100⌉}`

For every integer `b ≥ 256` we have `(4/3)^b ≥ 4 · 16^{⌈b/100⌉}`.
Since `4^5 = 1024 > 972 = 4 · 3^5`, the power `(4/3)^b` grows at least like `4^{⌊b/5⌋}`,
while `4 · 16^k = 4^{1 + 2k}`, and `1 + 2k ≤ ⌊b/5⌋` whenever `100 (k - 1) < b` and `b ≥ 256`.

## Main results

* `CollatzPosDens.four_mul_sixteen_pow_mul_three_pow_le_four_pow`: the cleared-denominator
  form `4 · 16^k · 3^b ≤ 4^b` in `ℕ`, for any `k` with `100 k < b + 100`.
* `CollatzPosDens.four_mul_sixteen_pow_ceil_le_four_thirds_pow`:
  `4 · 16^{⌈b/100⌉} ≤ (4/3)^b` in `ℝ`, for `b ≥ 256`.

## Implementation notes

Rather than comparing through `(4/3)^{100} > 16^3`, the proof uses the sharper per-five-steps
comparison `4 · 3^5 < 4^5`, which keeps all numerals small. The only property of the ceiling
used is `⌈b/100⌉ < b/100 + 1`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `100 k < b + 100` (i.e. `b > 100 (k - 1)`) and `b ≥ 256`, then `4 · 16^k · 3^b ≤ 4^b`:
the inequality `(4/3)^b ≥ 4 · 16^k` with denominators cleared, in `ℕ`. -/
theorem four_mul_sixteen_pow_mul_three_pow_le_four_pow {b k : ℕ} (hb : 256 ≤ b)
    (hk : 100 * k < b + 100) : 4 * 16 ^ k * 3 ^ b ≤ 4 ^ b := by
  have h1 : 4 * 16 ^ k ≤ 4 ^ (b / 5) := by
    rw [show 4 * 16 ^ k = 4 ^ (1 + 2 * k) by rw [pow_add, pow_mul]; norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb5 : b = 5 * (b / 5) + b % 5 := (Nat.div_add_mod b 5).symm
  generalize b / 5 = q at h1 hb5
  generalize b % 5 = r at hb5
  subst hb5
  calc 4 * 16 ^ k * 3 ^ (5 * q + r) ≤ 4 ^ q * 3 ^ (5 * q + r) :=
        Nat.mul_le_mul_right _ h1
    _ = (4 * 243) ^ q * 3 ^ r := by
      rw [pow_add, pow_mul, mul_pow]
      norm_num
      ring
    _ ≤ 1024 ^ q * 4 ^ r := by gcongr <;> norm_num
    _ = 4 ^ (5 * q + r) := by
      rw [pow_add, pow_mul]
      norm_num

/-- **A power comparison.** For every integer `b ≥ 256`, `(4/3)^b ≥ 4 · 16^{⌈b/100⌉}`. -/
@[collatz_pos_dens "lem_s05_four_thirds"]
theorem four_mul_sixteen_pow_ceil_le_four_thirds_pow {b : ℕ} (hb : 256 ≤ b) :
    4 * (16 : ℝ) ^ ⌈(b : ℝ) / 100⌉₊ ≤ (4 / 3 : ℝ) ^ b := by
  have hk : 100 * ⌈(b : ℝ) / 100⌉₊ < b + 100 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (b : ℝ) / 100 by positivity)
    have : (100 : ℝ) * ⌈(b : ℝ) / 100⌉₊ < b + 100 := by linarith
    exact_mod_cast this
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast four_mul_sixteen_pow_mul_three_pow_le_four_pow hb hk

end CollatzPosDens
