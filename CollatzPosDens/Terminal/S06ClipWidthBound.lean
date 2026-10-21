/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.S02EUpper
public import CollatzPosDens.Terminal.S06ClipWidth

/-!
# Size of the central window

For natural numbers `m, n` with `m ≤ n` and `n ≥ 3`, the clipping width
`w = CollatzPosDens.clipWidth m n` satisfies `2 w + 1 ≤ 256 √(n log n)`. Since `e < 3 ≤ n`,
`log n ≥ 1`, so `log n ≤ √(n log n)` and `1 ≤ √(n log n)`; together with
`√(256 m log n) ≤ 16 √(n log n)` and `w < √(256 m log n) + 64 log n + 2` this gives
`2 w + 1 < 165 √(n log n)`.

## Main results

* `CollatzPosDens.two_mul_clipWidth_add_one_le`: `2 w^clp_{m,n} + 1 ≤ 256 √(n log n)`.

## Implementation notes

The source assumes `1 ≤ m ≤ n`; the bound holds for `m = 0` as well and is stated for every
`m ≤ n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Size of the central window.** For `m ≤ n` and `n ≥ 3`,
`2 w^clp_{m,n} + 1 ≤ 256 √(n log n)`. -/
@[collatz_pos_dens "lem_s06_clip_width_bound"]
theorem two_mul_clipWidth_add_one_le {m n : ℕ} (hmn : m ≤ n) (hn : 3 ≤ n) :
    2 * (clipWidth m n : ℝ) + 1 ≤ 256 * √(n * Real.log n) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hL1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_68_div_25]
  have hLn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hS1 : 1 ≤ √(n * Real.log n) := Real.one_le_sqrt.2 (by nlinarith)
  have hLS : Real.log n ≤ √(n * Real.log n) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq : √(256 * (m : ℝ) * Real.log n) ≤ 16 * √(n * Real.log n) := by
    calc √(256 * (m : ℝ) * Real.log n) ≤ √(256 * (n : ℝ) * Real.log n) :=
          Real.sqrt_le_sqrt (by gcongr)
      _ = 16 * √(n * Real.log n) := by
        rw [show (256 : ℝ) * n * Real.log n = 16 ^ 2 * (n * Real.log n) by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hw := clipWidth_lt m n
  linarith

end CollatzPosDens
