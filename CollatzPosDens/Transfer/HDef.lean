/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Beta
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Positivity

/-!
# The window length `h_*`

For `q ∈ ℕ` the window length is the natural number `h_*(q) := ⌈4 β_*(q) / 35⌉ + 8192`, where
`β_*` is the scale schedule. Since `β_*(q)` is a natural number, the ceiling is the ceiling
division `(4 β_*(q) + 34) / 35` of `ℕ`. As `β_*` is strictly monotone, `h_*` is monotone, and
`8192 ≤ h_*(q)` always.

## Main definitions

* `CollatzPosDens.windowLength`: the window length `h_*(q)`.

## Main results

* `CollatzPosDens.windowLength_eq_div`: `h_*(q) = (4 β_*(q) + 34) / 35 + 8192`.
* `CollatzPosDens.windowLength_monotone`: `h_*` is monotone.
* `CollatzPosDens.le_windowLength`: `8192 ≤ h_*(q)`.
* `CollatzPosDens.windowLength_mul_ge`: `4 β_*(q) + 35 · 8192 ≤ 35 h_*(q)`.
* `CollatzPosDens.windowLength_mul_le`: `35 h_*(q) ≤ 4 β_*(q) + 34 + 35 · 8192`.

## Implementation notes

The ceiling is taken in `ℝ` with `Nat.ceil`; `windowLength_eq_div` converts it to natural-number
arithmetic.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The window length `h_*(q) := ⌈4 β_*(q) / 35⌉ + 8192 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_h"]
noncomputable def windowLength (q : ℕ) : ℕ := ⌈(4 * betaStar q : ℝ) / 35⌉₊ + 8192

/-- The window length is `h_*(q) = ⌈4 β_*(q) / 35⌉ + 8192`. -/
theorem windowLength_def (q : ℕ) :
    windowLength q = ⌈(4 * betaStar q : ℝ) / 35⌉₊ + 8192 := rfl

/-- The ceiling in `h_*` is the ceiling division of natural numbers. -/
theorem windowLength_eq_div (q : ℕ) :
    windowLength q = (4 * betaStar q + 34) / 35 + 8192 := by
  rw [windowLength_def]
  congr 1
  set b := betaStar q
  have h : ((4 * b : ℕ) : ℝ) = 4 * (b : ℝ) := by push_cast; rfl
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ (by norm_num), ← h]
    have key : 4 * b ≤ (4 * b + 34) / 35 * 35 := by omega
    exact_mod_cast key
  · rcases Nat.eq_zero_or_pos ((4 * b + 34) / 35) with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · have hm : (4 * b + 34) / 35 = ((4 * b + 34) / 35 - 1) + 1 := by omega
      rw [hm, Nat.add_one_le_iff, Nat.lt_ceil, lt_div_iff₀ (by norm_num), ← h]
      have key : ((4 * b + 34) / 35 - 1) * 35 < 4 * b := by omega
      exact_mod_cast key

/-- The window length satisfies `8192 ≤ h_*(q)`. -/
theorem le_windowLength (q : ℕ) : 8192 ≤ windowLength q := by
  rw [windowLength_eq_div]; omega

/-- The window length `h_*(q)` is positive. -/
theorem windowLength_pos (q : ℕ) : 0 < windowLength q :=
  lt_of_lt_of_le (by norm_num) (le_windowLength q)

/-- The window length satisfies `4 β_*(q) + 35 · 8192 ≤ 35 h_*(q)`. -/
theorem windowLength_mul_ge (q : ℕ) : 4 * betaStar q + 35 * 8192 ≤ 35 * windowLength q := by
  rw [windowLength_eq_div]; omega

/-- The window length satisfies `35 h_*(q) ≤ 4 β_*(q) + 34 + 35 · 8192`. -/
theorem windowLength_mul_le (q : ℕ) :
    35 * windowLength q ≤ 4 * betaStar q + 34 + 35 * 8192 := by
  rw [windowLength_eq_div]; omega

/-- The window length `h_*` is monotone. -/
theorem windowLength_monotone : Monotone windowLength := by
  intro p q hpq
  rw [windowLength_eq_div, windowLength_eq_div]
  have := betaStar_monotone hpq
  omega

end CollatzPosDens
