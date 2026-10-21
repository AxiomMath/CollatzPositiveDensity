/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr

/-!
# The clipping width

For integers `m ≥ 1` and `n ≥ 2`, the *clipping width* is the natural number
$$w^{\mathrm{clp}}_{m,n} = \lceil\sqrt{256\, m \log n}\,\rceil + \lceil 64 \log n\rceil,$$
with `log` the natural logarithm.

## Main definitions

* `CollatzPosDens.clipWidth m n`: the clipping width `w^clp_{m,n}`.

## Main results

* `CollatzPosDens.sqrt_le_clipWidth`: `√(256 m log n) ≤ w^clp_{m,n}`.
* `CollatzPosDens.log_le_clipWidth`: `64 log n ≤ w^clp_{m,n}`.
* `CollatzPosDens.clipWidth_lt`: `w^clp_{m,n} < √(256 m log n) + 64 log n + 2`.
* `CollatzPosDens.clipWidth_mono_left`: `w^clp_{m,n}` is monotone in `m`.

## Implementation notes

Both summands are nonnegative reals (`Real.log` is nonnegative on natural numbers), so the
ceilings are taken with `Nat.ceil`. The definition is stated for all `m n : ℕ`, not only for
`m ≥ 1` and `n ≥ 2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping width `w^clp_{m,n} = ⌈√(256 m log n)⌉ + ⌈64 log n⌉ ∈ ℕ`, with `log` the
natural logarithm. -/
@[collatz_pos_dens "def_s06_clip_width"]
noncomputable def clipWidth (m n : ℕ) : ℕ :=
  ⌈√(256 * (m : ℝ) * Real.log n)⌉₊ + ⌈64 * Real.log n⌉₊

/-- Unfolding lemma for `clipWidth`. -/
theorem clipWidth_def (m n : ℕ) :
    clipWidth m n = ⌈√(256 * (m : ℝ) * Real.log n)⌉₊ + ⌈64 * Real.log n⌉₊ :=
  rfl

/-- The square-root summand is at most the clipping width: `√(256 m log n) ≤ w^clp_{m,n}`. -/
theorem sqrt_le_clipWidth (m n : ℕ) :
    √(256 * (m : ℝ) * Real.log n) ≤ clipWidth m n := by
  rw [clipWidth_def, Nat.cast_add]
  exact le_add_of_le_of_nonneg (Nat.le_ceil _) (Nat.cast_nonneg _)

/-- The logarithmic summand is at most the clipping width: `64 log n ≤ w^clp_{m,n}`. -/
theorem log_le_clipWidth (m n : ℕ) : 64 * Real.log n ≤ clipWidth m n := by
  rw [clipWidth_def, Nat.cast_add]
  exact le_add_of_nonneg_of_le (Nat.cast_nonneg _) (Nat.le_ceil _)

/-- Upper bound for the clipping width: `w^clp_{m,n} < √(256 m log n) + 64 log n + 2`. -/
theorem clipWidth_lt (m n : ℕ) :
    (clipWidth m n : ℝ) < √(256 * (m : ℝ) * Real.log n) + 64 * Real.log n + 2 := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have h1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg (256 * (m : ℝ) * Real.log n))
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 64 * Real.log n by positivity)
  rw [clipWidth_def, Nat.cast_add]
  linarith

/-- The clipping width is monotone in `m`. -/
theorem clipWidth_mono_left {m m' : ℕ} (h : m ≤ m') (n : ℕ) : clipWidth m n ≤ clipWidth m' n := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [clipWidth_def, clipWidth_def]
  gcongr

end CollatzPosDens
