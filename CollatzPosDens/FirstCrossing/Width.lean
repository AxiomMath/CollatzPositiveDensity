/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Clog

/-!
# The width `wd(b)`

For an integer `b ≥ 2`, the width of the barrier at level `b` is
$$\mathrm{wd}(b) = \min\bigl(\lceil\sqrt{32\,b\,\mathrm{lg}(b)}\,\rceil,\
  \lfloor 3b/5\rfloor - 1\bigr),$$
where `lg b = ⌈log₂ b⌉` is the binary ceiling logarithm.

## Main definitions

* `CollatzPosDens.wd`: the width `min ⌈√(32 b lg b)⌉₊ (⌊3b/5⌋ - 1)`.

## Main results

* `CollatzPosDens.wd_le_ceil_sqrt`, `CollatzPosDens.wd_le_floor_sub_one`: the two
  upper bounds.
* `CollatzPosDens.le_wd_iff`: `k ≤ wd b` exactly when `k` is below both bounds.
* `CollatzPosDens.ceil_le_wd`: if `x ≤ √(32 b lg b)` and `⌈x⌉₊ ≤ ⌊3b/5⌋ - 1` then
  `⌈x⌉₊ ≤ wd b`.
* `CollatzPosDens.wd_lt_self`: `wd b < b` for `0 < b`.

## Implementation notes

The width is defined for every natural number `b`, with truncated subtraction in
`⌊3b/5⌋ - 1`. For `b ≥ 2` one has `⌊3b/5⌋ ≥ 1`, so the truncated difference is the integer
one and the definition agrees with the formula above; for `b ∈ {0, 1}` it gives `wd b = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The width `wd(b) = min(⌈√(32 b lg b)⌉, ⌊3b/5⌋ - 1)` of level `b`. -/
@[collatz_pos_dens "def_width"]
noncomputable def wd (b : ℕ) : ℕ :=
  min ⌈√(32 * (b : ℝ) * (lg b : ℝ))⌉₊ (3 * b / 5 - 1)

/-- The width `wd b` equals `min ⌈√(32 b lg b)⌉₊ (⌊3b/5⌋ - 1)`. -/
theorem wd_def (b : ℕ) :
    wd b = min ⌈√(32 * (b : ℝ) * (lg b : ℝ))⌉₊ (3 * b / 5 - 1) := rfl

/-- The width is at most `⌈√(32 b lg b)⌉`. -/
theorem wd_le_ceil_sqrt (b : ℕ) : wd b ≤ ⌈√(32 * (b : ℝ) * (lg b : ℝ))⌉₊ :=
  min_le_left _ _

/-- The width is at most `⌊3b/5⌋ - 1`. -/
theorem wd_le_floor_sub_one (b : ℕ) : wd b ≤ 3 * b / 5 - 1 :=
  min_le_right _ _

/-- `k ≤ wd b` exactly when `k` lies below both defining bounds. -/
theorem le_wd_iff {b k : ℕ} :
    k ≤ wd b ↔ k ≤ ⌈√(32 * (b : ℝ) * (lg b : ℝ))⌉₊ ∧ k ≤ 3 * b / 5 - 1 :=
  le_min_iff

/-- If `x ≤ √(32 b lg b)` and `⌈x⌉ ≤ ⌊3b/5⌋ - 1`, then `⌈x⌉ ≤ wd b`. -/
theorem ceil_le_wd {b : ℕ} {x : ℝ} (hx : x ≤ √(32 * (b : ℝ) * (lg b : ℝ)))
    (h : ⌈x⌉₊ ≤ 3 * b / 5 - 1) : ⌈x⌉₊ ≤ wd b :=
  le_wd_iff.2 ⟨Nat.ceil_mono hx, h⟩

/-- The width of a positive level is less than the level. -/
theorem wd_lt_self {b : ℕ} (hb : 0 < b) : wd b < b :=
  (wd_le_floor_sub_one b).trans_lt (by omega)

end CollatzPosDens
