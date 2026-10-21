/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# The split level `ς(ι, m)`

For each index `ι : CollatzPosDens.FIndex` (either `o` or `b`) and real `m`, the split level is the
real number `ς(ι, m)`, with `ς(o, m) = 3m/2` and `ς(b, m) = 2m`.

## Main definitions

* `CollatzPosDens.gapSplit`: the split level `ς(ι, m) : ℝ`.

## Main results

* `CollatzPosDens.gapSplit_o`, `CollatzPosDens.gapSplit_b`: the values `ς(o, m) = 3m/2` and
  `ς(b, m) = 2m`.
* `CollatzPosDens.gapSplit_nonneg`, `CollatzPosDens.gapSplit_pos`: `ς(ι, m)` has the sign of `m`.
* `CollatzPosDens.gapSplit_mono`: `ς(ι, ·)` is monotone.
* `CollatzPosDens.le_gapSplit`: `3m/2 ≤ ς(ι, m)` for `m ≥ 0`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The split level `ς(ι, m) ∈ ℝ` at the index `ι` and the real level `m`: `ς(o, m) = 3m/2` and
`ς(b, m) = 2m`. -/
@[collatz_pos_dens "def_s02_split"]
noncomputable def gapSplit : FIndex → ℝ → ℝ
  | .o, m => 3 * m / 2
  | .b, m => 2 * m

/-- The split level at the original index. -/
@[simp]
theorem gapSplit_o (m : ℝ) : gapSplit .o m = 3 * m / 2 := rfl

/-- The split level at the bootstrap index. -/
@[simp]
theorem gapSplit_b (m : ℝ) : gapSplit .b m = 2 * m := rfl

/-- The split level is nonnegative at a nonnegative level. -/
theorem gapSplit_nonneg (ι : FIndex) {m : ℝ} (hm : 0 ≤ m) : 0 ≤ gapSplit ι m := by
  cases ι <;> simp <;> linarith

/-- The split level is positive at a positive level. -/
theorem gapSplit_pos (ι : FIndex) {m : ℝ} (hm : 0 < m) : 0 < gapSplit ι m := by
  cases ι <;> simp <;> linarith

/-- The split level is monotone in the level. -/
theorem gapSplit_mono (ι : FIndex) : Monotone (gapSplit ι) := by
  intro m m' h
  cases ι <;> simp <;> linarith

/-- At a nonnegative level, the split level is at least `3m/2`. -/
theorem le_gapSplit (ι : FIndex) {m : ℝ} (hm : 0 ≤ m) : 3 * m / 2 ≤ gapSplit ι m := by
  cases ι
  · exact le_rfl
  · rw [gapSplit_b]; linarith

end CollatzPosDens
