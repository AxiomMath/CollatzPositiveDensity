/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Width

/-!
# The depth half-width of a central block

For an integer `b ≥ 9`, the depth half-width of a central block at level `b` is
$$\mathrm{dw}(b) = \begin{cases} \lfloor 3b/5\rfloor & b < 256,\\
  \mathrm{wd}(b) & b \ge 256,\end{cases}$$
where `wd` is the width of the barrier at level `b`.

## Main definitions

* `CollatzPosDens.dw`: the depth half-width.

## Main results

* `CollatzPosDens.dw_of_lt`, `CollatzPosDens.dw_of_le`: the two branches.
* `CollatzPosDens.dw_le_three_mul_div_five`: `dw b ≤ ⌊3b/5⌋`.
* `CollatzPosDens.dw_lt_self`: `dw b < b` for `0 < b`.

## Implementation notes

The function is defined on all of `ℕ`; the hypothesis `b ≥ 9` is not needed to make sense
of the definition, and is carried by the lemmas that use it instead, so that sums of `dw`
over arbitrary levels typecheck without side conditions.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The depth half-width `dw(b)`: `⌊3b/5⌋` if `b < 256`, and `wd b` otherwise. -/
@[collatz_pos_dens "def_s05_depth_width"]
noncomputable def dw (b : ℕ) : ℕ :=
  if b < 256 then 3 * b / 5 else wd b

/-- The depth half-width is `⌊3b/5⌋` if `b < 256`, and `wd b` otherwise. -/
theorem dw_def (b : ℕ) : dw b = if b < 256 then 3 * b / 5 else wd b := rfl

/-- Below level `256`, the depth half-width is `⌊3b/5⌋`. -/
theorem dw_of_lt {b : ℕ} (hb : b < 256) : dw b = 3 * b / 5 := ite_eq_left hb

/-- From level `256` on, the depth half-width is the barrier width `wd b`. -/
theorem dw_of_le {b : ℕ} (hb : 256 ≤ b) : dw b = wd b := ite_eq_right (by omega)

/-- The depth half-width is at most `⌊3b/5⌋`. -/
theorem dw_le_three_mul_div_five (b : ℕ) : dw b ≤ 3 * b / 5 := by
  unfold dw
  split_ifs
  · exact le_rfl
  · exact (wd_le_floor_sub_one b).trans (Nat.sub_le _ _)

/-- The depth half-width of a positive level is less than the level. -/
theorem dw_lt_self {b : ℕ} (hb : 0 < b) : dw b < b :=
  (dw_le_three_mul_div_five b).trans_lt (by omega)

/-- The depth half-width is at most the level. -/
theorem dw_le_self (b : ℕ) : dw b ≤ b :=
  (dw_le_three_mul_div_five b).trans (by omega)

end CollatzPosDens
