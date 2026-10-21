/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Width

/-!
# The block length bound `len⁺(b)`

For an integer `b ≥ 2` the block length bound is
$$\mathrm{len}^+(b) = \begin{cases} h_b & b < 2^{40},\\ b + \mathrm{wd}(b) & b \ge 2^{40},
\end{cases}$$
where `h_b = b + ⌊3b/5⌋` is the scale parameter and `wd(b)` is the width of level `b`. It bounds
the length of the words in the block at level `b`.

## Main definitions

* `CollatzPosDens.lenPlus`: the block length bound `len⁺(b)`.

## Main results

* `CollatzPosDens.lenPlus_of_lt`, `CollatzPosDens.lenPlus_of_le`: the two branches.
* `CollatzPosDens.le_lenPlus`: `b ≤ len⁺(b)`.
* `CollatzPosDens.lenPlus_le_hb`: `len⁺(b) ≤ h_b`.

## Implementation notes

The bound is defined for every natural number `b`; it is only used for `b ≥ 2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The block length bound: `len⁺(b) = h_b` if `b < 2^40`, and `len⁺(b) = b + wd(b)` otherwise. -/
@[collatz_pos_dens "def_ph_block_len"]
noncomputable def lenPlus (b : ℕ) : ℕ := if b < 2 ^ 40 then hb b else b + wd b

/-- Below `2^40`, the block length bound is `h_b`. -/
theorem lenPlus_of_lt {b : ℕ} (h : b < 2 ^ 40) : lenPlus b = hb b := ite_eq_left h

/-- From `2^40` on, the block length bound is `b + wd(b)`. -/
theorem lenPlus_of_le {b : ℕ} (h : 2 ^ 40 ≤ b) : lenPlus b = b + wd b :=
  ite_eq_right (Nat.not_lt.mpr h)

/-- `b ≤ len⁺(b)`. -/
theorem le_lenPlus (b : ℕ) : b ≤ lenPlus b := by
  unfold lenPlus
  split_ifs
  · exact le_hb b
  · exact Nat.le_add_right b _

/-- `len⁺(b) ≤ h_b`. -/
theorem lenPlus_le_hb (b : ℕ) : lenPlus b ≤ hb b := by
  unfold lenPlus
  split_ifs
  · exact le_rfl
  · have := wd_le_floor_sub_one b
    rw [hb_eq]
    omega

/-- `len⁺(b) ≤ 2b`. -/
theorem lenPlus_le_two_mul (b : ℕ) : lenPlus b ≤ 2 * b :=
  (lenPlus_le_hb b).trans (hb_le_two_mul b)

end CollatzPosDens
