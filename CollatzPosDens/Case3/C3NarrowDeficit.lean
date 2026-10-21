/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3PacketDeficit

/-!
# The narrow deficit

For integers `c` and `o`, the *narrow deficit* is
`δ'_{c,o} = min (a_{c,o} / (c - 1), 1 - 2^{-16})`,
where `a_{c,o}` is the maximal packet deficit `CollatzPosDens.c3PacketDeficit c o`. It is the
amount by which a packet family for `(c,o)` lowers the normalised packet sum, capped at
`1 - 2^{-16}` so that `1 - δ'_{c,o} ≥ 2^{-16}` matches the floor of the paid reward.

## Main definitions

* `CollatzPosDens.c3NarrowDeficit c o`: the narrow deficit `δ'_{c,o}`.

## Main results

* `CollatzPosDens.c3NarrowDeficit_le_div`, `CollatzPosDens.c3NarrowDeficit_le_cap`: the two
  upper bounds of the minimum.
* `CollatzPosDens.c3NarrowDeficit_eq_div`, `CollatzPosDens.c3NarrowDeficit_eq_cap`: the value in
  each of the two cases.
* `CollatzPosDens.c3NarrowDeficit_nonneg`: `0 ≤ δ'_{c,o}` for `1 ≤ c`.
* `CollatzPosDens.c3NarrowDeficit_lt_one`: `δ'_{c,o} < 1`.

## Implementation notes

The quantity is only used for `3 ≤ c ≤ 16` and `1 ≤ o ≤ c`; the definition here is total in
the integers `c` and `o` (as is `CollatzPosDens.c3PacketDeficit`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The *narrow deficit* `δ'_{c,o} = min (a_{c,o} / (c - 1), 1 - 2^{-16})`, where `a_{c,o}` is
the maximal packet deficit `c3PacketDeficit c o`. -/
@[collatz_pos_dens "def_c3_narrow_deficit"]
def c3NarrowDeficit (c o : ℤ) : ℚ :=
  min (c3PacketDeficit c o / (c - 1)) (1 - (2 ^ 16 : ℚ)⁻¹)

/-- The narrow deficit is at most `c3PacketDeficit c o / (c - 1)`. -/
theorem c3NarrowDeficit_le_div (c o : ℤ) :
    c3NarrowDeficit c o ≤ c3PacketDeficit c o / (c - 1) :=
  min_le_left _ _

/-- The narrow deficit is at most `1 - 2^{-16}`. -/
theorem c3NarrowDeficit_le_cap (c o : ℤ) : c3NarrowDeficit c o ≤ 1 - (2 ^ 16 : ℚ)⁻¹ :=
  min_le_right _ _

/-- If `c3PacketDeficit c o / (c - 1) ≤ 1 - 2^{-16}`, the narrow deficit equals
`c3PacketDeficit c o / (c - 1)`. -/
theorem c3NarrowDeficit_eq_div {c o : ℤ}
    (h : c3PacketDeficit c o / (c - 1) ≤ 1 - (2 ^ 16 : ℚ)⁻¹) :
    c3NarrowDeficit c o = c3PacketDeficit c o / (c - 1) :=
  min_eq_left h

/-- If `1 - 2^{-16} ≤ c3PacketDeficit c o / (c - 1)`, the narrow deficit equals `1 - 2^{-16}`. -/
theorem c3NarrowDeficit_eq_cap {c o : ℤ}
    (h : 1 - (2 ^ 16 : ℚ)⁻¹ ≤ c3PacketDeficit c o / (c - 1)) :
    c3NarrowDeficit c o = 1 - (2 ^ 16 : ℚ)⁻¹ :=
  min_eq_right h

/-- The narrow deficit is strictly less than `1`. -/
theorem c3NarrowDeficit_lt_one (c o : ℤ) : c3NarrowDeficit c o < 1 :=
  (c3NarrowDeficit_le_cap c o).trans_lt (by norm_num)

/-- For `1 ≤ c`, the narrow deficit is nonnegative. -/
theorem c3NarrowDeficit_nonneg {c : ℤ} (hc : 1 ≤ c) (o : ℤ) : 0 ≤ c3NarrowDeficit c o := by
  refine le_min (div_nonneg (c3PacketDeficit_nonneg c o) ?_) (by norm_num)
  have : (1 : ℚ) ≤ c := by exact_mod_cast hc
  linarith

end CollatzPosDens
