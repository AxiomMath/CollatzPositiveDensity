/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Tstar
public import Mathlib.Algebra.Order.Floor.Div

/-!
# The clearance time after a small gap

For a Fourier index `ι` and a gap threshold `G ∈ ℕ`, the *clearance time*
`h^st_G(ι) := ⌈G/4⌉ + T_*(ι) + 1 ∈ ℕ` bounds the time after which a stopping trace, standing at
a black point of gap less than `G`, reaches its next stop. Along a live path the height grows
by at least `4` per step, so after `⌈G/4⌉` steps the path has passed the top `l_*` of the
current column; the next `T_*(ι) + 1` steps contain a point which is not white on the low event.

## Main definitions

* `CollatzPosDens.trStageHold ι G`: the clearance time `h^st_G(ι)`.

## Main results

* `CollatzPosDens.trStageHold_eq_div`: `h^st_G(ι) = (G + 3) / 4 + T_*(ι) + 1`.
* `CollatzPosDens.add_four_mul_le_four_mul_trStageHold`:
  `G + 4 (T_*(ι) + 1) ≤ 4 h^st_G(ι)`.
* `CollatzPosDens.trStageHold_b_4096`: `h^st_4096(b) = 1193`.

## Implementation notes

The ceiling `⌈G/4⌉` of a natural number `G` is Mathlib's ceiling division `G ⌈/⌉ 4` of natural
numbers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The clearance time after a small gap, `h^st_G(ι) := ⌈G/4⌉ + T_*(ι) + 1`. -/
@[collatz_pos_dens "def_c3_stage_hold"]
def trStageHold (ι : FIndex) (G : ℕ) : ℕ := G ⌈/⌉ 4 + tStar ι + 1

/-- `h^st_G(ι) = ⌈G/4⌉ + T_*(ι) + 1`. -/
theorem trStageHold_def (ι : FIndex) (G : ℕ) : trStageHold ι G = G ⌈/⌉ 4 + tStar ι + 1 := rfl

/-- The ceiling division as a floor division: `h^st_G(ι) = (G + 3) / 4 + T_*(ι) + 1`. -/
theorem trStageHold_eq_div (ι : FIndex) (G : ℕ) :
    trStageHold ι G = (G + 3) / 4 + tStar ι + 1 := by
  rw [trStageHold_def, Nat.ceilDiv_eq_add_pred_div]
  rfl

/-- The first `⌈G/4⌉` steps of the clearance time cover a height `G`:
`G + 4 (T_*(ι) + 1) ≤ 4 h^st_G(ι)`. -/
theorem add_four_mul_le_four_mul_trStageHold (ι : FIndex) (G : ℕ) :
    G + 4 * (tStar ι + 1) ≤ 4 * trStageHold ι G := by
  rw [trStageHold_eq_div]
  omega

/-- `T_*(ι) < h^st_G(ι)`. -/
theorem tStar_lt_trStageHold (ι : FIndex) (G : ℕ) : tStar ι < trStageHold ι G := by
  rw [trStageHold_def]
  omega

/-- The clearance time is positive. -/
theorem trStageHold_pos (ι : FIndex) (G : ℕ) : 0 < trStageHold ι G :=
  (Nat.zero_le _).trans_lt (tStar_lt_trStageHold ι G)

/-- `h^st_4096(b) = 1024 + 168 + 1 = 1193`. -/
theorem trStageHold_b_4096 : trStageHold .b 4096 = 1193 := by
  rw [trStageHold_eq_div, tStar_b]

end CollatzPosDens
