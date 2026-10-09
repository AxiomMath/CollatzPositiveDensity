/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.FieldSimp
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Weight

/-!
# The affine identity of an inverse orbit

For every rational `R` and every word `w`, the starting point of the inverse orbit is an affine
function of its source: `R = ω(w) · src(w, R) + off(w)`, where `ω(w) = 3 ^ |w| 2 ^ {-A(w)}` is
the weight and `off(w)` the offset of `w`.

## Main results

* `CollatzPosDens.eq_weight_mul_src_add_off`: `R = ω(w) src(w, R) + off(w)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The affine identity `R = ω(w) src(w, R) + off(w)` of the inverse orbit of `R` along `w`. -/
@[collatz_pos_dens "lem_affine_identity"]
theorem eq_weight_mul_src_add_off (w : Word) (R : ℚ) :
    R = Word.weight w * src w R + off w := by
  induction w generalizing R with
  | nil => simp
  | cons a w ih =>
    have h := ih (invStep a R)
    rw [src_cons, Word.weight_cons, off_cons, mul_assoc,
      eq_sub_of_add_eq h.symm, invStep]
    field_simp
    ring

end CollatzPosDens
