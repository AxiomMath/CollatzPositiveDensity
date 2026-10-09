/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# The path of a concatenation of block lists

For a base point `o`, block lists `u ∈ 𝔅^a` and `f ∈ 𝔅^b`, the path of the concatenation
`uf` from `o` first follows the path of `u` and then, from the endpoint `x_a(o, u)`, the path
of `f`: `x_{a+t}(o, uf) = x_t(x_a(o, u), f)` for every `t ∈ ℕ`. This rests on the additivity
`Bp_{a+t}(uf) = Bp_a(u) + Bp_t(f)` of block path points.

## Main results

* `CollatzPosDens.chBlockPath_append_add`: `Bp_{a+t}(uf) = Bp_a(u) + Bp_t(f)` for `|u| = a`.
* `CollatzPosDens.trPath_append_add`: `x_{a+t}(o, uf) = x_t(x_a(o, u), f)` for `|u| = a`.

## Implementation notes

The statement is proved for every base point `o ∈ ℤ × ℤ` and every pair of lists of
`List ℤ × ℤ`, without the hypotheses `o ∈ 𝒫` and that the closing letters lie in `{4, 5}`:
neither is used. The length `b` of `f` plays no role either, and the identity
`Bp_{a+t}(uf) = Bp_a(u) + Bp_t(f)` holds for every `t`, since `chBlockPath` is constant beyond
the length of the list.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Additivity of block path points along a concatenation: `Bp_{a+t}(uf) = Bp_a(u) + Bp_t(f)`
when `u` has length `a`. -/
lemma chBlockPath_append_add (u f : List (List ℤ × ℤ)) {a : ℕ} (hu : u.length = a) (t : ℕ) :
    chBlockPath (u ++ f) (a + t) = chBlockPath u a + chBlockPath f t := by
  subst hu
  rw [chBlockPath, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.map_append, List.sum_append, chBlockPath, List.take_length]
  rfl

/-- The path of a concatenation: `x_{a+t}(o, uf) = x_t(x_a(o, u), f)` for `u ∈ 𝔅^a`. -/
@[collatz_pos_dens "lem_tr_concat_shift"]
theorem trPath_append_add (o : ℤ × ℤ) (u f : List (List ℤ × ℤ)) {a : ℕ} (hu : u.length = a)
    (t : ℕ) : trPath o (u ++ f) (a + t) = trPath (trPath o u a) f t := by
  rw [trPath_eq_add_chBlockPath, trPath_eq_add_chBlockPath, trPath_eq_add_chBlockPath,
    chBlockPath_append_add u f hu, add_assoc]

end CollatzPosDens
