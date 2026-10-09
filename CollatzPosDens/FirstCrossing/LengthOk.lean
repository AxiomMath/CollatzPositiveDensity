/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.Maps.Word

/-!
# The length restriction `Λ_{b,u}(w)`

For a natural number `b`, an integer `u` and a word `w`, the length restriction
`Λ_{b,u}(w)` is the proposition
$$2|w| \le H_{b,u}(|w|) + \lfloor b/8 \rfloor,$$
where `H_{b,u}` is `CollatzPosDens.barrier`: the word is short enough that twice its length
stays below the barrier at its own length, up to the slack `⌊b/8⌋`.

## Main definitions

* `CollatzPosDens.LengthOk`: the proposition `Λ_{b,u}(w)`.

## Main results

* `CollatzPosDens.lengthOk_iff`: the unfolding of `Λ_{b,u}(w)`.

## Implementation notes

The parameter `b` is a natural number, and `⌊b/8⌋` is natural-number division, cast to
`ℤ`. The inequality is stated in `ℤ`, so `LengthOk b u` is a decidable predicate.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The length restriction `Λ_{b,u}(w)`: `2|w| ≤ H_{b,u}(|w|) + ⌊b/8⌋`. -/
@[collatz_pos_dens "def_length_ok"]
def LengthOk (b : ℕ) (u : ℤ) (w : Word) : Prop :=
  2 * (w.length : ℤ) ≤ barrier b u w.length + ((b / 8 : ℕ) : ℤ)

/-- `Λ_{b,u}(w)` holds iff `2|w| ≤ H_{b,u}(|w|) + ⌊b/8⌋`. -/
theorem lengthOk_iff (b : ℕ) (u : ℤ) (w : Word) :
    LengthOk b u w ↔ 2 * (w.length : ℤ) ≤ barrier b u w.length + ((b / 8 : ℕ) : ℤ) :=
  Iff.rfl

/-- The length restriction `Λ_{b,u}` is decidable. -/
noncomputable instance LengthOk.instDecidablePred (b : ℕ) (u : ℤ) :
    DecidablePred (LengthOk b u) := fun w =>
  inferInstanceAs (Decidable (2 * (w.length : ℤ) ≤ barrier b u w.length + ((b / 8 : ℕ) : ℤ)))

end CollatzPosDens
