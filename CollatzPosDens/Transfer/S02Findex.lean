/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Fintype.Card

/-!
# The Fourier parameter indices

The analytic recipe constants come in two families, one for the original parameter set and one for
the bootstrap parameter set. They are indexed by the two-element type `𝔍 = {o, b}`, where `o`
denotes the original parameter set and `b` the bootstrap one.

## Main definitions

* `CollatzPosDens.FIndex`: the two-element type `𝔍 = {o, b}` of Fourier parameter indices.

## Main results

* `CollatzPosDens.FIndex.eq_o_or_eq_b`: every index is `o` or `b`.
* `CollatzPosDens.FIndex.card_eq_two`: there are exactly two indices.
-/

@[expose] public section

namespace CollatzPosDens

/-- The Fourier parameter indices `𝔍 = {o, b}`: `o` is the original parameter set and `b` the
bootstrap parameter set. -/
@[collatz_pos_dens "def_s02_findex"]
inductive FIndex
  /-- The original parameter set. -/
  | o
  /-- The bootstrap parameter set. -/
  | b
  deriving DecidableEq, Repr

namespace FIndex

/-- `FIndex` is finite, with elements `o` and `b`. -/
instance : Fintype FIndex where
  elems := {o, b}
  complete x := by cases x <;> simp

/-- The default index is `o`. -/
instance : Inhabited FIndex := ⟨o⟩

/-- The two indices are distinct. -/
theorem o_ne_b : o ≠ b := by decide

/-- Every index is `o` or `b`. -/
theorem eq_o_or_eq_b (ι : FIndex) : ι = o ∨ ι = b := by
  cases ι <;> simp

/-- There are exactly two Fourier parameter indices. -/
theorem card_eq_two : Fintype.card FIndex = 2 := rfl

end FIndex

end CollatzPosDens
