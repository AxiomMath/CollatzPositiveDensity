/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxBlockMarginal

/-!
# The marginal identity for the geometric mass

Let `t ≤ h` and let `E ⊆ ℤ_{≥1}^t` be a set of words of length `t`. Then the words
`v ∈ ℤ_{≥1}^h` whose length-`t` prefix `v_{≤ t}` lies in `E` have the same geometric mass as `E`:
`𝐩({v ∈ ℤ_{≥1}^h : v_{≤ t} ∈ E}) = 𝐩(E)`.

The prefix `v_{≤ t}` is the block of `v` starting at position `0`, so this is the block-marginal
identity `geomMass_setOf_block_mem` with `i = 0`.

## Main results

* `CollatzPosDens.geomMass_setOf_take_mem`: the marginal identity.

## Implementation notes

Words are lists of positive naturals; `ℤ_{≥1}^t` is the set of words of length `t` and the
prefix `v_{≤ t}` is `List.take t v`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Marginal identity.** For `t ≤ h` and a set `E` of words of length `t`,
`𝐩({v ∈ ℤ_{≥1}^h : v_{≤ t} ∈ E}) = 𝐩(E)`. -/
@[collatz_pos_dens "lem_fc_marginal"]
theorem geomMass_setOf_take_mem {t h : ℕ} (ht : t ≤ h) {E : Set Word}
    (hE : ∀ w ∈ E, w.length = t) :
    geomMass {v : Word | v.length = h ∧ v.take t ∈ E} = geomMass E :=
  geomMass_setOf_block_mem (i := 0) (by omega) hE

end CollatzPosDens
