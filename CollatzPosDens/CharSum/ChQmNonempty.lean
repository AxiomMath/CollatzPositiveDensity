/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQm

/-!
# The set defining `Q_m` is nonempty

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a real exponent `A` and an integer
`m ≥ 0`, the weighted supremum `Q_m` is the supremum of the set
`{d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ J ∸ m}`, where `J = ⌊n/2⌋`. This set is nonempty: the point
`(J + 1, 0)` lies in `𝒫` and satisfies `J + 1 ≥ J ∸ m`, so its weighted value belongs to the set.

## Main results

* `CollatzPosDens.chQm_set_nonempty`: the set whose supremum defines `Q_m` is nonempty.

## Implementation notes

The statement holds for every real exponent `A`, with no sign assumption on `A`. The witness
point `(J + 1, 0)` lies in `𝒫` since its first coordinate is positive.

## References

* [Mazur, *Collatz positive density*], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `{d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ ⌊n/2⌋ ∸ m}` whose supremum defines `Q_m` is
nonempty: it contains the weighted value at the point `(⌊n/2⌋ + 1, 0)`. -/
@[collatz_pos_dens "lem_ch_Qm_nonempty"]
theorem chQm_set_nonempty (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (A : ℝ) (m : ℕ) :
    {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
      x = (chDist n p : ℝ) ^ A * chQ n ξ ε p}.Nonempty := by
  refine ⟨_, (((n / 2 + 1 : ℕ) : ℤ), 0), ?_, ?_, rfl⟩
  · simp only [mem_bkPoints, bkJ]; omega
  · simp only [bkJ]; omega

end CollatzPosDens
