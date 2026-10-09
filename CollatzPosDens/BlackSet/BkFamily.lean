/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle

/-!
# The canonical family of triangles

Fix a level `n`, a residue `ξ` and a tolerance `ε`. The *canonical family* `bkFamily n ξ ε` is
the set of canonical triangles `bkCanonTriangle n ξ ε p hp` at the points `p ∈ bkPoints` that
are black, i.e. satisfy `BkBlack n ξ ε p`.

## Main definitions

* `CollatzPosDens.bkFamily n ξ ε`: the canonical family, a set of triangles.

## Main results

* `CollatzPosDens.mem_bkFamily`: a triangle lies in `bkFamily n ξ ε` iff it is the canonical
  triangle at some black point of `bkPoints`.
* `CollatzPosDens.bkCanonTriangle_mem_bkFamily`: the canonical triangle at every black point of
  `bkPoints` lies in `bkFamily n ξ ε`.
* `CollatzPosDens.forall_mem_bkFamily`, `CollatzPosDens.exists_mem_bkFamily`: quantifying over
  `bkFamily n ξ ε` is quantifying over black points of `bkPoints`.
* `CollatzPosDens.bkFamily_eq_empty_iff`: `bkFamily n ξ ε` is empty iff `bkPoints` has no black
  points.

## Implementation notes

The canonical triangle `bkCanonTriangle n ξ ε p hp` is defined only for `p ∈ bkPoints`, where
its row start `bkRowStart n ξ ε p` is at least `1`. The family is therefore written as the set
of triangles of the form `bkCanonTriangle n ξ ε p hp` with `p ∈ bkPoints` black, rather than as
an image under a total function.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ} {Δ : BkTriangle}

/-- The canonical family: the set of canonical triangles `bkCanonTriangle n ξ ε p hp` at the
black points `p ∈ bkPoints`. -/
@[collatz_pos_dens "def_bk_family"]
def bkFamily (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) : Set BkTriangle :=
  {Δ | ∃ p, ∃ hp : p ∈ bkPoints, BkBlack n ξ ε p ∧ bkCanonTriangle n ξ ε p hp = Δ}

/-- A triangle lies in the canonical family iff it is the canonical triangle at some black
`p ∈ bkPoints`. -/
theorem mem_bkFamily :
    Δ ∈ bkFamily n ξ ε ↔
      ∃ p, ∃ hp : p ∈ bkPoints, BkBlack n ξ ε p ∧ bkCanonTriangle n ξ ε p hp = Δ :=
  Iff.rfl

/-- The canonical triangle at a black point lies in the canonical family. -/
theorem bkCanonTriangle_mem_bkFamily (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    bkCanonTriangle n ξ ε p hp ∈ bkFamily n ξ ε :=
  ⟨p, hp, hb, rfl⟩

/-- A property holds on the canonical family iff it holds for the canonical triangle
at every black `p ∈ bkPoints`. -/
theorem forall_mem_bkFamily {P : BkTriangle → Prop} :
    (∀ Δ ∈ bkFamily n ξ ε, P Δ) ↔
      ∀ p (hp : p ∈ bkPoints), BkBlack n ξ ε p → P (bkCanonTriangle n ξ ε p hp) := by
  constructor
  · intro h p hp hb
    exact h _ (bkCanonTriangle_mem_bkFamily hp hb)
  · rintro h _ ⟨p, hp, hb, rfl⟩
    exact h p hp hb

/-- Some member of the canonical family has a property iff the canonical triangle at
some black `p ∈ bkPoints` has it. -/
theorem exists_mem_bkFamily {P : BkTriangle → Prop} :
    (∃ Δ ∈ bkFamily n ξ ε, P Δ) ↔
      ∃ p, ∃ hp : p ∈ bkPoints, BkBlack n ξ ε p ∧ P (bkCanonTriangle n ξ ε p hp) := by
  constructor
  · rintro ⟨_, ⟨p, hp, hb, rfl⟩, h⟩
    exact ⟨p, hp, hb, h⟩
  · rintro ⟨p, hp, hb, h⟩
    exact ⟨_, bkCanonTriangle_mem_bkFamily hp hb, h⟩

/-- The canonical family is empty iff `bkPoints` has no black points. -/
theorem bkFamily_eq_empty_iff :
    bkFamily n ξ ε = ∅ ↔ ∀ p ∈ bkPoints, ¬BkBlack n ξ ε p :=
  Set.eq_empty_iff_forall_notMem.trans (forall_mem_bkFamily (P := fun _ ↦ False))

end CollatzPosDens
