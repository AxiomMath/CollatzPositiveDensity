/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints

/-!
# The block point of a block

A block is a pair `β = (c, e)` of a word `c = (c₁, …, c_m)` of integers (its nonclosing letters)
and a closing letter `e ∈ {4, 5}`. Its block point is the lattice point
`bpt(β) = (m + 1, c₁ + ⋯ + c_m + e) ∈ 𝒫`: the total displacement of the `m + 1` letters of `β`.
Block points are added along a list of blocks, so they take values in the additive group `ℤ × ℤ`.

## Main definitions

* `CollatzPosDens.chBlockPoint`: the block point `bpt : List ℤ × ℤ → ℤ × ℤ`.

## Main results

* `CollatzPosDens.chBlockPoint_mem_bkPoints`: every block point lies in `𝒫`.
* `CollatzPosDens.chBlockPoint_cons`: `bpt(a :: c, e) = bpt(c, e) + (1, a)`.
* `CollatzPosDens.chBlockPoint_append`: `bpt(c ++ d, e) = bpt(d, e) + (|c|, ∑ c)`, where `∑ c`
  is the sum of the letters of `c`.

## Implementation notes

Words in `ℤ^{<ω}` are modelled as `List ℤ`, so the length `m` is `c.length`. The set of blocks
`𝔅 = ℤ^{<ω} × {4, 5}` is modelled by `List ℤ × ℤ`: the formula for `bpt` makes sense for every
integer closing letter, and the restriction `e ∈ {4, 5}` plays no role in it, so `chBlockPoint`
is defined on all of `List ℤ × ℤ`. As in `CollatzPosDens.bkPoints`, the point set `𝒫` is a
subset of `ℤ × ℤ`, so `bpt` takes values in `ℤ × ℤ` and membership in `𝒫` is the separate
statement `chBlockPoint_mem_bkPoints`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The block point `bpt(β) = (m + 1, c₁ + ⋯ + c_m + e)` of a block `β = (c, e)` with
`c = (c₁, …, c_m)`. -/
@[collatz_pos_dens "def_ch_block_point"]
def chBlockPoint (β : List ℤ × ℤ) : ℤ × ℤ := ((β.1.length : ℤ) + 1, β.1.sum + β.2)

/-- The block point of `(c, e)`, unfolded. -/
lemma chBlockPoint_mk (c : List ℤ) (e : ℤ) :
    chBlockPoint (c, e) = ((c.length : ℤ) + 1, c.sum + e) := rfl

/-- The first coordinate of the block point of a block `β` is the length of `β.1` plus one. -/
@[simp]
lemma chBlockPoint_fst (β : List ℤ × ℤ) : (chBlockPoint β).1 = β.1.length + 1 := rfl

/-- The second coordinate of the block point of a block `β` is the sum of the letters of `β.1`
plus the closing letter `β.2`. -/
@[simp]
lemma chBlockPoint_snd (β : List ℤ × ℤ) : (chBlockPoint β).2 = β.1.sum + β.2 := rfl

/-- Every block point lies in the lattice point set `𝒫`. -/
@[collatz_pos_dens "def_ch_block_point"]
lemma chBlockPoint_mem_bkPoints (β : List ℤ × ℤ) : chBlockPoint β ∈ bkPoints := by
  simp only [mem_bkPoints, bkJ, chBlockPoint_fst]
  omega

/-- A block with no nonclosing letters has block point `(1, e)`. -/
@[simp]
lemma chBlockPoint_nil (e : ℤ) : chBlockPoint ([], e) = (1, e) := by
  simp [chBlockPoint]

/-- Prepending a nonclosing letter `a` adds `(1, a)` to the block point. -/
lemma chBlockPoint_cons (a : ℤ) (c : List ℤ) (e : ℤ) :
    chBlockPoint (a :: c, e) = chBlockPoint (c, e) + (1, a) := by
  ext <;> simp [chBlockPoint]; ring

/-- Prepending a word `c` of nonclosing letters adds `(|c|, ∑ c)` to the block point, where `∑ c`
is the sum of the letters of `c`. -/
lemma chBlockPoint_append (c d : List ℤ) (e : ℤ) :
    chBlockPoint (c ++ d, e) = chBlockPoint (d, e) + ((c.length : ℤ), c.sum) := by
  ext <;> simp [chBlockPoint] <;> ring

end CollatzPosDens
