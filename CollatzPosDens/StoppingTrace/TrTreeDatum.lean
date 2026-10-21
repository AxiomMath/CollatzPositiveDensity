/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.StoppingTrace.TrTreePolicy

/-!
# Tree data

For `H ∈ ℕ`, a *tree datum of height `H`* is a pair `(cut, W)` of a cutoff function
`cut : ℕ → ℕ` and a bounded policy `W ⊆ ℕ × ℕ × ℕ` such that

1. `c ≤ cut h` for every `(r, h, c) ∈ W`;
2. `cut 0 ≤ 16` and `cut 0 ≤ H`;
3. `cut (h + c) ≤ 16` and `h + c + cut (h + c) ≤ H` for every `(r, h, c) ∈ W`.

The cutoff `cut h` bounds the length of a retained continuation started at depth `h`; conditions
(2) and (3) say that every depth reached by the tree (the root `0` and every `h + c`) has cutoff at
most `16` and leaves room for a full retained continuation below height `H`. A number `k ∈ ℕ` in
place of `cut` stands for the constant function `fun _ => k`.

## Main definitions

* `CollatzPosDens.TreeDatum H`: a tree datum of height `H`.

## Main results

* `CollatzPosDens.TreeDatum.add_le`: every `(r, h, c) ∈ W` has `h + c ≤ H`.
* `CollatzPosDens.TreeDatum.cut_le_sixteen_of_reached`,
  `CollatzPosDens.TreeDatum.add_cut_le_of_reached`: the cutoff conditions at every depth reached
  by the tree (the root `0` or `h + c` for `(r, h, c) ∈ W`).
* `CollatzPosDens.TreeDatum.mono`: a tree datum of height `H` is one of every height `H' ≥ H`.

## Implementation notes

Triples `(r, h, c)` are encoded as `ℕ × ℕ × ℕ` with `p.1 = r`, `p.2.1 = h`, `p.2.2 = c`, as in
`CollatzPosDens.IsBoundedPolicy`. The convention that a number `k` stands for a constant cutoff is
realised by writing `fun _ => k` for the field `cut`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- A *tree datum of height `H`*: a cutoff function `cut : ℕ → ℕ` and a bounded policy `W` such
that (i) `c ≤ cut h` for every `(r, h, c) ∈ W`; (ii) `cut 0 ≤ 16` and `cut 0 ≤ H`; and
(iii) `cut (h + c) ≤ 16` and `h + c + cut (h + c) ≤ H` for every `(r, h, c) ∈ W`.
A number `k` in place of `cut` stands for the constant function `fun _ => k`. -/
@[collatz_pos_dens "def_tr_tree_datum"]
structure TreeDatum (H : ℕ) where
  /-- The cutoff function. -/
  cut : ℕ → ℕ
  /-- The policy of triples `(r, h, c)`. -/
  W : Set (ℕ × ℕ × ℕ)
  /-- The policy is bounded. -/
  isBoundedPolicy : IsBoundedPolicy W
  /-- (i) Every continuation length is at most the cutoff at its starting depth. -/
  le_cut : ∀ p ∈ W, p.2.2 ≤ cut p.2.1
  /-- (ii) The cutoff at the root is at most `16`. -/
  cut_zero_le_sixteen : cut 0 ≤ 16
  /-- (ii) The cutoff at the root is at most `H`. -/
  cut_zero_le : cut 0 ≤ H
  /-- (iii) The cutoff at every reached depth `h + c` is at most `16`. -/
  cut_add_le_sixteen : ∀ p ∈ W, cut (p.2.1 + p.2.2) ≤ 16
  /-- (iii) A retained continuation from every reached depth `h + c` stays below height `H`. -/
  add_add_cut_le : ∀ p ∈ W, p.2.1 + p.2.2 + cut (p.2.1 + p.2.2) ≤ H

namespace TreeDatum

variable {H : ℕ} (D : TreeDatum H)

/-- Every triple `(r, h, c)` of the policy of a tree datum of height `H` has `h + c ≤ H`. -/
theorem add_le {p : ℕ × ℕ × ℕ} (hp : p ∈ D.W) : p.2.1 + p.2.2 ≤ H :=
  (Nat.le_add_right _ _).trans (D.add_add_cut_le p hp)

/-- Every triple `(r, h, c)` of the policy of a tree datum has `c ≥ 2`. -/
theorem two_le {p : ℕ × ℕ × ℕ} (hp : p ∈ D.W) : 2 ≤ p.2.2 :=
  D.isBoundedPolicy.two_le hp

/-- The cutoff of a tree datum at the root and at every reached depth `h + c` is at most `16`. -/
theorem cut_le_sixteen_of_reached {h : ℕ} (hh : h = 0 ∨ ∃ p ∈ D.W, h = p.2.1 + p.2.2) :
    D.cut h ≤ 16 := by
  rcases hh with rfl | ⟨p, hp, rfl⟩
  · exact D.cut_zero_le_sixteen
  · exact D.cut_add_le_sixteen p hp

/-- At the root and at every reached depth `h`, a retained continuation of length at most
`cut h` stays below height `H`: `h + cut h ≤ H`. -/
theorem add_cut_le_of_reached {h : ℕ} (hh : h = 0 ∨ ∃ p ∈ D.W, h = p.2.1 + p.2.2) :
    h + D.cut h ≤ H := by
  rcases hh with rfl | ⟨p, hp, rfl⟩
  · simpa using D.cut_zero_le
  · exact D.add_add_cut_le p hp

/-- A tree datum of height `H` is a tree datum of every height `H' ≥ H`. -/
def mono {H' : ℕ} (hH : H ≤ H') : TreeDatum H' where
  cut := D.cut
  W := D.W
  isBoundedPolicy := D.isBoundedPolicy
  le_cut := D.le_cut
  cut_zero_le_sixteen := D.cut_zero_le_sixteen
  cut_zero_le := D.cut_zero_le.trans hH
  cut_add_le_sixteen := D.cut_add_le_sixteen
  add_add_cut_le p hp := (D.add_add_cut_le p hp).trans hH

/-- Raising the height keeps the cutoff function. -/
@[simp]
theorem mono_cut {H' : ℕ} (hH : H ≤ H') : (D.mono hH).cut = D.cut := rfl

/-- Raising the height keeps the policy. -/
@[simp]
theorem mono_W {H' : ℕ} (hH : H ≤ H') : (D.mono hH).W = D.W := rfl

end TreeDatum

end CollatzPosDens
