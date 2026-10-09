/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing

/-!
# The first-crossing family is prefix-disjoint

No word of the first-crossing family `𝒲(b, u, K)` is a proper prefix of another: if
`w = w'_{≤ s}` with `s = |w| < |w'|`, then `ℓ_b < s < |w'|`, so the definition of `𝒲(b, u, K)`
applied to `w'` gives `A(w) < H_{b,u}(s)`, while applied to `w` it gives `A(w) ≥ H_{b,u}(s)`.

## Main results

* `CollatzPosDens.isPrefixFree_firstCrossing`: `𝒲(b, u, K)` is prefix-free.

## Implementation notes

A prefix-disjoint family is expressed by Mathlib's `InformationTheory.IsPrefixFree`. As in
`CollatzPosDens.firstCrossing`, `b` and `K` range over all natural numbers, rather than only
`b ≥ 1` and `K ≥ 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The first-crossing family `𝒲(b, u, K)` is prefix-disjoint: no element is a prefix of a
different element. -/
@[collatz_pos_dens "lem_first_crossing_prefix_disjoint"]
theorem isPrefixFree_firstCrossing (b : ℕ) (u : ℤ) (K : ℕ) :
    InformationTheory.IsPrefixFree (firstCrossing b u K) := by
  intro w hw w' hw' hpre
  by_contra hne
  have hlen : w.length < w'.length :=
    lt_of_le_of_ne hpre.length_le fun h => hne (hpre.eq_of_length h)
  have htake : w'.take w.length = w := by
    obtain ⟨t, rfl⟩ := hpre
    simp
  have h1 := valSum_take_lt_of_mem_firstCrossing hw' (lb_lt_length_of_mem_firstCrossing hw).le
    hlen
  rw [htake] at h1
  exact (barrier_le_valSum_of_mem_firstCrossing hw).not_gt h1

end CollatzPosDens
