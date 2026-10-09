/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Hb

/-!
# Finiteness of the first-crossing families

For a level `b`, an integer offset `u` and an overshoot bound `K`, the first-crossing family
`𝒲(b, u, K)` is finite. Every word of `𝒲(b, u, K)` has length `s ≤ h_b` and valuation sum
`A(w) ≤ H_{b,u}(s) + K`, which is bounded by `B = max {H_{b,u}(t) + K : t ≤ h_b}`; since every
letter is a positive integer, there are only finitely many words of valuation sum at most `B`.

## Main results

* `CollatzPosDens.firstCrossing_finite`: the family `𝒲(b, u, K)` is finite.

## Implementation notes

The source takes integers `b ≥ 1` and `K ≥ 0`; here `b` and `K` are arbitrary natural numbers,
so the statement covers `b = 0` as well. Rather than bounding the length and the letters
separately, finiteness is derived from the bound on the valuation sum alone: a word with
`A(w) ≤ M` has length at most `M` and letters at most `M`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Finiteness of the first-crossing families.** For every level `b`, offset `u` and
overshoot bound `K`, the first-crossing family `𝒲(b, u, K)` is finite. -/
@[collatz_pos_dens "lem_first_crossing_finite"]
theorem firstCrossing_finite (b : ℕ) (u : ℤ) (K : ℕ) : (firstCrossing b u K).Finite := by
  set M : ℕ := (Finset.range (hb b + 1)).sup fun t => (barrier b u t + K).toNat
  refine (Word.finite_setOf_valSum_le M).subset fun w hw => ?_
  have hlen := length_le_hb_of_mem_firstCrossing hw
  have hval := valSum_le_barrier_add_of_mem_firstCrossing hw
  have hM : (barrier b u w.length + K).toNat ≤ M :=
    Finset.le_sup (f := fun t => (barrier b u t + K).toNat)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hlen))
  change w.valSum ≤ M
  omega

end CollatzPosDens
