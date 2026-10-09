/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChQRange

/-!
# Nonnegativity of `Q_m`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a real exponent `A` and an integer
`m ≥ 0`, the weighted supremum `Q_m = sup {d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ ⌊n/2⌋ ∸ m}` is
nonnegative: every element of the defining set is the product of the positive weight
`d_J(p)^A` (as `d_J(p) ≥ 1`) and the nonnegative value `Q(p)`.

## Main results

* `CollatzPosDens.chQm_nonneg`: `0 ≤ Q_m`.

## Implementation notes

The statement holds for every real `A`, not only `A ≥ 0`, since a real power of a positive base
is positive. The real supremum `sSup` of a set of nonnegative reals is nonnegative whether or not
the set is bounded above (an unbounded or empty set has supremum `0`), so neither nonemptiness
nor the upper bound `max(m, 1)^A` is needed.

## References

* [Mazur, *Collatz positive density*], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every real `A` and every `m ≥ 0`, the weighted supremum `chQm n ξ ε A m` is nonnegative. -/
@[collatz_pos_dens "lem_ch_Qm_bounded"]
theorem chQm_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (A : ℝ) (m : ℕ) :
    0 ≤ chQm n ξ ε A m := by
  refine Real.sSup_nonneg fun x ⟨p, _, _, hx⟩ => hx ▸ ?_
  exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast (chDist_pos n p).le) A)
    (chQ_range n ξ ε p).1

end CollatzPosDens
