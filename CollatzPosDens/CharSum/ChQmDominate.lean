/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChQmSetBound

/-!
# The weighted supremum `Q_m` dominates its weighted values

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a real `A ≥ 0`, an integer
`m ≥ 0` and `p ∈ 𝒫` with `j(p) ≥ ⌊n/2⌋ ∸ m`, we have `d_J(p)^A Q(p) ≤ Q_m`: the left side lies
in the set whose supremum is `Q_m`, and that set is bounded above by `max(m, 1)^A`.

## Main results

* `CollatzPosDens.chQm_dominate`: `d_J(p)^A Q(p) ≤ Q_m`.

## Implementation notes

The power is the real power `Real.rpow`, matching `CollatzPosDens.chQm`. The threshold `ε`
is arbitrary, since the bound on the set defining `Q_m` holds for every `ε`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For real `A ≥ 0`, an integer `m ≥ 0` and `p ∈ 𝒫` with `j(p) ≥ ⌊n/2⌋ ∸ m`, the weighted
value `d_J(p)^A Q(p)` is at most `Q_m`. -/
@[collatz_pos_dens "lem_ch_Qm_dominate"]
theorem chQm_dominate (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A) (m : ℕ)
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) (hj : ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p) :
    (chDist n p : ℝ) ^ A * chQ n ξ ε p ≤ chQm n ξ ε A m :=
  le_chQm (chQm_set_bddAbove n ξ ε hA m) hp hj

end CollatzPosDens
