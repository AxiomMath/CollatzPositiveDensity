/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQfinite

/-!
# The renewal function `Q`

Fix a level `n`, a residue `ξ : ResidueGroup n` and a threshold `ε`. The renewal function
`Q(p)` is the finite-horizon white product `Q^{(K)}(p)` of `CollatzPosDens.chQFinite` at the
horizon `K = ⌊n/2⌋`.

## Main definitions

* `CollatzPosDens.chQ n ξ ε p`: the renewal function `Q(p) = Q^{(⌊n/2⌋)}(p)`.

## Main results

* `CollatzPosDens.chQ_def`: the defining equation `Q(p) = Q^{(⌊n/2⌋)}(p)`.
* `CollatzPosDens.chQ_nonneg`: `Q(p) ≥ 0`.

## Implementation notes

The horizon `⌊n/2⌋` is the natural-number division `n / 2`. The base point `p` ranges over all
of `ℤ × ℤ`, not only over the admissible points `𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The renewal function `Q(p) = Q^{(⌊n/2⌋)}(p)`: the finite-horizon white product for
`n, ξ, ε` at horizon `⌊n/2⌋`. -/
@[collatz_pos_dens "def_ch_Q"]
noncomputable def chQ (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℝ :=
  chQFinite n ξ ε (n / 2) p

/-- Unfolding lemma for `chQ`: `Q(p) = Q^{(⌊n/2⌋)}(p)`. -/
theorem chQ_def (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    chQ n ξ ε p = chQFinite n ξ ε (n / 2) p :=
  rfl

/-- The renewal function is nonnegative. -/
theorem chQ_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : 0 ≤ chQ n ξ ε p :=
  chQFinite_nonneg _ _ _ _ _

end CollatzPosDens
