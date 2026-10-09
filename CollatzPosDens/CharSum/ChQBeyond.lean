/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQfiniteBeyond

/-!
# The renewal function beyond the cut-off

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. If `j(p) > ⌊n/2⌋`, then the renewal
function `chQ n ξ ε p`, which is `chQFinite n ξ ε (n / 2) p`, equals `1`, since
`chQFinite n ξ ε m p = 1` whenever `j(p) > m`.

## Main results

* `CollatzPosDens.chQ_eq_one_of_lt_bkJ`: if `j(p) > ⌊n/2⌋` then `Q(p) = 1`.

## Implementation notes

The base point `p` ranges over all of `ℤ × ℤ`; no hypothesis `p ∈ 𝒫` is imposed.

## References

* [Mazur, *Collatz positive density*], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The renewal function beyond the cut-off.** If `j(p) > ⌊n/2⌋`, then `Q(p) = 1`. -/
@[collatz_pos_dens "lem_ch_Q_beyond"]
theorem chQ_eq_one_of_lt_bkJ (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {p : ℤ × ℤ}
    (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) : chQ n ξ ε p = 1 := by
  rw [chQ_def]
  exact chQFinite_eq_one_of_lt_bkJ n ξ ε (n / 2) hp

end CollatzPosDens
