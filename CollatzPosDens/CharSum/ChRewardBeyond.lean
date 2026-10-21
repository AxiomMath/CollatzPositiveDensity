/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidReward

/-!
# The paid reward beyond the half level

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. If a point `p` has first coordinate
`j(p) > ⌊n/2⌋`, then the paid reward `R_c(p)` vanishes for every integer `c`. Indeed, the paid
reward then equals the baseline reward `R^old_c(p)`, and no point `q` with `j(q) = j(p)` is white;
this applies to `p` and to every `p - (0, k)`, so every indicator in `R^old_c(p)` vanishes, the set
`Adm_c(p)` of admissible packets is empty, and the packet coverage `M_c(p)` is `0`.

## Main results

* `CollatzPosDens.chPaidReward_eq_zero_of_half_lt_bkJ`: `R_c(p) = 0` when `j(p) > ⌊n/2⌋`.

## Implementation notes

The statement holds for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, as the paid reward is defined
on all of `ℤ × ℤ`; the hypothesis `p ∈ 𝒫` of the source is therefore omitted.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The paid reward `R_c(p)` vanishes for every integer `c` when `j(p) > ⌊n/2⌋`. -/
@[collatz_pos_dens "lem_ch_reward_beyond"]
theorem chPaidReward_eq_zero_of_half_lt_bkJ {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ)
    {p : ℤ × ℤ} (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) : chPaidReward n ξ ε c p = 0 :=
  chPaidReward_eq_zero_of_lt_bkJ hp

end CollatzPosDens
