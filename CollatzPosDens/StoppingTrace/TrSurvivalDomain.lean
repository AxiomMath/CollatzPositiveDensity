/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ

/-!
# The fresh path stays in the strip

Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, let `e` be an entry point and `m ∈ ℕ` with `j(e) + m = J`. If an
atom `a ∈ 𝒜_n` lies outside the bad event `Bad^e_m(ι)`, then its fresh path stays at level at
most `J` up to time `P_*(ι)`: `j(y^e_t(a)) ≤ J` for every `t ≤ P_*(ι)`. Indeed, outside
`Bad^e_m(ι)` we have `400 (j(y^e_{P_*(ι)}(a)) - j(e)) < 317m ≤ 400m`, so `j(y^e_{P_*(ι)}(a)) < J`,
and the `j`-coordinate is nondecreasing along the path.

## Main results

* `CollatzPosDens.bkJ_trFreshPath_le_of_notMem_trBad`: the survival bound.

## Implementation notes

The statement assumes neither `n ≥ 1`, nor `e ∈ 𝒫`, nor that `ξ ∈ G_n` is a unit: monotonicity
of the `j`-coordinate along a block path holds for every starting point and every block list.
The level `J = ⌊n/2⌋` is the integer cast of the natural-number quotient `n / 2`.

## References

* [Mazur, *Collatz positive density*], §9.12.
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ι ∈ 𝔍`. Outside the bad event `Bad^e_m(ι)` with `j(e) + m = ⌊n/2⌋`, the fresh path of
an atom of `𝒜_n` stays at level at most `⌊n/2⌋` up to time `P_*(ι)`. -/
@[collatz_pos_dens "lem_tr_survival_domain"]
theorem bkJ_trFreshPath_le_of_notMem_trBad {ι : FIndex} {n : ℕ} {e : ℤ × ℤ} {m : ℕ}
    (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) (hb : a ∉ trBad ι n e m) {t : ℕ} (ht : t ≤ pStar ι) :
    bkJ (trFreshPath e a t) ≤ ((n / 2 : ℕ) : ℤ) := by
  have hlt := lt_of_not_mem_trBad ha hb
  have hgrow := trPath_bkJ_sub_bkJ_ge (bkJ e + a.1.1, bkL e + a.1.2) a.2 ht
  have hmin : ((min t a.2.length : ℕ) : ℤ) ≤ ((min (pStar ι) a.2.length : ℕ) : ℤ) :=
    Nat.cast_le.2 (min_le_min_right _ ht)
  simp only [trFreshPath] at hlt ⊢
  omega

end CollatzPosDens
