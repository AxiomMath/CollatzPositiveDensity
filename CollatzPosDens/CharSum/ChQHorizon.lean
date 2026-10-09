/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQfinite
public import CollatzPosDens.CharSum.ChQfiniteStable

/-!
# The white product at any sufficiently long horizon

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `J = ⌊n/2⌋`. If `p ∈ 𝒫` and
`J ≤ j(p) + K`, then `Q(p) = Q^{(K)}(p)`. Indeed, if `K ≥ J`, stability of the finite-horizon
products (`chQFinite_add_of_le`) at horizon `J`, valid since `J ≤ j(p) + J`, gives
`Q^{(K)}(p) = Q^{(J)}(p) = Q(p)`; if `K < J`, stability at horizon `K` gives
`Q(p) = Q^{(J)}(p) = Q^{(K)}(p)`.

## Main results

* `CollatzPosDens.chQ_eq_chQFinite_of_nonneg`: if `0 ≤ j(p)` and `⌊n/2⌋ ≤ j(p) + K` then
  `Q(p) = Q^{(K)}(p)`.
* `CollatzPosDens.chQ_eq_chQFinite`: if `p ∈ 𝒫` and `⌊n/2⌋ ≤ j(p) + K` then
  `Q(p) = Q^{(K)}(p)`.

## Implementation notes

The hypothesis `p ∈ 𝒫` is used only through `j(p) ≥ 0`, which makes the horizon `J` itself
admissible for `chQFinite_add_of_le`; `chQ_eq_chQFinite_of_nonneg` records the statement under
this weaker hypothesis.

## References

* [Mazur, *Collatz positive density*], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `0 ≤ j(p)` and `⌊n/2⌋ ≤ j(p) + K`, then `Q(p) = Q^{(K)}(p)`. -/
theorem chQ_eq_chQFinite_of_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {K : ℕ} {p : ℤ × ℤ}
    (hp : 0 ≤ bkJ p) (hK : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + K) :
    chQ n ξ ε p = chQFinite n ξ ε K p := by
  rw [chQ_def]
  rcases le_or_gt (n / 2) K with h | h
  · obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le h
    have hJ : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + (n / 2 : ℕ) := by omega
    exact (chQFinite_add_of_le n ξ ε hJ D).symm
  · obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le h.le
    rw [hD]
    exact chQFinite_add_of_le n ξ ε hK D

/-- **The white product at a long horizon.** If `p ∈ 𝒫` and `⌊n/2⌋ ≤ j(p) + K`, then
`Q(p) = Q^{(K)}(p)`. -/
@[collatz_pos_dens "lem_ch_Q_horizon"]
theorem chQ_eq_chQFinite (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {K : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) (hK : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + K) :
    chQ n ξ ε p = chQFinite n ξ ε K p :=
  chQ_eq_chQFinite_of_nonneg n ξ ε (by have := mem_bkPoints.mp hp; omega) hK

end CollatzPosDens
