/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChQmDominate

/-!
# A boundary step for the weighted suprema of `Q`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and write `J = ⌊n/2⌋`. If `p ∈ 𝒫`
satisfies `j(p) + m = J + r` with `r ≥ 1`, then `j(p) ≥ J ∸ (m - 1)`, so `p` contributes to the
weighted supremum `Q_{m-1}`; since its distance to the cut-off is `d_J(p) = max(m - r, 1)`, this
gives `Q(p) ≤ max(m - r, 1)^{-A} Q_{m-1}`.

## Main results

* `CollatzPosDens.chQ_le_boundary_step_chDist_eq`: if `j(p) + m = J + r` then
  `d_J(p) = max(m - r, 1)`.
* `CollatzPosDens.chQ_le_boundary_step`: `Q(p) ≤ max(m - r, 1)^{-A} Q_{m-1}`.

## Implementation notes

The power is the real power `Real.rpow`, matching `CollatzPosDens.chQm`, and the base
`max(m - r, 1)` is computed in `ℤ`. No hypothesis `m ≥ 1` is imposed: for `m = 0`, `m - 1` is
truncated subtraction and the bound still holds. The threshold `ε` is arbitrary.

## References

* [Mazur, *Collatz positive density*], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `j(p) + m = ⌊n/2⌋ + r` as integers, the distance to the cut-off is `max(m - r, 1)`. -/
theorem chQ_le_boundary_step_chDist_eq {n m r : ℕ} {p : ℤ × ℤ}
    (h : bkJ p + m = ((n / 2 : ℕ) : ℤ) + r) :
    (chDist n p : ℤ) = max ((m : ℤ) - r) 1 := by
  rw [chDist_eq]
  omega

/-- **Boundary step.** For real `A ≥ 0`, an integer `r ≥ 1` and `p ∈ 𝒫` with
`j(p) + m = ⌊n/2⌋ + r`, we have `Q(p) ≤ max(m - r, 1)^{-A} Q_{m-1}`. -/
@[collatz_pos_dens "lem_ch_boundary_step"]
theorem chQ_le_boundary_step (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A)
    {m r : ℕ} (hr : 1 ≤ r) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (h : bkJ p + m = ((n / 2 : ℕ) : ℤ) + r) :
    chQ n ξ ε p ≤ ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) ^ (-A) * chQm n ξ ε A (m - 1) := by
  have hj : ((n / 2 - (m - 1) : ℕ) : ℤ) ≤ bkJ p := by
    rw [mem_bkPoints] at hp
    omega
  have hdom := chQm_dominate n ξ ε hA (m - 1) hp hj
  have hd : ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) = (chDist n p : ℝ) := by
    rw [← chQ_le_boundary_step_chDist_eq h]; push_cast; rfl
  have hpos : (0 : ℝ) < (chDist n p : ℝ) := by exact_mod_cast chDist_pos n p
  rw [hd, Real.rpow_neg hpos.le, ← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hpos A),
    mul_comm]
  exact hdom

end CollatzPosDens
