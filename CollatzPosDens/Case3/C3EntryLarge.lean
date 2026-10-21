/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3FutureMass
public import CollatzPosDens.StoppingTrace.TrBridgePositive
public import CollatzPosDens.Transfer.S02Gamma

/-!
# The entry kernel at a large gap

Let `ξ` be a unit and `v ∈ 𝒫` black (for `ε_*`) with `gap(v) ≥ 4096`. Then the entry kernel
satisfies `m_1(v) < b_* = 333407/10^6`.

With `s = gap(v)`, `trKernel_one_le_ofReal_tsum_trPassage` gives
`m_1(v) ≤ ∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|))`. As `γ_* = z_* = 133/3125`, grouping the
lists `π` by their endpoint shows that this sum is the paid passage mass `∑_x F̃_v(x)`
(`tsum_c3PaidPassage_eq`), which is less than `b_*` at gaps `≥ 4096`.

## Main results

* `CollatzPosDens.trKernel_one_lt_stageRate`: `m_1(v) < b_*` for black `v` with `gap(v) ≥ 4096`.

## Implementation notes

The kernel takes values in `[0, ∞]`, and `b_* ∈ ℚ` is embedded there through `ENNReal.ofReal`.
That `ξ` is a unit and that `v ∈ 𝒫`, the set on which blackness is defined, are explicit
hypotheses.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.4
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- **The entry kernel at a large gap.** Let `ξ` be a unit and `v ∈ 𝒫` black (for `ε_*`) with
`gap(v) ≥ 4096`. Then `m_1(v) < b_* = 333407/10^6`. -/
@[collatz_pos_dens "lem_c3_entry_large"]
theorem trKernel_one_lt_stageRate {n : ℕ} {ξ : ResidueGroup n} {v : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    (hgap : 4096 ≤ trGap n ξ (epsStar : ℝ) v) :
    trKernel n ξ 1 v < ENNReal.ofReal (stageRate : ℝ) := by
  refine lt_of_le_of_lt (trKernel_one_le_ofReal_tsum_trPassage ξ v) ?_
  have hγz : (gammaStar : ℝ) = (zStar : ℝ) := by rw [gammaStar_cast, zStar_cast]
  have hsum := summable_trPassage_mul_exp_neg_trCount ξ v (trGap n ξ (epsStar : ℝ) v).toNat
  rw [hγz] at hsum
  rw [hγz, ENNReal.ofReal_tsum_of_nonneg
      (fun π ↦ mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le) hsum,
    ← tsum_c3PaidPassage_eq]
  exact tsum_c3PaidPassage_lt_stageRate hξ hv hb hgap

end CollatzPosDens
