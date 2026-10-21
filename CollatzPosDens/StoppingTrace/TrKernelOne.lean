/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02Dentry
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrGapNonneg
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrZeroGapTree
public import CollatzPosDens.StoppingTrace.TrDirectPositive
public import CollatzPosDens.StoppingTrace.TrBridgePositive
public import CollatzPosDens.StoppingTrace.TrGapThreePassage
public import CollatzPosDens.StoppingTrace.TrPassageBound
public import CollatzPosDens.StoppingTrace.TrDSmall
public import CollatzPosDens.StoppingTrace.TrDTail

/-!
# One kernel step

Fix a level `n` and a unit `ξ : ResidueGroup n`, and call `v` black when `BkBlack n ξ epsStar v`.
For every black point `v ∈ bkPoints`, the first power `m_1(v) = trKernel n ξ 1 v` of the entry
kernel satisfies
```
m_1(v) ≤ 1 - d_entry = 77/100.
```
The gap `s = trGap n ξ epsStar v` is a natural number. If `s = 0`, the zero-gap tree bound
applies; if `s ∈ {1, 6, 9, 13, 16}`, the direct-gap tree bound applies; both give
`m_1(v) < 1 - d_entry`. Otherwise the bridge bound dominates `m_1(v)` by the passage sum
`∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}`, which is at most
* `1 - 37/160` when `s = 3`;
* `1 - D_cr(s) ≤ 1 - 61817834604121/268435456000000` when `2 ≤ s ≤ 511` and
  `s ∉ {3, 6, 9, 13, 16}`;
* `1 - D_cr(s) ≤ 1 - 3927606451461/16777216000000` when `s ≥ 512`;

and each of these is below `77/100`.

## Main results

* `CollatzPosDens.trKernel_one_le`: `m_1(v) ≤ 1 - d_entry` for a black point `v`.

## Implementation notes

The value `m_1(v)` lives in `[0, ∞]`, so the bound is stated with `ENNReal.ofReal` on the right;
since `1 - d_entry > 0` this loses nothing. The standing assumptions that black points lie in `𝒫`
and that the residue `ξ` is a unit are the hypotheses `v ∈ bkPoints` and `IsResidueUnit ξ`.

## References

* [Mazur, *Collatz positive density*], §9.10.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n}

/-- **One kernel step.** Let `ξ ∈ G_n` be a unit and `v ∈ 𝒫` a black point. Then
`m_1(v) ≤ 1 - d_entry`. -/
@[collatz_pos_dens "lem_tr_kernel_one"]
theorem trKernel_one_le (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) :
    trKernel n ξ 1 v ≤ ENNReal.ofReal (1 - (dEntry : ℝ)) := by
  have hg0 := trGap_nonneg n ξ (epsStar : ℝ) v
  by_cases h0 : trGap n ξ (epsStar : ℝ) v = 0
  · exact (trKernel_one_lt_one_sub_dEntry_of_trGap_eq_zero hξ hv hb h0).le
  by_cases hd : trGap n ξ (epsStar : ℝ) v ∈ ({1, 6, 9, 13, 16} : Set ℤ)
  · exact (trKernel_one_lt_one_sub_dEntry_of_trGap_mem hξ hv hb hd).le
  refine (trKernel_one_le_ofReal_tsum_trPassage ξ v).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [dEntry_cast]
  by_cases h3 : trGap n ξ (epsStar : ℝ) v = 3
  · have h := tsum_trPassage_three_mul_exp_neg_trCount_le hξ hv hb h3
    rw [h3]
    exact h.trans (by norm_num)
  refine (tsum_trPassage_mul_exp_neg_trCount_le hξ hv hb).trans ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd
  have hs : ((trGap n ξ (epsStar : ℝ) v).toNat : ℤ) = trGap n ξ (epsStar : ℝ) v :=
    Int.toNat_of_nonneg hg0
  by_cases hsmall : (trGap n ξ (epsStar : ℝ) v).toNat ≤ 511
  · have h := le_trDirectCrossing_of_le_511 (s := (trGap n ξ (epsStar : ℝ) v).toNat)
      (by omega) hsmall (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    linarith
  · have h := trDirectCrossing_ge (s := (trGap n ξ (epsStar : ℝ) v).toNat) (by omega)
    linarith

end CollatzPosDens
