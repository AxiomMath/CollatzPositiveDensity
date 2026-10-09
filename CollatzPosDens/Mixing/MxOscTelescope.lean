/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxFiberAvg
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxOscForm
public import CollatzPosDens.Mixing.MxPushforward
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Transfer.TransferAbsMean

/-!
# Oscillation of the reference law across an intermediate level

For integers `0 ≤ m ≤ r ≤ n`, the oscillation of the reference law `μ_n` at scale `m` splits
across the intermediate level `r`:
`Osc_{m,n}(μ_n) ≤ Osc_{r,n}(μ_n) + Osc_{m,r}(μ_r)`.

The fibre averages of the reference law are `Avg_{m,q} μ_q = 3^{m-q} μ_m ∘ π_{q,m}`
(`CollatzPosDens.fiberAvg_refLaw`). Hence for `y ∈ G_n` with `x = π_{n,r}(y)`,
`μ_n(y) - Avg_{m,n} μ_n(y) =
  (μ_n(y) - Avg_{r,n} μ_n(y)) + 3^{r-n} (μ_r(x) - Avg_{m,r} μ_r(x))`.
Taking absolute values and summing over `y ∈ G_n`, every `x ∈ G_r` is hit by exactly
`3^{n-r}` points `y`, which cancels the factor `3^{r-n}`.

## Main results

* `CollatzPosDens.oscillation_refLaw_le_add`:
  `Osc_{m,n}(μ_n) ≤ Osc_{r,n}(μ_n) + Osc_{m,r}(μ_r)`.

## Implementation notes

The reference law enters the oscillation through `ENNReal.toReal`; every weight is finite
(indeed at most one), so this loses nothing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **Oscillation across an intermediate level.** For `m ≤ r ≤ n`,
`Osc_{m,n}(μ_n) ≤ Osc_{r,n}(μ_n) + Osc_{m,r}(μ_r)`. -/
@[collatz_pos_dens "lem_mx_osc_telescope"]
theorem oscillation_refLaw_le_add {m r n : ℕ} (hmr : m ≤ r) (hrn : r ≤ n) :
    oscillation (hmr.trans hrn) (fun y => (refLaw n y).toReal) ≤
      oscillation hrn (fun y => (refLaw n y).toReal) +
        oscillation hmr (fun x => (refLaw r x).toReal) := by
  set f : ResidueGroup r → ℝ := fun x =>
    (refLaw r x).toReal - fiberAvg hmr (fun y => (refLaw r y).toReal) x with hf
  set c : ℝ := (3 : ℝ) ^ ((r : ℤ) - n) with hc
  have hc0 : 0 < c := zpow_pos (by norm_num) _
  have hzpow : (3 : ℝ) ^ ((m : ℤ) - n) = c * (3 : ℝ) ^ ((m : ℤ) - r) := by
    rw [hc, ← zpow_add₀ (by norm_num)]
    congr 1
    ring
  have hpt : ∀ y : ResidueGroup n,
      (refLaw n y).toReal - fiberAvg (hmr.trans hrn) (fun y => (refLaw n y).toReal) y =
        ((refLaw n y).toReal - fiberAvg hrn (fun y => (refLaw n y).toReal) y) +
          c * f (residueReduction hrn y) := by
    intro y
    rw [hf]
    simp only [fiberAvg_refLaw, residueReduction_residueReduction, hzpow]
    ring
  rw [oscillation, oscillation, oscillation]
  calc ∑ y, |(refLaw n y).toReal - fiberAvg (hmr.trans hrn)
          (fun y => (refLaw n y).toReal) y|
      ≤ ∑ y : ResidueGroup n, (|(refLaw n y).toReal -
          fiberAvg hrn (fun y => (refLaw n y).toReal) y| +
          c * |f (residueReduction hrn y)|) := by
        refine sum_le_sum fun y _ => ?_
        rw [hpt, ← abs_of_pos hc0, ← abs_mul, abs_of_pos hc0]
        exact abs_add_le _ _
    _ = _ := by
        rw [sum_add_distrib, ← mul_sum, sum_comp_residueReduction hrn (fun x => |f x|),
          ← mul_assoc, hc, three_zpow_sub_eq_inv hrn, inv_mul_cancel₀ (by positivity),
          one_mul]

end CollatzPosDens
