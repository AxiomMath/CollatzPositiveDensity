/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxPushforward
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.FxRefLawBounded

/-!
# The oscillation form of the reference-density discrepancy

For integers `0 ≤ m ≤ q`, the average discrepancy between the reference density `ρ_q` and the
pulled-back coarser density `ρ_m ∘ π_{q,m}` is two thirds of the oscillation of the reference
law at scale `m`:
`⟨|ρ_q - ρ_m ∘ π_{q,m}|⟩_q = (2/3) Osc_{m,q}(μ_q)`.
The key input is that, by `CollatzPosDens.sum_refLaw_residueReduction_eq`, the fibre average of
`μ_q` is `Avg_{m,q} μ_q (y) = 3^{m-q} μ_m(π_{q,m} y)`.

## Main results

* `CollatzPosDens.fiberAvg_refLaw`: `Avg_{m,q} μ_q (y) = 3^{m-q} μ_m(π_{q,m} y)`.
* `CollatzPosDens.residueAvg_abs_refDensity_sub`:
  `⟨|ρ_q - ρ_m ∘ π_{q,m}|⟩_q = (2/3) Osc_{m,q}(μ_q)`.

## Implementation notes

The reference law takes values in `[0, ∞]`; it enters the oscillation through
`ENNReal.toReal`, as in `CollatzPosDens.refDensity`. Since every weight is at most one, this loses
nothing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The fibre average of the reference law: `Avg_{m,q} μ_q (y) = 3^{m-q} μ_m(π_{q,m} y)`. -/
theorem fiberAvg_refLaw {m q : ℕ} (h : m ≤ q) (y : ResidueGroup q) :
    fiberAvg h (fun y => (refLaw q y).toReal) y =
      (3 : ℝ) ^ ((m : ℤ) - q) * (refLaw m (residueReduction h y)).toReal := by
  rw [fiberAvg, ← ENNReal.toReal_sum fun y _ =>
    refLaw_ne_top q y,
    sum_refLaw_residueReduction_eq]

/-- **Oscillation form.** For `m ≤ q`,
`⟨|ρ_q - ρ_m ∘ π_{q,m}|⟩_q = (2/3) Osc_{m,q}(μ_q)`. -/
@[collatz_pos_dens "lem_mx_osc_form"]
theorem residueAvg_abs_refDensity_sub {m q : ℕ} (h : m ≤ q) :
    residueAvg q (fun y => |refDensity q y - refDensity m (residueReduction h y)|) =
      2 / 3 * oscillation h (fun y => (refLaw q y).toReal) := by
  have h3 : (3 : ℝ) ^ m = 3 ^ q * (3 : ℝ) ^ ((m : ℤ) - q) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    ring
  have hpos : (0 : ℝ) < 3 ^ q := by positivity
  rw [residueAvg_def, oscillation, mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [fiberAvg_refLaw, refDensity, refDensity, h3]
  rw [show 2 / 3 * 3 ^ q * (refLaw q y).toReal -
      2 / 3 * (3 ^ q * 3 ^ ((m : ℤ) - q)) * (refLaw m (residueReduction h y)).toReal =
      (2 / 3 * 3 ^ q) * ((refLaw q y).toReal -
        3 ^ ((m : ℤ) - q) * (refLaw m (residueReduction h y)).toReal) by ring,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / 3 * 3 ^ q)]
  field_simp

end CollatzPosDens
