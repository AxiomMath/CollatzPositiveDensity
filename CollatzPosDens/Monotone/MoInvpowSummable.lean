/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Summability of `ν₄₅`-weighted inverse powers

For a real `A` and an integer `m`, the series `∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A}` converges.
For `r ≥ m` the factor `max(m - r, 1)` equals `1`, so all but finitely many terms equal `ν₄₅(r)`,
and `∑_{r ≥ 1} ν₄₅(r) = 1` converges.

## Main results

* `CollatzPosDens.summable_nu45_mul_max_rpow_neg`: the series above is summable.

## Implementation notes

The summation index `r ≥ 1` is written as `r + 1` with `r : ℕ`, as for `M₄₅`. The power
`max(m - r, 1)^{-A}` is the real power `Real.rpow` of the integer `max(m - r, 1)` cast to `ℝ`.
No sign condition on `A` is needed: for `A ≥ 0` every term lies between `0` and `ν₄₅(r)`, but for
every real `A` only finitely many terms differ from `ν₄₅(r)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For a real `A` and `m ∈ ℤ`, the series `∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A}` converges. -/
@[collatz_pos_dens "lem_mo_invpow_summable"]
theorem summable_nu45_mul_max_rpow_neg (A : ℝ) (m : ℤ) :
    Summable (fun r : ℕ ↦
      nu45 ((r : ℤ) + 1) * (((max (m - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A))) := by
  refine hasSum_nu45_natCast_add_one.summable.of_norm_bounded_eventually ?_
  have h : ∀ᶠ r : ℕ in Filter.cofinite, max (m - ((r : ℤ) + 1)) 1 = 1 := by
    rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    exact ⟨m.toNat, fun r hr ↦ by omega⟩
  filter_upwards [h] with r hr
  rw [hr, Int.cast_one, Real.one_rpow, mul_one, Real.norm_of_nonneg (nu45_nonneg _)]

end CollatzPosDens
