/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The total mass of the holding-time law

The holding-time law `η` is a probability distribution on `𝒫 = ℤ_{≥1} × ℤ`:
`∑_{p ∈ 𝒫} η(p) = 1`. Since `η ≥ 0`, the sum may be computed fibrewise in `j`. The
`j`-marginal is `∑_l η(j, l) = ν₄₅(j)`, and
`∑_{j ≥ 1} ν₄₅(j) = (5/16) ∑_{k ≥ 0} (11/16)^k = 1`. In particular the series converges
(unconditionally, as a `HasSum`).

## Main results

* `CollatzPosDens.hasSum_holdLaw_bkPoints`: `p ↦ η(p)` on `𝒫` has sum `1`.
* `CollatzPosDens.tsum_holdLaw_bkPoints`: `∑_{p ∈ 𝒫} η(p) = 1`.
* `CollatzPosDens.hasSum_holdLaw_bkPoints_succ`: the same statement in the parametrization
  `(m, l) ↦ (m + 1, l)` of `𝒫` by `ℕ × ℤ`.

## Implementation notes

The law `holdLaw j l` takes `j : ℕ`, whereas `𝒫 = bkPoints` is a subset of `ℤ × ℤ`; a point
`p ∈ 𝒫` is evaluated as `holdLaw p.1.toNat p.2`, which is faithful since `p.1 ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- `∑_{k ≥ 0} ν₄₅(k + 1) = 1`. -/
theorem hasSum_holdLaw_bkPoints_nu45 :
    HasSum (fun k : ℕ ↦ nu45 ((k : ℤ) + 1)) 1 := by
  simp_rw [nu45_natCast_add_one]
  have h := (hasSum_geometric_of_lt_one (r := (11 / 16 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (5 / 16)
  convert h using 1
  norm_num

/-- **Total mass of `η`**, parametrized by `ℕ × ℤ`: `∑_{(m, l)} η(m + 1, l) = 1`. -/
theorem hasSum_holdLaw_bkPoints_succ :
    HasSum (fun x : ℕ × ℤ ↦ holdLaw (x.1 + 1) x.2) 1 := by
  set f : ℕ × ℤ → ℝ := fun x ↦ holdLaw (x.1 + 1) x.2
  have h0 : 0 ≤ f := fun _ ↦ holdLaw_nonneg _ _
  have hfib : ∀ n : ℕ, HasSum (fun l : ℤ ↦ f (n, l)) (nu45 ((n : ℤ) + 1)) := fun n ↦ by
    have := hasSum_holdLaw (j := n + 1) (by omega)
    simpa [f] using this
  have hs : Summable f := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun n ↦ (hfib n).summable, ?_⟩
    simp_rw [(hfib _).tsum_eq]
    exact hasSum_holdLaw_bkPoints_nu45.summable
  exact (hs.hasSum.prod_fiberwise hfib).unique hasSum_holdLaw_bkPoints_nu45 ▸ hs.hasSum

/-- **Total mass of the holding-time law.** `p ↦ η(p)` on `𝒫` has sum `1`. -/
@[collatz_pos_dens "lem_rn_hold_mass"]
theorem hasSum_holdLaw_bkPoints :
    HasSum (fun p : bkPoints ↦ holdLaw p.1.1.toNat p.1.2) 1 := by
  rw [← bkPointsEquiv.hasSum_iff]
  convert hasSum_holdLaw_bkPoints_succ using 2 with x
  simp only [Function.comp_apply, bkPointsEquiv, Equiv.coe_fn_mk]
  congr 1

/-- **Total mass of the holding-time law.** `∑_{p ∈ 𝒫} η(p) = 1`. -/
@[collatz_pos_dens "lem_rn_hold_mass"]
theorem tsum_holdLaw_bkPoints : ∑' p : bkPoints, holdLaw p.1.1.toNat p.1.2 = 1 :=
  hasSum_holdLaw_bkPoints.tsum_eq

end CollatzPosDens
