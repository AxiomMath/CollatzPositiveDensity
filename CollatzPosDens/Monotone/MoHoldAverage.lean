/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.CharSum.ChBoundaryStep
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import CollatzPosDens.Monotone.MoHoldAverageSummable
public import CollatzPosDens.Monotone.MoInvpowSummable

/-!
# One hold from the boundary row

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and write `J = ⌊n/2⌋`. Let `A ≥ 0` be
real, `m` a natural number, and `p ∈ 𝒫` with `j(p) + m = J`. Then
`∑_{h ∈ 𝒫} η(h) Q(p + h) ≤ (∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A}) Q_{m-1}`.

Each point `h ∈ 𝒫` has `j(h) ≥ 1` and `j(p + h) + m = J + j(h)`, so `chQ_le_boundary_step`
bounds `Q(p + h)` by `max(m - j(h), 1)^{-A} Q_{m-1}`. Grouping the nonnegative series
`∑_h η(h) max(m - j(h), 1)^{-A}` by the value `r = j(h)` and using `∑_l η(r, l) = ν₄₅(r)` turns
it into `∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A}`; comparing termwise concludes.

## Main results

* `CollatzPosDens.tsum_holdLaw_mul_chQ_add_le_hasSum_weight`: for a weight `w` of the first
  coordinate with `0 ≤ w ≤ 1` on `ℤ_{≥1}`, `∑_{h ∈ 𝒫} η(h) w(j(h)) = ∑_{r ≥ 1} ν₄₅(r) w(r)`.
* `CollatzPosDens.tsum_holdLaw_mul_chQ_add_le`: the averaging inequality.

## Implementation notes

The sum over `r ≥ 1` is written as a sum over `r + 1` with `r ∈ ℕ`, and a point `h = (j, l) ∈ 𝒫`
contributes `η(j, l)` evaluated at the natural number `j`. The statement holds for every `m ∈ ℕ`,
with no hypothesis `m ≥ 1` (for `m = 0`, `m - 1` is truncated subtraction). The threshold `ε` is
arbitrary.
-/

@[expose] public section

namespace CollatzPosDens

/-- Grouping by the first coordinate: for a weight `w` of the first coordinate with
`0 ≤ w ≤ 1` on `ℤ_{≥1}`, `∑_{h ∈ 𝒫} η(h) w(j(h)) = ∑_{r ≥ 1} ν₄₅(r) w(r)`. -/
theorem tsum_holdLaw_mul_chQ_add_le_hasSum_weight {w : ℤ → ℝ} (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j)
    (hw1 : ∀ j, 1 ≤ j → w j ≤ 1) :
    HasSum (fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * w (bkJ h))
      (∑' r : ℕ, nu45 ((r : ℤ) + 1) * w ((r : ℤ) + 1)) := by
  rw [← bkPointsEquiv.hasSum_iff]
  set f : ℕ × ℤ → ℝ := fun x ↦ holdLaw (x.1 + 1) x.2 * w ((x.1 : ℤ) + 1) with hf
  have hcomp : (fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * w (bkJ h)) ∘ bkPointsEquiv = f := by
    funext x
    simp only [Function.comp_apply, bkPointsEquiv, Equiv.coe_fn_mk, bkJ, hf]
    congr 2
  rw [hcomp]
  have hw0' : ∀ r : ℕ, 0 ≤ w ((r : ℤ) + 1) := fun r ↦ hw0 _ (by omega)
  have h0 : 0 ≤ f := fun _ ↦ mul_nonneg (holdLaw_nonneg _ _) (hw0' _)
  have hfib : ∀ r : ℕ, HasSum (fun l : ℤ ↦ f (r, l)) (nu45 ((r : ℤ) + 1) * w ((r : ℤ) + 1)) :=
    fun r ↦ by
      have := (hasSum_holdLaw (j := r + 1) (by omega)).mul_right (w ((r : ℤ) + 1))
      simpa [hf] using this
  have hsr : Summable fun r : ℕ ↦ nu45 ((r : ℤ) + 1) * w ((r : ℤ) + 1) :=
    hasSum_nu45_natCast_add_one.summable.of_nonneg_of_le
      (fun r ↦ mul_nonneg (nu45_nonneg _) (hw0' r))
      (fun r ↦ mul_le_of_le_one_right (nu45_nonneg _) (hw1 _ (by omega)))
  have hs : Summable f := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun r ↦ (hfib r).summable, ?_⟩
    simp_rw [(hfib _).tsum_eq]
    exact hsr
  exact (hs.hasSum.prod_fiberwise hfib).unique hsr.hasSum ▸ hs.hasSum

/-- **One hold from the boundary row.** Let `A ≥ 0` be real and `p ∈ 𝒫` with
`j(p) + m = ⌊n/2⌋`. Then
`∑_{h ∈ 𝒫} η(h) Q(p + h) ≤ (∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A}) Q_{m-1}`. -/
@[collatz_pos_dens "lem_mo_hold_average"]
theorem tsum_holdLaw_mul_chQ_add_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (m : ℕ) {p : ℤ × ℤ} (hp : p ∈ bkPoints) (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ)) :
    ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) ≤
      (∑' r : ℕ, nu45 ((r : ℤ) + 1) * ((max ((m : ℤ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) *
        chQm n ξ ε A (m - 1) := by
  set w : ℤ → ℝ := fun j ↦ ((max ((m : ℤ) - j) 1 : ℤ) : ℝ) ^ (-A) with hw
  have hw0 : ∀ j, 1 ≤ j → 0 ≤ w j := fun j _ ↦
    Real.rpow_nonneg (by exact_mod_cast zero_le_one.trans (le_max_right _ _)) _
  have hw1 : ∀ j, 1 ≤ j → w j ≤ 1 := fun j _ ↦
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast le_max_right _ _) (by linarith)
  have hsum := tsum_holdLaw_mul_chQ_add_le_hasSum_weight hw0 hw1
  rw [← hsum.tsum_eq, ← tsum_mul_right]
  refine (summable_holdLaw_mul_chQ_add n ξ ε p).tsum_le_tsum (fun h ↦ ?_)
    (hsum.summable.mul_right _)
  obtain ⟨h, hh⟩ := h
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (holdLaw_nonneg _ _)
  have hh' : 1 ≤ bkJ h := hh
  have hstep := chQ_le_boundary_step n ξ ε hA (m := m) (r := (bkJ h).toNat) (by omega)
    (add_mem_bkPoints hp hh) (by simp only [bkJ, Prod.fst_add] at hpm hh' ⊢; omega)
  have hr : (((bkJ h).toNat : ℕ) : ℤ) = bkJ h := by omega
  rw [hr] at hstep
  exact hstep

end CollatzPosDens
