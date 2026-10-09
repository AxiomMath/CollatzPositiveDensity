/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Transfer.Reduction
public import CollatzPosDens.Transfer.Transfer
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Transfer.PrefixExtension
public import CollatzPosDens.Transfer.PrefixFamilyLe
public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.Transfer.TransferMean
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Mixing.Mixing

/-!
# The finite-transfer estimate

Let `h ≥ 0`, `k`, `Q = h + k` and `ℓ` be natural numbers with `2 ^ 131072 ≤ k` and
`2 ^ 131072 ≤ ℓ ≤ Q`, and let `𝒱` be a finite prefix-disjoint set of words, all of length at
most `h`. Then
$$\Bigl\langle \Bigl|\sum_{w\in\mathcal V}\mathcal T_{w,Q}\,\rho_k
  - \rho_\ell\circ\pi_{Q,\ell}\Bigr|\Bigr\rangle_Q
  \le \frac23\Bigl(\frac C{k^{9/8}}+\frac C{\ell^{9/8}}+1-\mathbf p(\mathcal V)\Bigr),$$
where `C` is the mixing coefficient.

The difference splits as `E₁ + E₂ + E₃` with
`E₁ = ∑_w 𝒯_w (ρ_k ∘ π_{Q-|w|,k} - ρ_{Q-|w|})`, `E₂ = ∑_w 𝒯_w ρ_{Q-|w|} - ρ_Q` and
`E₃ = ρ_Q - ρ_ℓ ∘ π_{Q,ℓ}`. `CollatzPosDens.residueAvg_abs_liftedTransfer` and
`CollatzPosDens.residueAvg_abs_refDensity_sub_le_of_two_pow_le` bound
`⟨|E₁|⟩_Q ≤ 𝐩(𝒱) · 2C/(3k^{9/8}) ≤ 2C/(3k^{9/8})`; `CollatzPosDens.sum_transfer_refDensity_le`
gives `E₂ ≤ 0`, so that `⟨|E₂|⟩_Q = (2/3)(1 - 𝐩(𝒱))` by `CollatzPosDens.residueAvg_refDensity`
and `CollatzPosDens.residueAvg_transfer`; and
`CollatzPosDens.residueAvg_abs_refDensity_sub_le_of_two_pow_le` bounds
`⟨|E₃|⟩_Q ≤ 2C/(3ℓ^{9/8})`.

## Main results

* `CollatzPosDens.residueAvg_abs_sum_liftedTransfer_sub_le_of_two_pow_le`: the estimate, for
  any `Q` with `|w| + k ≤ Q` for every `w ∈ 𝒱`.
* `CollatzPosDens.residueAvg_abs_sum_liftedTransfer_refDensity_sub_le`: the estimate with
  `Q = h + k`.

## Implementation notes

The lifted transfer `𝒯_{w,Q}` carries a proof of `|w| + k ≤ Q`, so the sum over `𝒱` runs over
`𝒱.attach`. The geometric mass `𝐩(𝒱) ∈ [0, ∞]` enters through `ENNReal.toReal`; it is finite,
being a finite sum. The powers `k^{9/8}`, `ℓ^{9/8}` are real powers. The general form only asks
`|w| + k ≤ Q` for each `w ∈ 𝒱`, of which `Q = h + k` with `|w| ≤ h` is a special case.
-/

@[expose] public section

open scoped ENNReal
open InformationTheory Finset

namespace CollatzPosDens

/-- The triangle inequality for a sum split as `∑ aᵢ + b - r`, with `b ≤ R` absorbed by `R`. -/
private theorem transferEstimate_abs_sum_add_sub_le_of_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {b R r : ℝ} (hb : b ≤ R) :
    |∑ i ∈ s, a i + b - r| ≤ ∑ i ∈ s, |a i| + (R - b) + |R - r| := by
  have h₁ := abs_add_le (∑ i ∈ s, a i + (b - R)) (R - r)
  have h₂ := abs_add_le (∑ i ∈ s, a i) (b - R)
  rw [abs_of_nonpos (sub_nonpos.2 hb), show ∑ i ∈ s, a i + (b - R) + (R - r) =
    ∑ i ∈ s, a i + b - r by ring] at *
  linarith [abs_sum_le_sum_abs a s]

/-- The average of the transfers of the reference densities over a finite set of words is
`2/3` times its geometric mass. -/
private theorem residueAvg_sum_transfer_refDensity {V : Finset Word} {Q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ Q) :
    residueAvg Q (fun y => ∑ w ∈ V, transfer w (refDensity (Q - w.length))
      (y.cast : ResidueGroup (Q - w.length + w.length))) =
      (geomMass (V : Set Word)).toReal * (2 / 3) := by
  rw [residueAvg_sum, toReal_geomMass_coe_finset, sum_mul]
  refine sum_congr rfl fun w hw => ?_
  have e := residueAvg_comp_residueReduction (Nat.sub_add_cancel (hlen w hw)).le
    (transfer w (refDensity (Q - w.length)))
  simp only [Function.comp_def, residueReduction_apply] at e
  rw [e, residueAvg_transfer, residueAvg_refDensity, zpow_neg, zpow_natCast, inv_pow]

/-- The lifted transfer of `ρ_k` splits as the lifted transfer of `ρ_k ∘ π - ρ_{Q-|w|}` plus the
transfer of `ρ_{Q-|w|}`. -/
private theorem transferEstimate_liftedTransfer_refDensity_eq_add (w : Word) {k Q : ℕ}
    (h : w.length + k ≤ Q) (y : ResidueGroup Q) :
    liftedTransfer w h (refDensity k) y =
      liftedTransfer w (Nat.add_sub_of_le (le_of_add_le_left h)).le
        (fun z => refDensity k (residueReduction (Nat.le_sub_of_add_le' h) z) -
          refDensity (Q - w.length) z) y +
      transfer w (refDensity (Q - w.length)) (y.cast : ResidueGroup (Q - w.length + w.length)) := by
  set g : ResidueGroup (Q - w.length) → ℝ := fun z =>
    refDensity k (residueReduction (Nat.le_sub_of_add_le' h) z) - refDensity (Q - w.length) z
  have h₁ : g ∘ residueReduction
      (Nat.le_sub_of_add_le' (Nat.add_sub_of_le (le_of_add_le_left h)).le) = g := by
    funext z
    simp
  have h₂ : refDensity k ∘ residueReduction (Nat.le_sub_of_add_le' h) =
      g + refDensity (Q - w.length) := by
    funext z
    simp [g]
  simp only [liftedTransfer_apply, h₁, h₂, transfer_add, Pi.add_apply]
  rfl

/-- **The finite-transfer estimate**, for any level `Q` with `|w| + k ≤ Q` for all `w ∈ 𝒱`:
if `𝒱` is a finite prefix-disjoint set of words, `2 ^ 131072 ≤ k` and `2 ^ 131072 ≤ ℓ ≤ Q`, then
`⟨|∑_{w ∈ 𝒱} 𝒯_{w,Q} ρ_k - ρ_ℓ ∘ π_{Q,ℓ}|⟩_Q ≤ (2/3)(C/k^{9/8} + C/ℓ^{9/8} + 1 - 𝐩(𝒱))`. -/
theorem residueAvg_abs_sum_liftedTransfer_sub_le_of_two_pow_le {V : Finset Word}
    (hV : IsPrefixFree (V : Set Word)) {k Q ℓ : ℕ} (hk : 2 ^ 131072 ≤ k)
    (hVQ : ∀ w ∈ V, w.length + k ≤ Q) (hℓ : 2 ^ 131072 ≤ ℓ) (hℓQ : ℓ ≤ Q) :
    residueAvg Q (fun y => |∑ w ∈ V.attach, liftedTransfer w.1 (hVQ w.1 w.2) (refDensity k) y -
        refDensity ℓ (residueReduction hℓQ y)|) ≤
      2 / 3 * (mixingConst / (k : ℝ) ^ (9 / 8 : ℝ) + mixingConst / (ℓ : ℝ) ^ (9 / 8 : ℝ) + 1 -
        (geomMass (V : Set Word)).toReal) := by
  have hlenQ : ∀ w ∈ V, w.length ≤ Q := fun w hw => le_of_add_le_left (hVQ w hw)
  have hp1 : (geomMass (V : Set Word)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (geomMass_le_one_of_isPrefixFree hV hlenQ)
  let g : (w : V) → ResidueGroup (Q - w.1.length) → ℝ := fun w z =>
    refDensity k (residueReduction (Nat.le_sub_of_add_le' (hVQ w.1 w.2)) z) -
      refDensity (Q - w.1.length) z
  have hw' (w : V) : w.1.length + (Q - w.1.length) ≤ Q := (Nat.add_sub_of_le (hlenQ w.1 w.2)).le
  let a : V → ResidueGroup Q → ℝ := fun w y => liftedTransfer w.1 (hw' w) (g w) y
  let b : Word → ResidueGroup Q → ℝ := fun w y => transfer w (refDensity (Q - w.length))
    (y.cast : ResidueGroup (Q - w.length + w.length))
  have hab (w : V) (y : ResidueGroup Q) :
      liftedTransfer w.1 (hVQ w.1 w.2) (refDensity k) y = a w y + b w.1 y :=
    transferEstimate_liftedTransfer_refDensity_eq_add w.1 (hVQ w.1 w.2) y
  have hpt (y : ResidueGroup Q) :
      |∑ w ∈ V.attach, liftedTransfer w.1 (hVQ w.1 w.2) (refDensity k) y -
          refDensity ℓ (residueReduction hℓQ y)| ≤
        ∑ w ∈ V.attach, |a w y| + (refDensity Q y - ∑ w ∈ V, b w y) +
          |refDensity Q y - refDensity ℓ (residueReduction hℓQ y)| := by
    simp only [hab, sum_add_distrib, sum_attach V fun w => b w y]
    exact transferEstimate_abs_sum_add_sub_le_of_le _ _
      (sum_transfer_refDensity_le hV hlenQ le_rfl y)
  have hE1 : residueAvg Q (fun y => ∑ w ∈ V.attach, |a w y|) ≤
      (geomMass (V : Set Word)).toReal *
        (2 * mixingConst / (3 * (k : ℝ) ^ (9 / 8 : ℝ))) := by
    rw [residueAvg_sum, toReal_geomMass_coe_finset,
      ← sum_attach V fun w => (2 : ℝ)⁻¹ ^ w.valSum, sum_mul]
    refine sum_le_sum fun w _ => ?_
    rw [residueAvg_abs_liftedTransfer, zpow_neg, zpow_natCast, inv_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa only [g, abs_sub_comm] using
      residueAvg_abs_refDensity_sub_le_of_two_pow_le hk (Nat.le_sub_of_add_le' (hVQ w.1 w.2))
  have hE2 : residueAvg Q (fun y => refDensity Q y - ∑ w ∈ V, b w y) =
      2 / 3 - (geomMass (V : Set Word)).toReal * (2 / 3) := by
    rw [residueAvg_sub, residueAvg_refDensity, residueAvg_sum_transfer_refDensity hlenQ]
  have hE3 := residueAvg_abs_refDensity_sub_le_of_two_pow_le hℓ hℓQ
  have hX := mul_le_mul_of_nonneg_right hp1
    (by have := mixingConst_pos; positivity : (0 : ℝ) ≤ mixingConst / (k : ℝ) ^ (9 / 8 : ℝ))
  have hS := residueAvg_mono hpt
  have e (m : ℝ) : 2 * mixingConst / (3 * m) = 2 / 3 * (mixingConst / m) := by ring
  rw [residueAvg_add, residueAvg_add, hE2] at hS
  rw [e] at hE1 hE3
  nlinarith

/-- **The finite-transfer estimate.** Let `h ≥ 0`, `k`, `Q = h + k` and `ℓ` be natural numbers
with `2 ^ 131072 ≤ k` and `2 ^ 131072 ≤ ℓ ≤ Q`, and let `𝒱` be a finite prefix-disjoint set of
words, all of length at most `h`. Then
`⟨|∑_{w ∈ 𝒱} 𝒯_{w,Q} ρ_k - ρ_ℓ ∘ π_{Q,ℓ}|⟩_Q ≤ (2/3)(C/k^{9/8} + C/ℓ^{9/8} + 1 - 𝐩(𝒱))`. -/
@[collatz_pos_dens "lem_transfer_estimate"]
theorem residueAvg_abs_sum_liftedTransfer_refDensity_sub_le {V : Finset Word}
    (hV : IsPrefixFree (V : Set Word)) {h k ℓ : ℕ} (hk : 2 ^ 131072 ≤ k)
    (hlen : ∀ w ∈ V, w.length ≤ h) (hℓ : 2 ^ 131072 ≤ ℓ) (hℓQ : ℓ ≤ h + k) :
    residueAvg (h + k) (fun y => |∑ w ∈ V.attach,
        liftedTransfer w.1 (Nat.add_le_add_right (hlen w.1 w.2) k) (refDensity k) y -
        refDensity ℓ (residueReduction hℓQ y)|) ≤
      2 / 3 * (mixingConst / (k : ℝ) ^ (9 / 8 : ℝ) + mixingConst / (ℓ : ℝ) ^ (9 / 8 : ℝ) + 1 -
        (geomMass (V : Set Word)).toReal) :=
  residueAvg_abs_sum_liftedTransfer_sub_le_of_two_pow_le hV hk
    (fun w hw => Nat.add_le_add_right (hlen w hw) k) hℓ hℓQ

end CollatzPosDens
