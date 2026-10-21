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
public import CollatzPosDens.Transfer.S02LiftedTransfer
public import CollatzPosDens.Transfer.S02Reduction
public import CollatzPosDens.Transfer.Transfer
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Transfer.PrefixExtension
public import CollatzPosDens.Transfer.PrefixFamilyLe
public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.Transfer.TransferMean
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxProfile
public import CollatzPosDens.Transfer.S02Bstar
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Mixing.Mixing

/-!
# The finite-transfer estimate

Let `ι ∈ {o, b}` be a Fourier index and `d`, `k`, `m` natural numbers with `Q = d + k`,
`n₀ ≤ k` and `n₀ ≤ m ≤ Q`, where `n₀` (`= 2 ^ 80`) is the mixing gate level, and let `𝒱` be a
finite prefix-disjoint set of words, all of length at most `d`. Then
$$\Bigl\langle \Bigl|\sum_{w\in\mathcal V}\mathcal T_{w,Q}\,\rho_k
  - \rho_m\circ\pi_{Q,m}\Bigr|\Bigr\rangle_Q
  \le \mathfrak M_ι(k)+\mathfrak M_ι(m)+1-\mathbf p(\mathcal V),$$
where `𝔐_ι` is the propagation mixing profile (`CollatzPosDens.mxProfile ι`).

The difference splits as `E₁ + E₂ + E₃` with
`E₁ = ∑_w 𝒯_w (ρ_k ∘ π_{Q-|w|,k} - ρ_{Q-|w|})`, `E₂ = ∑_w 𝒯_w ρ_{Q-|w|} - ρ_Q` and
`E₃ = ρ_Q - ρ_m ∘ π_{Q,m}`. The mean absolute value of a transfer and the mixing lemma bound
`⟨|E₁|⟩_Q ≤ 𝐩(𝒱) · 𝔐_ι(k) ≤ 𝔐_ι(k)`; the domination of a prefix-disjoint family by the reference
density gives `E₂ ≤ 0`, so that `⟨|E₂|⟩_Q = 1 - 𝐩(𝒱)` by the means of `ρ_Q` and of a transfer;
and the mixing lemma bounds `⟨|E₃|⟩_Q ≤ 𝔐_ι(m)`.

## Main results

* `CollatzPosDens.residueAvg_abs_sum_liftedTransfer_sub_le_of_mxGateLevel_le`: the estimate,
  for any `Q` with `|w| + k ≤ Q` for every `w ∈ 𝒱`.
* `CollatzPosDens.residueAvg_abs_sum_liftedTransfer_refDensity_sub_le`: the estimate with
  `Q = d + k`.

## Implementation notes

The lifted transfer `𝒯_{w,Q}` carries a proof of `|w| + k ≤ Q`, so the sum over `𝒱` runs over
`𝒱.attach`. The geometric mass `𝐩(𝒱) ∈ [0, ∞]` enters through `ENNReal.toReal`; it is finite,
being a finite sum. The profile `𝔐_ι` is a function on `ℝ`, evaluated at the casts of `k` and
`m`. The general form only asks `|w| + k ≤ Q` for each `w ∈ 𝒱`, which is all the argument
uses; it follows from `Q = d + k` and `|w| ≤ d`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
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

/-- The average of the transfers of the reference densities over a finite set of words is its
geometric mass. -/
private theorem residueAvg_sum_transfer_refDensity {V : Finset Word} {Q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ Q) :
    residueAvg Q (fun y => ∑ w ∈ V, transfer w (refDensity (Q - w.length))
      (y.cast : ResidueGroup (Q - w.length + w.length))) =
      (geomMass (V : Set Word)).toReal := by
  rw [residueAvg_sum, toReal_geomMass_coe_finset]
  refine sum_congr rfl fun w hw => ?_
  have e := residueAvg_comp_residueReduction (Nat.sub_add_cancel (hlen w hw)).le
    (transfer w (refDensity (Q - w.length)))
  simp only [Function.comp_def, residueReduction_apply] at e
  rw [e, residueAvg_transfer, residueAvg_refDensity, zpow_neg, zpow_natCast, inv_pow, mul_one]

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

/-- The propagation mixing profile is nonnegative at every level beyond the gate level. -/
private theorem transferEstimate_mxProfile_nonneg (ι : FIndex) {k : ℕ} (hk : mxGateLevel ≤ k) :
    0 ≤ mxProfile ι k := by
  refine mxProfile_nonneg ι ?_
  have : 1 ≤ k := le_trans (by rw [mxGateLevel_def]; exact Nat.one_le_two_pow) hk
  exact_mod_cast this

/-- **The finite-transfer estimate**, for any level `Q` with `|w| + k ≤ Q` for all `w ∈ 𝒱`:
if `ι` is a Fourier index, `𝒱` a finite prefix-disjoint set of words, `n₀ ≤ k` and
`n₀ ≤ m ≤ Q`, then
`⟨|∑_{w ∈ 𝒱} 𝒯_{w,Q} ρ_k - ρ_m ∘ π_{Q,m}|⟩_Q ≤ 𝔐_ι(k) + 𝔐_ι(m) + 1 - 𝐩(𝒱)`. -/
theorem residueAvg_abs_sum_liftedTransfer_sub_le_of_mxGateLevel_le (ι : FIndex) {V : Finset Word}
    (hV : IsPrefixFree (V : Set Word)) {k Q m : ℕ} (hk : mxGateLevel ≤ k)
    (hVQ : ∀ w ∈ V, w.length + k ≤ Q) (hm : mxGateLevel ≤ m) (hmQ : m ≤ Q) :
    residueAvg Q (fun y => |∑ w ∈ V.attach, liftedTransfer w.1 (hVQ w.1 w.2) (refDensity k) y -
        refDensity m (residueReduction hmQ y)|) ≤
      mxProfile ι k + mxProfile ι m + 1 -
        (geomMass (V : Set Word)).toReal := by
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
          refDensity m (residueReduction hmQ y)| ≤
        ∑ w ∈ V.attach, |a w y| + (refDensity Q y - ∑ w ∈ V, b w y) +
          |refDensity Q y - refDensity m (residueReduction hmQ y)| := by
    simp only [hab, sum_add_distrib, sum_attach V fun w => b w y]
    exact transferEstimate_abs_sum_add_sub_le_of_le _ _
      (sum_transfer_refDensity_le hV hlenQ le_rfl y)
  have hE1 : residueAvg Q (fun y => ∑ w ∈ V.attach, |a w y|) ≤
      (geomMass (V : Set Word)).toReal * (mxProfile ι k) := by
    rw [residueAvg_sum, toReal_geomMass_coe_finset,
      ← sum_attach V fun w => (2 : ℝ)⁻¹ ^ w.valSum, sum_mul]
    refine sum_le_sum fun w _ => ?_
    rw [residueAvg_abs_liftedTransfer, zpow_neg, zpow_natCast, inv_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa only [g, abs_sub_comm] using
      residueAvg_abs_refDensity_sub_le_of_two_pow_le ι hk (Nat.le_sub_of_add_le' (hVQ w.1 w.2))
  have hE2 : residueAvg Q (fun y => refDensity Q y - ∑ w ∈ V, b w y) =
      1 - (geomMass (V : Set Word)).toReal := by
    rw [residueAvg_sub, residueAvg_refDensity, residueAvg_sum_transfer_refDensity hlenQ]
  have hE3 := residueAvg_abs_refDensity_sub_le_of_two_pow_le ι hm hmQ
  have hX := mul_le_mul_of_nonneg_right hp1
    (transferEstimate_mxProfile_nonneg ι hk)
  calc _ ≤ residueAvg Q (fun y => ∑ w ∈ V.attach, |a w y| +
          (refDensity Q y - ∑ w ∈ V, b w y) +
          |refDensity Q y - refDensity m (residueReduction hmQ y)|) :=
        residueAvg_mono hpt
    _ = residueAvg Q (fun y => ∑ w ∈ V.attach, |a w y|) +
          residueAvg Q (fun y => refDensity Q y - ∑ w ∈ V, b w y) +
          residueAvg Q (fun y => |refDensity Q y - refDensity m (residueReduction hmQ y)|) := by
        rw [residueAvg_add, residueAvg_add]
    _ ≤ _ := by
        rw [hE2]
        linarith

/-- **The finite-transfer estimate.** Let `ι` be a Fourier index and `d`, `k`, `m` natural
numbers with `Q = d + k`, `n₀ ≤ k` and `n₀ ≤ m ≤ Q`, where `n₀` is the mixing gate level, and let
`𝒱` be a finite prefix-disjoint set of words, all of length at most `d`. Then
`⟨|∑_{w ∈ 𝒱} 𝒯_{w,Q} ρ_k - ρ_m ∘ π_{Q,m}|⟩_Q ≤ 𝔐_ι(k) + 𝔐_ι(m) + 1 - 𝐩(𝒱)`, where `𝔐_ι` is
the propagation mixing profile. -/
@[collatz_pos_dens "lem_transfer_estimate"]
theorem residueAvg_abs_sum_liftedTransfer_refDensity_sub_le (ι : FIndex) {V : Finset Word}
    (hV : IsPrefixFree (V : Set Word)) {d k m : ℕ} (hk : mxGateLevel ≤ k)
    (hlen : ∀ w ∈ V, w.length ≤ d) (hm : mxGateLevel ≤ m) (hmQ : m ≤ d + k) :
    residueAvg (d + k) (fun y => |∑ w ∈ V.attach,
        liftedTransfer w.1 (Nat.add_le_add_right (hlen w.1 w.2) k) (refDensity k) y -
        refDensity m (residueReduction hmQ y)|) ≤
      mxProfile ι k + mxProfile ι m + 1 -
        (geomMass (V : Set Word)).toReal :=
  residueAvg_abs_sum_liftedTransfer_sub_le_of_mxGateLevel_le ι hV hk
    (fun w hw => Nat.add_le_add_right (hlen w hw) k) hm hmQ

end CollatzPosDens
