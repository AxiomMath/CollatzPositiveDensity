/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Mixing.MxSubdensity
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Reduction
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Mixing.MxSubdensityCap
public import CollatzPosDens.Mixing.MxSubdensityLe
public import CollatzPosDens.Terminal.CensusError
public import CollatzPosDens.Terminal.CensusUnfold

/-!
# The masked census

Let `M` be a good seed, `n ≥ 0`, let `X` be admissible for generation `n`, write `k = k_n` and
let `m'` be an integer with `16 ≤ m' ≤ k`. Then
$$\Theta_{n,X}(M) \le \frac{64}9\, m'^{5633/2048}\, \Upsilon_{n,X}(M)
  + 44 M \Bigl(\bigl\langle |\rho_k - \rho_{m'} \circ \pi_{k,m'}| \bigr\rangle_k
  + \langle \rho_{m'} - g_{m'} \rangle_{m'}\Bigr).$$

Write `δ = |ρ_k - ρ_{m'} ∘ π_{k,m'}| + (ρ_{m'} - g_{m'}) ∘ π_{k,m'}` on `G_k`; it is nonnegative
since `g_{m'} ≤ ρ_{m'}`. Unfolding `Θ_{n,X}(M)` over the counted pairs `(h, w)` of
`Υ_{n,X}(M)` bounds it by `∑_{(h,w)} ω(h) ω(w) ∑_{j ≥ 0} 4^{-j} ρ_k(z_j(h, w))`. Pointwise
`ρ_k ≤ g_{m'} ∘ π_{k,m'} + δ ≤ (16/3) m'^{5633/2048} + δ` by
`CollatzPosDens.mxSubdensity_le_of_sixteen_le`. Since `∑_j 4^{-j} = 4/3`, the constant part
contributes `(64/9) m'^{5633/2048} Υ_{n,X}(M)`, and the error part, after exchanging the finite
sum with the series, is at most `(4/3) · 33 M ⟨δ⟩_k = 44 M ⟨δ⟩_k` by
`CollatzPosDens.GoodSeed.finsum_unweightedMassPairs_residue_le`. Finally every fibre of
`π_{k,m'}` has `3^{k-m'}` elements, so `⟨(ρ_{m'} - g_{m'}) ∘ π_{k,m'}⟩_k = ⟨ρ_{m'} - g_{m'}⟩_{m'}`.

## Main results

* `CollatzPosDens.GoodSeed.markedMass_le_census`: the masked census bound.
* `CollatzPosDens.markedMass_le_census_tsum_le`: the damped series of `ρ_k` along any
  sequence is bounded by a constant cap plus the damped series of an error term dominating
  `ρ_k` minus the cap.

## Implementation notes

The only property of `m'` used is the cap `g_{m'} ≤ (16/3) m'^{5633/2048}`, which holds for
`m' ≥ 16`, so the bound is stated under `16 ≤ m' ≤ k_n`. The reduction `π_{k,m'}` is
`CollatzPosDens.residueReduction`, and the seed `M` is a natural number cast to `ℚ` in `Θ` and
`Υ`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- `∑_{j ≥ 0} 4^{-j} = 4/3`. -/
private lemma tsum_inv_four_pow : ∑' j : ℕ, ((4 : ℝ) ^ j)⁻¹ = 4 / 3 := by
  simp_rw [← inv_pow]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- If `ρ_k ≤ c + δ` pointwise with `δ ≥ 0`, then the `4^{-j}`-damped series of `ρ_k` along any
sequence `z` is at most `c · (4/3)` plus the damped series of `δ` along `z`. -/
theorem markedMass_le_census_tsum_le {k : ℕ} {c : ℝ} {δ : ResidueGroup k → ℝ} (hδ : 0 ≤ δ)
    (hρ : ∀ y, refDensity k y ≤ c + δ y) (z : ℕ → ResidueGroup k) :
    ∑' j, ((4 : ℝ) ^ j)⁻¹ * refDensity k (z j) ≤
      c * (4 / 3) + ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j) := by
  have hsδ : Summable fun j => ((4 : ℝ) ^ j)⁻¹ * δ (z j) :=
    summable_inv_four_pow_mul_of_le (fun _ => hδ _)
      fun j => Finset.single_le_sum (fun y _ => hδ y) (Finset.mem_univ (z j))
  have hsc : Summable fun j : ℕ => ((4 : ℝ) ^ j)⁻¹ * c := by
    simp_rw [← inv_pow]
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4⁻¹) (by norm_num)).mul_right c
  calc ∑' j, ((4 : ℝ) ^ j)⁻¹ * refDensity k (z j)
      ≤ ∑' j, (((4 : ℝ) ^ j)⁻¹ * c + ((4 : ℝ) ^ j)⁻¹ * δ (z j)) :=
        (summable_inv_four_pow_mul_of_le (fun _ => refDensity_nonneg _ _)
          fun j => Finset.single_le_sum (fun y _ => refDensity_nonneg k y)
            (Finset.mem_univ (z j))).tsum_le_tsum (fun j => by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (hρ _) (by positivity)) (hsc.add hsδ)
    _ = c * (4 / 3) + ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j) := by
        rw [hsc.tsum_add hsδ, tsum_mul_right, tsum_inv_four_pow, mul_comm]

/-- If each `j`-slice `∑_{p ∈ P} ω(p) δ(z_j(p))` is at most `B`, then the `4^{-j}`-damped
total `∑_{p ∈ P} ω(p) ∑_j 4^{-j} δ(z_j(p))` is at most `(4/3) B`. -/
private theorem sum_mul_tsum_inv_four_pow_mul_le {ι G : Type*} [Finite G] {P : Finset ι}
    {ω : ι → ℝ} {δ : G → ℝ} {z : ℕ → ι → G} {B : ℝ} (hω : ∀ p, 0 ≤ ω p) (hδ : 0 ≤ δ)
    (hj : ∀ j, ∑ p ∈ P, ω p * δ (z j p) ≤ B) :
    ∑ p ∈ P, ω p * ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j p) ≤ 4 / 3 * B := by
  have := Fintype.ofFinite G
  have hsδ : ∀ p, Summable fun j => ((4 : ℝ) ^ j)⁻¹ * δ (z j p) := fun p =>
    summable_inv_four_pow_mul_of_le (fun _ => hδ _)
      fun j => Finset.single_le_sum (fun y _ => hδ y) (Finset.mem_univ (z j p))
  have hP : ∀ j, 0 ≤ ∑ p ∈ P, ω p * δ (z j p) := fun j =>
    Finset.sum_nonneg fun p _ => mul_nonneg (hω p) (hδ _)
  have hsB : Summable fun j : ℕ => ((4 : ℝ) ^ j)⁻¹ * B :=
    summable_inv_four_pow_mul_of_le (fun _ => (hP 0).trans (hj 0)) fun _ => le_rfl
  calc ∑ p ∈ P, ω p * ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j p)
      = ∑' j, ((4 : ℝ) ^ j)⁻¹ * ∑ p ∈ P, ω p * δ (z j p) := by
        simp_rw [← tsum_mul_left]
        rw [← Summable.tsum_finsetSum fun p _ => (hsδ p).mul_left _]
        refine tsum_congr fun j => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ ∑' j, ((4 : ℝ) ^ j)⁻¹ * B :=
        Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hj j) (by positivity))
          (Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (hP j))
            (fun j => mul_le_mul_of_nonneg_left (hj j) (by positivity)) hsB) hsB
    _ = 4 / 3 * B := by rw [tsum_mul_right, tsum_inv_four_pow]

/-- **Masked census.** Let `M` be a good seed, let `X` be admissible for generation `n`, write
`k = k_n` and let `16 ≤ m' ≤ k`. Then
`Θ_{n,X}(M) ≤ (64/9) m'^{5633/2048} Υ_{n,X}(M)
  + 44 M (⟨|ρ_k - ρ_{m'} ∘ π_{k,m'}|⟩_k + ⟨ρ_{m'} - g_{m'}⟩_{m'})`. -/
@[collatz_pos_dens "lem_census"]
theorem GoodSeed.markedMass_le_census {M : ℕ} (hM : GoodSeed M) {n : ℕ} {X : ℝ}
    (hX : IsAdmissibleScale M n X) {m' : ℕ} (hm16 : 16 ≤ m') (hm' : m' ≤ level n) :
    markedMass n X M ≤ 64 / 9 * (m' : ℝ) ^ ((5633 : ℝ) / 2048) * unweightedMass n X M +
      44 * M * (residueAvg (level n)
          (fun y => |refDensity (level n) y - refDensity m' (residueReduction hm' y)|) +
        residueAvg m' (fun y => refDensity m' y - mxSubdensity m' y)) := by
  classical
  set k := level n
  set π := residueReduction hm'
  set e : ResidueGroup m' → ℝ := fun y => refDensity m' y - mxSubdensity m' y
  set δ : ResidueGroup k → ℝ := fun y =>
    |refDensity k y - refDensity m' (π y)| + e (π y)
  set c : ℝ := 16 / 3 * (m' : ℝ) ^ ((5633 : ℝ) / 2048)
  set P := (unweightedMassPairs_finite n X M).toFinset
  set ω : (Fin n → Word) × Word → ℝ := fun p =>
    ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ)
  set z : ℕ → (Fin n → Word) × Word → ResidueGroup k := fun j p =>
    ((4 ^ j * src p.2 (historyEndpoint M p.1) + (4 ^ j - 1) / 3 : ℚ).num : ResidueGroup k)
  have he : ∀ y, 0 ≤ e y := fun y => sub_nonneg.2 (mxSubdensity_le_refDensity m' y)
  have hω : ∀ p, 0 ≤ ω p := fun p => mul_nonneg (by exact_mod_cast (Word.weight_pos _).le)
    (by exact_mod_cast (Word.weight_pos _).le)
  have hδ : 0 ≤ δ := fun y => add_nonneg (abs_nonneg _) (he _)
  have hρ : ∀ y, refDensity k y ≤ c + δ y := fun y => by
    simp only [δ, e, c]
    linarith [le_abs_self (refDensity k y - refDensity m' (π y)),
      mxSubdensity_le_of_sixteen_le hm16 (π y)]
  have herr : ∑ p ∈ P, ω p * ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j p) ≤
      4 / 3 * (33 * M * residueAvg k δ) :=
    sum_mul_tsum_inv_four_pow_mul_le hω hδ fun j => by
      have := hM.finsum_unweightedMassPairs_residue_le hX δ hδ j
      rwa [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)] at this
  have hΥ : unweightedMass n X M = ∑ p ∈ P, ω p := by
    rw [unweightedMass_eq_finsum_pairs,
      finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
  have havg : residueAvg k δ =
      residueAvg k (fun y => |refDensity k y - refDensity m' (π y)|) + residueAvg m' e := by
    rw [← residueAvg_comp_residueReduction hm' e, residueAvg_def, residueAvg_def,
      residueAvg_def, ← mul_add, ← Finset.sum_add_distrib]
    rfl
  calc markedMass n X M
      ≤ ∑ p ∈ P, ω p * ∑' j, ((4 : ℝ) ^ j)⁻¹ * refDensity k (z j p) := by
        have := markedMass_le_tsum_unweightedMassPairs n X M
        rwa [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)] at this
    _ ≤ ∑ p ∈ P, ω p * (c * (4 / 3) + ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j p)) :=
        Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (markedMass_le_census_tsum_le hδ hρ (z · p)) (hω p)
    _ = c * (4 / 3) * ∑ p ∈ P, ω p +
          ∑ p ∈ P, ω p * ∑' j, ((4 : ℝ) ^ j)⁻¹ * δ (z j p) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ c * (4 / 3) * ∑ p ∈ P, ω p + 4 / 3 * (33 * M * residueAvg k δ) := by gcongr
    _ = _ := by
        rw [hΥ, havg]
        simp only [c]
        ring

end CollatzPosDens
