/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhQstarFloor
public import CollatzPosDens.Seed.Pullback
public import CollatzPosDens.Seed.S05PrefixResidue
public import CollatzPosDens.Seed.S05TupleLength
public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.ResidueMap
public import CollatzPosDens.Transfer.S02Reduction
public import CollatzPosDens.Transfer.TransferAbsMean

/-!
# The mean of the pulled-back reference density on the selected cylinder

Write `G_q = ResidueGroup q`, `π_{q,m} = residueReduction`, `pr_m = prefixResidue m`,
`φ_w = residueMap w`, `𝒯_{w,Q} = liftedTransfer w`, `ρ_k = refDensity k`, `k_N = level N`,
`A(w) = w.valSum`, `q_* = conductor`, `N_* = generationThreshold`, `𝔗_N = selectedTuples N`,
`ŵ(τ) = concatWord τ` and `Ψ = pullbackDensity`. Let `Y ⊆ G_{q_*}` be the cylinder of the
residues `y` with `ỹ ≡ 6275 (mod 3^8)`. The pulled-back reference density
`Ψ = ∑_{τ ∈ 𝔗_{N_*}} 𝒯_{ŵ(τ), q_*} ρ_{k_{N_*}}` has total mass
$$\sum_{y\in Y}\Psi(y) = 3^{q_*}\sum_{\substack{\tau\in\mathfrak T_{N_*},\ |\hat w(\tau)|\ge8\\
  \mathrm{pr}_8(\hat w(\tau))=[6275]_8}} 2^{-A(\hat w(\tau))}$$
on `Y`.

For a word `w` with `|w| ≥ m` the residue map `φ_w : G_t → G_{t+|w|}` followed by the reduction
modulo `3^m` is the constant `pr_m(w)`: the weight `weight w = 3^{|w|} 2^{-A(w)}` vanishes
modulo `3^m`, and writing `w = w_{≤m} w'`, the offset satisfies
`off w = off w_{≤m} + weight w_{≤m} · off w'` with `weight w_{≤m} ≡ 0 (mod 3^m)`. Hence the
lifted transfer `𝒯_{w,Q} g` is supported in the fibre of `pr_m(w)` under `π_{Q,m}`. Its sum over
the fibre of `r` is therefore `0` when `pr_m(w) ≠ r`, and its total mass `3^Q 2^{-A(w)} ⟨g⟩_k`,
with `⟨g⟩_k = residueAvg k g`, when `pr_m(w) = r`. Every selected tuple of generation
`N_* = 9853 ≥ 1` fits below the conductor and has `|ŵ(τ)| > lb (scale 0) = 6618 ≥ 8`, since its
first block lies in the central family at scale `scale 0 = 16544`, hence in `firstCrossing`;
summing over the tuples gives the formula for the mass of `Ψ` on `Y`.

## Main results

* `CollatzPosDens.residueReduction_residueMap_of_le_length`: `π_{t+|w|,m} ∘ φ_w = pr_m(w)` for
  `|w| ≥ m`.
* `CollatzPosDens.sum_filter_liftedTransfer`: the mass of a lifted transfer on a fibre of the
  reduction modulo `3^m`.
* `CollatzPosDens.sum_filter_pullbackDensityOf`: the mass of `pullbackDensityOf N q` on a fibre
  of the reduction modulo `3^m`, when every selected tuple fits below `q` and has length `≥ m`.
* `CollatzPosDens.eight_le_length_concatWord`: `|ŵ(τ)| ≥ 8` for `τ ∈ 𝔗_N`, `N ≥ 1`.
* `CollatzPosDens.val_modEq_iff_residueReduction_eq`: the cylinder `ỹ ≡ 6275 (mod 3^8)` is the
  fibre of `[6275]_8` under `π_{q,8}`.
* `CollatzPosDens.sum_filter_pullbackDensity`: the mean of `Ψ` on the selected cylinder.

## Implementation notes

The cylinder `{y ∈ G_{q_*} | ỹ ≡ 6275 (mod 3^8)}` is written with the least nonnegative
representative `ỹ = y.val`, and the residue `[6275]_8 ∈ G_8` as the dyadic reduction of the
integer `6275`, as in `two_inv_pow_lt_tsum_selectedTuples`. The general statements take an
arbitrary fibre of `π_{q,m}` in place of the cylinder.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For a word `w` with `|w| ≥ m`, the residue map `φ_w : G_t → G_{t+|w|}` followed by the
reduction modulo `3^m` is constant, equal to the prefix residue `pr_m(w)`. -/
theorem residueReduction_residueMap_of_le_length {m t : ℕ} {w : Word} (hw : m ≤ w.length)
    (h : m ≤ t + w.length) (z : ResidueGroup t) :
    residueReduction h (residueMap w t z) = prefixResidue m w := by
  have hred : ∀ x : dyadicRationals, residueReduction h (dyadicRed (t + w.length) x) =
      dyadicRed m x := fun x =>
    RingHom.congr_fun (eq_dyadicRed ((residueReduction h).comp (dyadicRed _))) x
  have hzero : ∀ {n : ℕ}, m ≤ n → (3 : ResidueGroup m) ^ n = 0 := fun {n} hn => by
    rw [← Nat.add_sub_cancel' hn, pow_add, three_pow_self_residueGroup, zero_mul]
  rw [residueMap_apply, map_add, map_mul, hred, hred, dyadicRed_weight, hzero hw, zero_mul,
    zero_mul, zero_add, prefixResidue_def]
  conv_lhs => rw [← List.take_append_drop m w]
  rw [dyadicRed_off_append, dyadicRed_weight, List.length_take_of_le hw, hzero le_rfl, zero_mul,
    zero_mul, add_zero]

/-- The mass of a lifted transfer on a fibre of the reduction modulo `3^m`: for a word `w`
with `m ≤ |w|` and `|w| + k ≤ Q`, and `r ∈ G_m`,
`∑_{y ∈ G_Q, π_{Q,m}(y) = r} (𝒯_{w,Q} g)(y)` is `3^Q 2^{-A(w)} ⟨g⟩_k` if `pr_m(w) = r`, and `0`
otherwise. -/
theorem sum_filter_liftedTransfer {m k Q : ℕ} [NeZero (3 ^ Q)] {w : Word} (hw : m ≤ w.length)
    (h : w.length + k ≤ Q) (hm : m ≤ Q) (g : ResidueGroup k → ℝ) (r : ResidueGroup m) :
    ∑ y with residueReduction hm y = r, liftedTransfer w h g y =
      if prefixResidue m w = r then
        (3 : ℝ) ^ Q * ((2 : ℝ) ^ (-(w.valSum : ℤ)) * residueAvg k g)
      else 0 := by
  have hQ := Nat.sub_add_cancel (le_of_add_le_left h)
  -- `𝒯_{w,Q} g` vanishes off the fibre of `pr_m(w)`.
  have hvan : ∀ y : ResidueGroup Q, residueReduction hm y ≠ prefixResidue m w →
      liftedTransfer w h g y = 0 := by
    intro y hy
    rw [liftedTransfer_apply, transfer_apply]
    refine mul_eq_zero_of_right _ (sum_eq_zero fun z hz => absurd ?_ hy)
    have hz' := congrArg (residueReduction (hQ ▸ hm)) (mem_filter.1 hz).2
    rw [residueReduction_residueMap_of_le_length hw, residueReduction_residueReduction] at hz'
    exact hz'.symm
  split_ifs with hr
  · subst hr
    rw [← residueAvg_liftedTransfer w h g, residueAvg_def, mul_inv_cancel_left₀ (by positivity),
      sum_filter_of_ne fun y _ hy => by_contra fun hne => hy (hvan y hne)]
  · exact sum_eq_zero fun y hy => hvan y fun he => hr (he ▸ (mem_filter.1 hy).2)

/-- The mass of `pullbackDensityOf N q` on a fibre of the reduction modulo `3^m`: if every
selected tuple `τ ∈ 𝔗_N` has `m ≤ |ŵ(τ)|` and `|ŵ(τ)| + k_N ≤ q`, then for `r ∈ G_m`,
`∑_{y ∈ G_q, π_{q,m}(y) = r} (pullbackDensityOf N q)(y) =
3^q ∑_{τ ∈ 𝔗_N, |ŵ(τ)| ≥ m, pr_m(ŵ(τ)) = r} 2^{-A(ŵ(τ))}`. -/
theorem sum_filter_pullbackDensityOf {N q m : ℕ} [NeZero (3 ^ q)] (hm : m ≤ q)
    (hlen : ∀ τ ∈ selectedTuples N, m ≤ (concatWord τ).length)
    (hq : ∀ τ ∈ selectedTuples N, (concatWord τ).length + level N ≤ q) (r : ResidueGroup m) :
    ∑ y with residueReduction hm y = r, pullbackDensityOf N q y =
      (3 : ℝ) ^ q * ∑ τ ∈ (selectedTuples_finite N).toFinset with
          m ≤ (concatWord τ).length ∧ prefixResidue m (concatWord τ) = r,
        (2 : ℝ) ^ (-((concatWord τ).valSum : ℤ)) := by
  simp_rw [pullbackDensityOf_apply]
  rw [sum_comm, sum_filter, mul_sum]
  refine sum_congr rfl fun τ hτ => ?_
  have hτ' := (selectedTuples_finite N).mem_toFinset.1 hτ
  simp only [dite_eq_left (hq τ hτ')]
  rw [sum_filter_liftedTransfer (hlen τ hτ') (hq τ hτ') hm, residueAvg_refDensity, mul_one]
  simp only [hlen τ hτ', true_and]
  rw [mul_ite, mul_zero]

/-- Every selected tuple `τ ∈ 𝔗_N` of a generation `N ≥ 1` has `|ŵ(τ)| ≥ 8`: its first block
`w_0`, in the central family at scale `scale 0 = 16544`, is a first-crossing word, of length more
than `lb 16544 = 16544 - ⌊3 · 16544 / 5⌋ = 6618`. -/
theorem eight_le_length_concatWord {N : ℕ} (hN : 0 < N) {τ : Fin N → Word}
    (hτ : τ ∈ selectedTuples N) : 8 ≤ (concatWord τ).length := by
  have h0 := lb_lt_length_of_mem_firstCrossing (centralFamily_subset_firstCrossing _ _
    (selectedTuples_mem_centralFamily hτ ⟨0, hN⟩))
  have hlb : lb (scale 0) = 6618 := by rw [scale_zero, lb_eq]
  rw [Fin.val_mk, hlb] at h0
  rw [length_concatWord]
  exact le_trans (by omega)
    (single_le_sum (f := fun j => (τ j).length) (fun _ _ => Nat.zero_le _) (mem_univ ⟨0, hN⟩))

/-- The selected cylinder as a fibre of the reduction modulo `3^8`: for `q ≥ 8` and `y ∈ G_q`,
`ỹ ≡ 6275 (mod 3^8)` if and only if `π_{q,8}(y) = [6275]_8`. -/
theorem val_modEq_iff_residueReduction_eq {q : ℕ} (h : 8 ≤ q) (y : ResidueGroup q) :
    y.val ≡ 6275 [MOD 3 ^ 8] ↔
      residueReduction h y = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩ := by
  rw [dyadicRed_intCast, ← (ZMod.val_injective _).eq_iff, val_residueReduction,
    show ((6275 : ℤ) : ResidueGroup 8).val = 6275 from rfl]
  rfl

/-- The mass of `pullbackDensity` on the selected cylinder:
`∑_{y ∈ G_{q_*}, ỹ ≡ 6275 (mod 3^8)} Ψ(y) =
3^{q_*} ∑_{τ ∈ 𝔗_{N_*}, |ŵ(τ)| ≥ 8, pr_8(ŵ(τ)) = [6275]_8} 2^{-A(ŵ(τ))}`. -/
@[collatz_pos_dens "lem_pullback_mean"]
theorem sum_filter_pullbackDensity :
    ∑ y : ResidueGroup conductor with y.val ≡ 6275 [MOD 3 ^ 8], pullbackDensity y =
      (3 : ℝ) ^ conductor * ∑ τ ∈ (selectedTuples_finite generationThreshold).toFinset with
          8 ≤ (concatWord τ).length ∧
            prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩,
        (2 : ℝ) ^ (-((concatWord τ).valSum : ℤ)) := by
  have h8 : 8 ≤ conductor := le_trans (by norm_num) three_hundred_fifty_two_le_conductor
  have hN : 0 < generationThreshold := by rw [generationThreshold_def]; norm_num
  rw [filter_congr fun y _ => val_modEq_iff_residueReduction_eq h8 y,
    pullbackDensity_eq_pullbackDensityOf]
  exact sum_filter_pullbackDensityOf h8 (fun _ hτ => eight_le_length_concatWord hN hτ)
    (fun _ hτ => length_concatWord_add_level_le_conductor hτ) _

end CollatzPosDens
