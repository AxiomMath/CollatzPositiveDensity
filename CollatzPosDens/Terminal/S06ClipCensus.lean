/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Terminal.S06CensusUnfold
public import CollatzPosDens.Terminal.S06CensusError
public import CollatzPosDens.Terminal.S06ClipDominate
public import CollatzPosDens.Terminal.S06ClipCapBound
public import CollatzPosDens.Terminal.S06ClipRemainderNonneg
public import CollatzPosDens.Terminal.S06ClipRemainderMean

/-!
# The finite-profile census

Let `t ≥ t_min` be an odd integer that is not Syracuse-periodic, let `j ≥ 0`, let `X` be
admissible for generation `j`, let `n ≥ n₀` be an integer, where `n₀ = 2^80` is the mixing gate
level, and let `B > 0` be real. Then
$$\Theta_{j,X}(t) \le \frac23 B\,\Upsilon_{j,X}(t) + 44\,t\Bigl(2n^{-8}
  + \frac{2^{13}\sqrt{n\log n}}{B} + 2^{365} n^{-a_{\mathrm{mx}}(\mathrm o)}\log n\Bigr).$$

Write `k = k_j`, `m = min(k, n)`, `π = π_{k,m}`, `g = g^clp_{m,n,B}` and `Φ = Φ^clp_{k,n,B}`.
By `markedMass_le_tsum_unweightedMassPairs`, `Θ_{j,X}(t)` is bounded by the sum over the
counted pairs `(h, w)` of `Υ_{j,X}(t)` of `ω(h) ω(w) ∑_{i ≥ 0} 4^{-i} ρ_k(z_i(h, w))`.
Pointwise `ρ_k ≤ g ∘ π + Φ ≤ B/2 + Φ` by `refDensity_le_clipDensity_add_clipRemainder` and
`clipDensity_le_half`, and `Φ ≥ 0` by `clipRemainder_nonneg`. Since `∑_i 4^{-i} = 4/3`, the
bounded part contributes `(2/3) B Υ_{j,X}(t)`; the remainder part, after exchanging the finite
sum with the series, is at most `(4/3) · 33 t ⟨Φ⟩_k = 44 t ⟨Φ⟩_k` by
`finsum_unweightedMassPairs_residue_le_of_odd`, and `⟨Φ⟩_k` is bounded by
`residueAvg_clipRemainder_le`.

## Main results

* `CollatzPosDens.markedMass_le_clipCensus`: the census bound above.

## Implementation notes

The integer `t` is a natural number (it is at least `t_min > 0`), cast to `ℚ` in `Θ` and `Υ`;
the power `n^{-8}` is `((n : ℝ) ^ 8)⁻¹`, the power `n^{-a}` is the real power
`(n : ℝ) ^ (-(a : ℝ))`, and `log` is `Real.log`.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- `∑_{i ≥ 0} 4^{-i} = 4/3`. -/
private lemma clipCensus_tsum_inv_four_pow : ∑' i : ℕ, ((4 : ℝ) ^ i)⁻¹ = 4 / 3 := by
  simp_rw [← inv_pow]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- If `ρ_k ≤ c + δ` pointwise with `δ ≥ 0`, then the `4^{-i}`-damped series of `ρ_k` along any
sequence `z` is at most `c · (4/3)` plus the damped series of `δ` along `z`. -/
private lemma clipCensus_tsum_le {k : ℕ} {c : ℝ} {δ : ResidueGroup k → ℝ} (hδ : 0 ≤ δ)
    (hρ : ∀ y, refDensity k y ≤ c + δ y) (z : ℕ → ResidueGroup k) :
    ∑' i, ((4 : ℝ) ^ i)⁻¹ * refDensity k (z i) ≤
      c * (4 / 3) + ∑' i, ((4 : ℝ) ^ i)⁻¹ * δ (z i) := by
  have hsδ : Summable fun i => ((4 : ℝ) ^ i)⁻¹ * δ (z i) :=
    summable_inv_four_pow_mul_of_le (fun _ => hδ _)
      fun i => Finset.single_le_sum (fun y _ => hδ y) (Finset.mem_univ (z i))
  have hsc : Summable fun i : ℕ => ((4 : ℝ) ^ i)⁻¹ * c := by
    simp_rw [← inv_pow]
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4⁻¹) (by norm_num)).mul_right c
  calc ∑' i, ((4 : ℝ) ^ i)⁻¹ * refDensity k (z i)
      ≤ ∑' i, (((4 : ℝ) ^ i)⁻¹ * c + ((4 : ℝ) ^ i)⁻¹ * δ (z i)) :=
        (summable_inv_four_pow_mul_of_le (fun _ => refDensity_nonneg _ _)
          fun i => Finset.single_le_sum (fun y _ => refDensity_nonneg k y)
            (Finset.mem_univ (z i))).tsum_le_tsum (fun i => by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (hρ _) (by positivity)) (hsc.add hsδ)
    _ = c * (4 / 3) + ∑' i, ((4 : ℝ) ^ i)⁻¹ * δ (z i) := by
        rw [hsc.tsum_add hsδ, tsum_mul_right, clipCensus_tsum_inv_four_pow, mul_comm]

/-- If each `i`-slice `∑_{p ∈ P} ω(p) δ(z_i(p))` is at most `C`, then the `4^{-i}`-damped
total `∑_{p ∈ P} ω(p) ∑_i 4^{-i} δ(z_i(p))` is at most `(4/3) C`. -/
private lemma clipCensus_sum_mul_tsum_le {ι G : Type*} [Finite G] {P : Finset ι}
    {ω : ι → ℝ} {δ : G → ℝ} {z : ℕ → ι → G} {C : ℝ} (hω : ∀ p, 0 ≤ ω p) (hδ : 0 ≤ δ)
    (hi : ∀ i, ∑ p ∈ P, ω p * δ (z i p) ≤ C) :
    ∑ p ∈ P, ω p * ∑' i, ((4 : ℝ) ^ i)⁻¹ * δ (z i p) ≤ 4 / 3 * C := by
  have := Fintype.ofFinite G
  have hsδ : ∀ p, Summable fun i => ((4 : ℝ) ^ i)⁻¹ * δ (z i p) := fun p =>
    summable_inv_four_pow_mul_of_le (fun _ => hδ _)
      fun i => Finset.single_le_sum (fun y _ => hδ y) (Finset.mem_univ (z i p))
  have hP : ∀ i, 0 ≤ ∑ p ∈ P, ω p * δ (z i p) := fun i =>
    Finset.sum_nonneg fun p _ => mul_nonneg (hω p) (hδ _)
  have hsC : Summable fun i : ℕ => ((4 : ℝ) ^ i)⁻¹ * C :=
    summable_inv_four_pow_mul_of_le (fun _ => (hP 0).trans (hi 0)) fun _ => le_rfl
  calc ∑ p ∈ P, ω p * ∑' i, ((4 : ℝ) ^ i)⁻¹ * δ (z i p)
      = ∑' i, ((4 : ℝ) ^ i)⁻¹ * ∑ p ∈ P, ω p * δ (z i p) := by
        simp_rw [← tsum_mul_left]
        rw [← Summable.tsum_finsetSum fun p _ => (hsδ p).mul_left _]
        refine tsum_congr fun i => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ ∑' i, ((4 : ℝ) ^ i)⁻¹ * C :=
        Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (hi i) (by positivity))
          (Summable.of_nonneg_of_le (fun i => mul_nonneg (by positivity) (hP i))
            (fun i => mul_le_mul_of_nonneg_left (hi i) (by positivity)) hsC) hsC
    _ = 4 / 3 * C := by rw [tsum_mul_right, clipCensus_tsum_inv_four_pow]

/-- **Finite-profile census.** Let `t ≥ t_min` be an odd integer that is not Syracuse-periodic,
let `j ≥ 0`, let `X` be admissible for generation `j`, let `n ≥ n₀` be an integer and let
`B > 0` be real. Then `Θ_{j,X}(t) ≤ (2/3) B Υ_{j,X}(t) +
44 t (2 n^{-8} + 2^13 √(n log n) / B + 2^365 n^{-a_mx(o)} log n)`. -/
@[collatz_pos_dens "lem_s06_clip_census"]
theorem markedMass_le_clipCensus {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t)
    (hper : ¬ SyrPeriodic t) {j : ℕ} {X : ℝ} (hX : IsAdmissibleScale t j X) {n : ℕ}
    (hn : mxGateLevel ≤ n) {B : ℝ} (hB : 0 < B) :
    markedMass j X t ≤ 2 / 3 * B * unweightedMass j X t +
      44 * t * (2 * ((n : ℝ) ^ 8)⁻¹ + 2 ^ 13 * √(n * Real.log n) / B +
        2 ^ 365 * (n : ℝ) ^ (-(amix .o : ℝ)) * Real.log n) := by
  classical
  set k := level j
  have hΦavg := residueAvg_clipRemainder_le (level_pos j) hn hB
  generalize 2 * ((n : ℝ) ^ 8)⁻¹ + 2 ^ 13 * √(n * Real.log n) / B +
    2 ^ 365 * (n : ℝ) ^ (-(amix .o : ℝ)) * Real.log n = E at hΦavg ⊢
  set Φ : ResidueGroup k → ℝ := clipRemainder k n B
  set P := (unweightedMassPairs_finite j X t).toFinset
  set ω : (Fin j → Word) × Word → ℝ := fun p =>
    ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ)
  set z : ℕ → (Fin j → Word) × Word → ResidueGroup k := fun i p =>
    ((4 ^ i * src p.2 (historyEndpoint t p.1) + (4 ^ i - 1) / 3 : ℚ).num : ResidueGroup k)
  have hΦ : 0 ≤ Φ := fun y => clipRemainder_nonneg k n B y
  have hω : ∀ p, 0 ≤ ω p := fun p => mul_nonneg (by exact_mod_cast (Word.weight_pos _).le)
    (by exact_mod_cast (Word.weight_pos _).le)
  have hρ : ∀ y, refDensity k y ≤ B / 2 + Φ y := fun y => by
    have h1 := refDensity_le_clipDensity_add_clipRemainder k n B y
    have h2 := clipDensity_le_half (min k n) n hB (residueReduction (min_le_left k n) y)
    simp only [Φ]
    linarith
  have herr : ∑ p ∈ P, ω p * ∑' i, ((4 : ℝ) ^ i)⁻¹ * Φ (z i p) ≤
      4 / 3 * (33 * t * residueAvg k Φ) :=
    clipCensus_sum_mul_tsum_le hω hΦ fun i => by
      have := finsum_unweightedMassPairs_residue_le_of_odd hodd ht hper hX Φ hΦ i
      rwa [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)] at this
  have hΥ : unweightedMass j X t = ∑ p ∈ P, ω p := by
    rw [unweightedMass_eq_finsum_pairs,
      finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  calc markedMass j X t
      ≤ ∑ p ∈ P, ω p * ∑' i, ((4 : ℝ) ^ i)⁻¹ * refDensity k (z i p) := by
        have := markedMass_le_tsum_unweightedMassPairs j X t
        rwa [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)] at this
    _ ≤ ∑ p ∈ P, ω p * (B / 2 * (4 / 3) + ∑' i, ((4 : ℝ) ^ i)⁻¹ * Φ (z i p)) :=
        Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (clipCensus_tsum_le hΦ hρ (z · p)) (hω p)
    _ = B / 2 * (4 / 3) * ∑ p ∈ P, ω p +
          ∑ p ∈ P, ω p * ∑' i, ((4 : ℝ) ^ i)⁻¹ * Φ (z i p) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ B / 2 * (4 / 3) * ∑ p ∈ P, ω p + 4 / 3 * (33 * t * E) := by
        gcongr
        exact herr.trans (by gcongr)
    _ = 2 / 3 * B * unweightedMass j X t + 44 * t * E := by
        rw [hΥ]
        ring

end CollatzPosDens
