/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Terminal.ResidueCount
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Terminal.S06EndpointFloor
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Maps.SyrPeriodic
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.S06PairWeight
public import CollatzPosDens.Terminal.SourceUniqueHistory
public import CollatzPosDens.Terminal.SourceWindow
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# The error part of the census

Let `t ≥ t_min` be an odd integer that is not Syracuse-periodic, let `j ≥ 0`, let `X` be
admissible for generation `j`, write `k = k_j`, let `Φ ≥ 0` be a function on `G_k` and let
`i ≥ 0`. Then
$$\sum_{(h,w)} \omega(h)\omega(w)\,
  \Phi\bigl((4^i \mathrm{src}(w, R_h) + (4^i - 1)/3) \bmod 3^k\bigr)
  \le 33 t \langle\Phi\rangle_k,$$
the sum over the counted pairs `(h, w)` of `Υ_{j,X}(t)`.

The map `σ_i : y ↦ 4^i y + (4^i - 1)/3` is a permutation of `G_k`, as `4` is a unit modulo
`3^k`. If there is a counted pair, its history `h₀` has `R_{h₀} ≥ 16^b` with `b = b_j`, and
`r_b ≤ 2 w_b ≤ 2b`, so admissibility gives `X > L_b(R_{h₀}) ≥ 16^b / (4 · 3^b) ≥ 3^k`.
Every counted pair has `ω(h) ω(w) ≤ t / X`, distinct counted pairs have distinct integer
sources (here non-periodicity of `t` is used), and these lie in `[X, 32 X)`;
`CollatzPosDens.sum_residue_perm_le` then bounds the sum by `(t / X) · 33 X ⟨Φ⟩_k`.

## Main results

* `CollatzPosDens.finsum_unweightedMassPairs_residue_le_of_odd`: the bound above.
* `CollatzPosDens.GoodSeed.finsum_unweightedMassPairs_residue_le`: the same bound for an
  `s`-good seed with `s ≥ 1`, which is odd, at least `t_min` and not Syracuse-periodic.

## Implementation notes

As in `CollatzPosDens.markedMass_le_tsum_unweightedMassPairs`, the residue modulo `3^k` of
the rational `4^i src(w, R_h) + (4^i - 1)/3` is that of its numerator; for a counted pair the
source is an integer, so this is the residue of the integer `4^i src(w, R_h) + (4^i - 1)/3`.
The weight `ω(h)` of a history is the weight of its concatenated word `ŵ(h)`. The integer `t`
is taken in `ℕ`, as it is positive and Syracuse-periodicity is a property of natural numbers.
Only `b_j ≥ 3` is used of the growth of the scales, which `b_j ≥ b_0 = 16544` provides.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.3.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The natural number `(4^j - 1)/3`. -/
private def censusErrorOffset (j : ℕ) : ℕ := (4 ^ j - 1) / 3

/-- `3 · (4^j - 1)/3 = 4^j - 1` in `ℚ`. -/
private lemma three_mul_censusErrorOffset (j : ℕ) :
    (3 : ℚ) * censusErrorOffset j = 4 ^ j - 1 := by
  have hd : 3 ∣ 4 ^ j - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := j)
  have h1 : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have := congrArg (Nat.cast : ℕ → ℚ)
    (Nat.mul_div_cancel' hd : 3 * censusErrorOffset j = 4 ^ j - 1)
  push_cast [Nat.cast_sub h1] at this
  exact this

/-- The permutation `σ_j : y ↦ 4^j y + (4^j - 1)/3` of `G_k`. -/
private noncomputable def censusErrorPerm (k j : ℕ) : Equiv.Perm (ResidueGroup k) :=
  (Units.mulLeft (ZMod.unitOfCoprime 4 (Nat.Coprime.pow_right k (by decide)) ^ j)).trans
    (Equiv.addRight (censusErrorOffset j : ResidueGroup k))

/-- For an integer `x`, the residue of the numerator of `4^j x + (4^j - 1)/3` is `σ_j(x)`. -/
private lemma num_cast_eq_censusErrorPerm (k j : ℕ) (x : ℤ) :
    (((4 ^ j * (x : ℚ) + (4 ^ j - 1) / 3 : ℚ).num : ℤ) : ResidueGroup k) =
      censusErrorPerm k j (x : ResidueGroup k) := by
  have hq : (4 ^ j * (x : ℚ) + (4 ^ j - 1) / 3 : ℚ) =
      ((4 ^ j * x + censusErrorOffset j : ℤ) : ℚ) := by
    have := three_mul_censusErrorOffset j
    push_cast
    linarith
  rw [hq, Rat.num_intCast]
  simp [censusErrorPerm, ZMod.coe_unitOfCoprime]

/-- If `t ≥ t_min` is an odd integer, `X` is admissible for generation `n` and `𝓗_n(t)` is
nonempty, then `3^{k_n} ≤ X`. -/
private lemma censusError_three_pow_level_le {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {n : ℕ} {X : ℝ} (hX : IsAdmissibleScale t n X)
    {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    (3 : ℝ) ^ level n ≤ X := by
  set b := scale n
  have hR : ((16 : ℝ) ^ b) ≤ (historyEndpoint (t : ℚ) h : ℝ) := by
    obtain ⟨m, hm, -, hle⟩ := historyEndpoint_large hodd ht hh
    rw [hm, Rat.cast_intCast]
    exact_mod_cast hle
  have hL := (lowerScale_mono b hR).trans_lt (hX.lowerScale_lt hh)
  refine le_trans ?_ hL.le
  have hrb : rb b ≤ ((2 * b : ℕ) : ℤ) := by
    have := rb_add_ceilLog3_add_eb b
    have := wb_le_self b
    push_cast
    omega
  have h2 : (2 : ℝ) ^ rb b ≤ 4 ^ b := by
    calc (2 : ℝ) ^ rb b ≤ 2 ^ (((2 * b : ℕ)) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hrb
      _ = 4 ^ b := by rw [zpow_natCast, pow_mul]; norm_num
  have h3 : (3 : ℝ) ^ level n ≤ 3 ^ b :=
    pow_le_pow_right₀ (by norm_num) (le_trans (Nat.le_mul_of_pos_left _ (by norm_num))
      (four_mul_level_le n))
  have hb3 : 3 ≤ b := le_trans (by norm_num) (sixteen544_le_scale n)
  obtain ⟨c, hc⟩ : ∃ c, b = c + 3 := ⟨b - 3, by omega⟩
  have hkey : (4 : ℝ) * 3 ^ b * 3 ^ b ≤ 16 ^ b := by
    rw [hc]
    have : (9 : ℝ) ^ c ≤ 16 ^ c := pow_le_pow_left₀ (by norm_num) (by norm_num) c
    calc (4 : ℝ) * 3 ^ (c + 3) * 3 ^ (c + 3) = 2916 * 9 ^ c := by
          rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring
      _ ≤ 4096 * 16 ^ c := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) c]
      _ = 16 ^ (c + 3) := by ring
  rw [lowerScale_def, le_div_iff₀ (lowerScale_denom_pos b)]
  calc (3 : ℝ) ^ level n * (4 * 2 ^ rb b * 3 ^ b) ≤ 3 ^ b * (4 * 4 ^ b * 3 ^ b) := by
        gcongr
    _ = 4 ^ b * (4 * 3 ^ b * 3 ^ b) := by ring
    _ ≤ 4 ^ b * 16 ^ b := by gcongr

/-- **Error part of the census.** Let `t ≥ t_min` be an odd integer that is not
Syracuse-periodic, let `j ≥ 0`, let `X` be admissible for generation `j`, write `k = k_j`,
let `Φ ≥ 0` be a function on `G_k` and let `i ≥ 0`. Then
`∑_{(h,w)} ω(h) ω(w) Φ((4^i src(w, R_h) + (4^i - 1)/3) mod 3^k) ≤ 33 t ⟨Φ⟩_k`, the sum over the
counted pairs of `Υ_{j,X}(t)`. -/
@[collatz_pos_dens "lem_s06_census_error"]
theorem finsum_unweightedMassPairs_residue_le_of_odd {t : ℕ} (hodd : Odd t)
    (ht : targetFloor ≤ t) (hper : ¬ SyrPeriodic t) {j : ℕ} {X : ℝ} (hX : IsAdmissibleScale t j X)
    (Φ : ResidueGroup (level j) → ℝ) (hΦ : 0 ≤ Φ) (i : ℕ) :
    ∑ᶠ p ∈ unweightedMassPairs j X t,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        Φ ((4 ^ i * src p.2 (historyEndpoint t p.1) + (4 ^ i - 1) / 3 : ℚ).num :
          ResidueGroup (level j)) ≤ 33 * t * residueAvg (level j) Φ := by
  have hoddZ : Odd (t : ℤ) := by exact_mod_cast hodd
  have htZ : (targetFloor : ℤ) ≤ t := by exact_mod_cast ht
  have hXZ : IsAdmissibleScale ((t : ℤ) : ℚ) j X := by rwa [Int.cast_natCast]
  set σ := censusErrorPerm (level j) i
  set P := (unweightedMassPairs_finite j X t).toFinset
  have havg : 0 ≤ residueAvg (level j) Φ := by
    rw [residueAvg_def]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hΦ y)
  have hXpos := hX.pos
  rw [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
  rcases P.eq_empty_or_nonempty with hP | ⟨p₀, hp₀⟩
  · rw [show (unweightedMassPairs_finite j X t).toFinset = ∅ from hP, Finset.sum_empty]
    positivity
  have hp₀' : p₀ ∈ unweightedMassPairs j X t := by simpa [P] using hp₀
  have h3X : (3 : ℝ) ^ (level j) ≤ X :=
    censusError_three_pow_level_le hoddZ htZ hXZ (by rw [Int.cast_natCast]; exact hp₀'.1)
  let z : (Fin j → Word) × Word → ℤ := fun p => (src p.2 (historyEndpoint t p.1)).num
  have hz : ∀ p ∈ unweightedMassPairs j X t, src p.2 (historyEndpoint t p.1) = z p := by
    intro p hp
    obtain ⟨y, hy⟩ := exists_intCast_src_of_mem_unweightedMassPairs hp
    simp only [z, hy, Rat.num_intCast]
  have hinj : Set.InjOn z P := by
    rintro ⟨h, w⟩ hp ⟨h', w'⟩ hq he
    have hp' : (h, w) ∈ unweightedMassPairs j X t := by simpa [P] using hp
    have hq' : (h', w') ∈ unweightedMassPairs j X t := by simpa [P] using hq
    exact eq_of_src_eq_of_mem_unweightedMassPairs hodd.pos hodd hper hp' hq'
      (by rw [hz _ hp', hz _ hq', he])
  have hsub : P.image z ⊆ Ico ⌈X⌉ ⌈32 * X⌉ := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    have hp' : p ∈ unweightedMassPairs j X t := by simpa [P] using hp
    have hpZ : p ∈ unweightedMassPairs j X ((t : ℤ) : ℚ) := by rwa [Int.cast_natCast]
    have hw := sources_subset_Ico_of_odd hoddZ htZ hXZ
      ⟨z p, src_mem_sources hpZ (by rw [Int.cast_natCast]; exact hz p hp'), rfl⟩
    exact Finset.mem_Ico.2 ⟨Int.ceil_le.2 hw.1, Int.lt_ceil.2 hw.2⟩
  calc ∑ p ∈ P, ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        Φ ((4 ^ i * src p.2 (historyEndpoint t p.1) + (4 ^ i - 1) / 3 : ℚ).num :
          ResidueGroup (level j))
      ≤ ∑ p ∈ P, (t : ℝ) / X * Φ (σ (z p : ResidueGroup (level j))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' : p ∈ unweightedMassPairs j X t := by simpa [P] using hp
        have hpZ : p ∈ unweightedMassPairs j X ((t : ℤ) : ℚ) := by rwa [Int.cast_natCast]
        rw [hz p hp', num_cast_eq_censusErrorPerm]
        have hw := weight_mul_weight_le_div_of_odd hoddZ htZ hXZ hpZ
        rw [Int.cast_natCast] at hw
        exact mul_le_mul_of_nonneg_right hw (hΦ _)
    _ = (t : ℝ) / X * ∑ x ∈ P.image z, Φ (σ (x : ResidueGroup (level j))) := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ (t : ℝ) / X * ∑ x ∈ Ico ⌈X⌉ ⌈32 * X⌉, Φ (σ (x : ResidueGroup (level j))) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hΦ _) (by positivity)
    _ ≤ (t : ℝ) / X * (33 * X * residueAvg (level j) Φ) := by
        gcongr
        exact sum_residue_perm_le (level j) h3X Φ hΦ σ
    _ = 33 * t * residueAvg (level j) Φ := by field_simp

/-- The error part of the census for an `s`-good seed `M` with `s ≥ 1`: if `X` is admissible for
generation `n`, `δ ≥ 0` is a function on `G_{k_n}` and `j ≥ 0`, then
`∑_{(h,w)} ω(h) ω(w) δ((4^j src(w, R_h) + (4^j - 1)/3) mod 3^{k_n}) ≤ 33 M ⟨δ⟩_{k_n}`. -/
theorem GoodSeed.finsum_unweightedMassPairs_residue_le {s M : ℕ} (hM : GoodSeed s M)
    (hs : 0 < s) {n : ℕ} {X : ℝ} (hX : IsAdmissibleScale M n X)
    (δ : ResidueGroup (level n) → ℝ) (hδ : 0 ≤ δ) (j : ℕ) :
    ∑ᶠ p ∈ unweightedMassPairs n X M,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        δ ((4 ^ j * src p.2 (historyEndpoint M p.1) + (4 ^ j - 1) / 3 : ℚ).num :
          ResidueGroup (level n)) ≤ 33 * M * residueAvg (level n) δ :=
  finsum_unweightedMassPairs_residue_le_of_odd hM.odd (by
    have h := (hM.two_pow_66176_lt hs).le
    rwa [show (66176 : ℕ) = 4 * 16544 by norm_num, pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num,
      ← targetFloor_eq] at h) hM.not_syrPeriodic hX δ hδ j

end CollatzPosDens
