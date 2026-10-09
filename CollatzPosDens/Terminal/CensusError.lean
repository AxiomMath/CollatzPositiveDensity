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
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.PairWeight
public import CollatzPosDens.Terminal.SourceUniqueHistory
public import CollatzPosDens.Terminal.SourceWindow
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# The error part of the census

Let `M` be a good seed, `n ≥ 0`, let `X` be admissible for generation `n`, write `k = k_n`, let
`δ ≥ 0` be a function on `G_k` and let `j ≥ 0`. Then
$$\sum_{(h,w)} \omega(h)\omega(w)\,
  \delta\bigl((4^j \mathrm{src}(w, R_h) + (4^j - 1)/3) \bmod 3^k\bigr)
  \le 33 M \langle\delta\rangle_k,$$
the sum over the counted pairs `(h, w)` of `Υ_{n,X}(M)`.

The map `σ_j : y ↦ 4^j y + (4^j - 1)/3` is a permutation of `G_k`, as `4` is a unit modulo
`3^k`. If there is a counted pair, its history `h₀` has `R_{h₀} ≥ 16^b` with `b = b_n`, and
`r_b ≤ 2 w_b ≤ 2b`, so admissibility gives `X > L_b(R_{h₀}) ≥ 16^b / (4 · 3^b) ≥ 3^b ≥ 3^k`.
Every counted pair has `ω(h) ω(w) ≤ M / X`, distinct counted pairs have distinct integer
sources, and these lie in `[X, 32 X)`; the residue count then bounds the sum by
`(M / X) · 33 X ⟨δ⟩_k`.

## Main results

* `CollatzPosDens.GoodSeed.finsum_unweightedMassPairs_residue_le`: the bound above.

## Implementation notes

As in `CollatzPosDens.markedMass_le_tsum_unweightedMassPairs`, the residue modulo `3^k` of
the rational `4^j src(w, R_h) + (4^j - 1)/3` is that of its numerator; for a counted pair the
source is an integer, so this is the residue of the integer `4^j src(w, R_h) + (4^j - 1)/3`.
The weight `ω(h)` of a history is the weight of its concatenated word `ŵ(h)`. Only `b_n ≥ 3`
is used of the growth of the scales, which `b_n ≥ 9` provides.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
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

/-- For `b ≥ 3`, `4 · 3^b · 3^b ≤ 16^b`. -/
lemma four_mul_three_pow_mul_three_pow_le_sixteen_pow {b : ℕ} (hb : 3 ≤ b) :
    (4 : ℝ) * 3 ^ b * 3 ^ b ≤ 16 ^ b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, by omega⟩
  have : (9 : ℝ) ^ c ≤ 16 ^ c := pow_le_pow_left₀ (by norm_num) (by norm_num) c
  calc (4 : ℝ) * 3 ^ (c + 3) * 3 ^ (c + 3) = 2916 * 9 ^ c := by
        rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]
        ring
    _ ≤ 4096 * 16 ^ c := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) c]
    _ = 16 ^ (c + 3) := by ring

/-- If `M` is a good seed, `X` is admissible for generation `n` and `𝓗_n(M)` is nonempty, then
`3^{k_n} ≤ X`. -/
private lemma censusError_three_pow_level_le {M : ℕ} (hM : GoodSeed M) {n : ℕ} {X : ℝ}
    (hX : IsAdmissibleScale M n X) {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    (3 : ℝ) ^ level n ≤ X := by
  set b := scale n
  have hh' : h ∈ centralHistories (((M : ℤ) : ℚ)) n := by rwa [Int.cast_natCast]
  have hR := historyEndpointAt_large_sixteen_pow_le_endpoint (M := (M : ℤ))
    (by exact_mod_cast hM.odd) (by exact_mod_cast hM.lower.le) hh'
  rw [Int.cast_natCast] at hR
  have hL := (lowerScale_mono b hR).trans_lt (hX.lowerScale_lt hh)
  refine le_trans ?_ hL.le
  -- `3^k ≤ L_b(16^b)`, from `r_b ≤ 2 w_b ≤ 2 b`
  have hrb : rb b ≤ ((2 * b : ℕ) : ℤ) := by
    have := rb_add_ceilLog3_add_eb b
    have := wb_le_self b
    push_cast
    omega
  have h2 : (2 : ℝ) ^ rb b ≤ 4 ^ b := by
    calc (2 : ℝ) ^ rb b ≤ 2 ^ (((2 * b : ℕ)) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hrb
      _ = 4 ^ b := by
        rw [zpow_natCast, pow_mul]
        norm_num
  have h3 : (3 : ℝ) ^ level n ≤ 3 ^ b :=
    pow_le_pow_right₀ (by norm_num) (le_trans (Nat.le_mul_of_pos_left _ (by norm_num))
      (four_mul_level_le n))
  have hkey := four_mul_three_pow_mul_three_pow_le_sixteen_pow
    (le_trans (by norm_num) (nine_le_scale n) : 3 ≤ b)
  rw [lowerScale_def, le_div_iff₀ (lowerScale_denom_pos b)]
  calc (3 : ℝ) ^ level n * (4 * 2 ^ rb b * 3 ^ b) ≤ 3 ^ b * (4 * 4 ^ b * 3 ^ b) := by
        gcongr
    _ = 4 ^ b * (4 * 3 ^ b * 3 ^ b) := by ring
    _ ≤ 4 ^ b * 16 ^ b := by gcongr

/-- **Error part of the census.** Let `M` be a good seed, let `X` be admissible for generation
`n`, write `k = k_n`, let `δ ≥ 0` be a function on `G_k` and let `j ≥ 0`. Then
`∑_{(h,w)} ω(h) ω(w) δ((4^j src(w, R_h) + (4^j - 1)/3) mod 3^k) ≤ 33 M ⟨δ⟩_k`, the sum over the
counted pairs of `Υ_{n,X}(M)`. -/
@[collatz_pos_dens "lem_s06_census_error"]
theorem GoodSeed.finsum_unweightedMassPairs_residue_le {M : ℕ} (hM : GoodSeed M) {n : ℕ}
    {X : ℝ} (hX : IsAdmissibleScale M n X) (δ : ResidueGroup (level n) → ℝ) (hδ : 0 ≤ δ)
    (j : ℕ) :
    ∑ᶠ p ∈ unweightedMassPairs n X M,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        δ ((4 ^ j * src p.2 (historyEndpoint M p.1) + (4 ^ j - 1) / 3 : ℚ).num :
          ResidueGroup (level n)) ≤ 33 * M * residueAvg (level n) δ := by
  set σ := censusErrorPerm (level n) j
  set P := (unweightedMassPairs_finite n X M).toFinset
  have hmem {p} : p ∈ P ↔ p ∈ unweightedMassPairs n X M := Set.Finite.mem_toFinset _
  have havg : 0 ≤ residueAvg (level n) δ := by
    rw [residueAvg_def]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hδ y)
  have hXpos := hX.pos
  rw [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
  rcases P.eq_empty_or_nonempty with hP | ⟨p₀, hp₀⟩
  · rw [show (unweightedMassPairs_finite n X M).toFinset = ∅ from hP, Finset.sum_empty]
    positivity
  have h3X : (3 : ℝ) ^ (level n) ≤ X := censusError_three_pow_level_le hM hX (hmem.1 hp₀).1
  -- the integer sources
  let z : (Fin n → Word) × Word → ℤ := fun p => (src p.2 (historyEndpoint M p.1)).num
  have hz : ∀ p ∈ unweightedMassPairs n X M, src p.2 (historyEndpoint M p.1) = z p := by
    intro p hp
    obtain ⟨y, hy⟩ := exists_intCast_src_of_mem_unweightedMassPairs hp
    simp only [z, hy, Rat.num_intCast]
  have hinj : Set.InjOn z P := by
    rintro ⟨h, w⟩ hp ⟨h', w'⟩ hq he
    exact eq_of_src_eq_of_mem_unweightedMassPairs hM (hmem.1 hp) (hmem.1 hq)
      (by rw [hz _ (hmem.1 hp), hz _ (hmem.1 hq), he])
  have hsub : P.image z ⊆ Ico ⌈X⌉ ⌈32 * X⌉ := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    have hp' := hmem.1 hp
    have hw := hM.sources_subset_Ico hX ⟨z p, src_mem_sources hp' (hz p hp'), rfl⟩
    exact Finset.mem_Ico.2 ⟨Int.ceil_le.2 hw.1, Int.lt_ceil.2 hw.2⟩
  calc ∑ p ∈ P, ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        δ ((4 ^ j * src p.2 (historyEndpoint M p.1) + (4 ^ j - 1) / 3 : ℚ).num :
          ResidueGroup (level n))
      ≤ ∑ p ∈ P, (M : ℝ) / X * δ (σ (z p : ResidueGroup (level n))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := hmem.1 hp
        rw [hz p hp', num_cast_eq_censusErrorPerm]
        exact mul_le_mul_of_nonneg_right (hM.weight_mul_weight_le_div hX hp') (hδ _)
    _ = (M : ℝ) / X * ∑ x ∈ P.image z, δ (σ (x : ResidueGroup (level n))) := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ (M : ℝ) / X * ∑ x ∈ Ico ⌈X⌉ ⌈32 * X⌉, δ (σ (x : ResidueGroup (level n))) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hδ _) (by positivity)
    _ ≤ (M : ℝ) / X * (33 * X * residueAvg (level n) δ) := by
        gcongr
        exact sum_residue_perm_le (level n) h3X δ hδ σ
    _ = 33 * M * residueAvg (level n) δ := by field_simp

end CollatzPosDens
