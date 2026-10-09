/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.Jstar
public import CollatzPosDens.Recipe.X0
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.GoodSeedExists
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.ULower
public import CollatzPosDens.Terminal.Charge
public import CollatzPosDens.Terminal.Coverage
public import CollatzPosDens.Terminal.SourceWindow
public import CollatzPosDens.OrdinaryTime.Time
public import CollatzPosDens.OrdinaryTime.CkAccelTime

/-!
# Joint logarithmic-time count of Collatz convergence

For every real `X ≥ X₀`, at least `c_M X` integers `1 ≤ n < X` reach `1` within
`⌊(523/50) log n⌋₊` Collatz steps and, starting from their odd part, within
`⌊(34881/10000) log n⌋₊` accelerated Collatz steps. Here `c_M = 1 / (2^33 𝓜 m^{5633/2048})` is
`densityConst` and `X₀ = 32 (2^{B_ht} 𝓜 + 1)` is `cutoff`, where `𝓜` is `seedBound`, `m` is
`modulusExponent` and `B_ht` is `heightExponent`.

The proof fixes a good seed `M`, puts `Z = X / 32`, chooses a generation `n ≥ J_*` for which `Z`
is admissible, and counts the source set `𝒮_{n,Z}(M)`: the unweighted terminal mass bound and the
source charge give `#𝒮_{n,Z}(M) ≥ c_M X`, the source window places `𝒮_{n,Z}(M)` in `[X/32, X)`,
and the two time lemmas give both clocks on every source.

## Main results

* `CollatzPosDens.densityConst_mul_le_ncard_reach`: the joint count `c_M X ≤ #{…}`.

## Implementation notes

The counted set is a subset of `ℕ` and its size is `Set.ncard`; the set is finite, being
contained in `{n | n < X}`, so this is its genuine number of elements. The source set lives in
`ℤ` and is transported to `ℕ` along `Int.toNat`, which is injective on positive integers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- For every real `X ≥ cutoff`, at least `densityConst * X` natural numbers `1 ≤ n < X` satisfy
both `CollatzOneWithin n ⌊(523/50) log n⌋₊` and `CollatzAccelOneWithin n ⌊(34881/10000) log n⌋₊`.
-/
@[collatz_pos_dens "prop_mn_internal"]
theorem densityConst_mul_le_ncard_reach {X : ℝ} (hX : (cutoff : ℝ) ≤ X) :
    densityConst * X ≤
      ({n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (CollatzOneWithin n ⌊(523 / 50 : ℝ) * Real.log n⌋₊ ∧
          CollatzAccelOneWithin n ⌊(34881 / 10000 : ℝ) * Real.log n⌋₊)}.ncard : ℝ) := by
  obtain ⟨M, hM⟩ := exists_goodSeed
  set Z : ℝ := X / 32 with hZdef
  have hcut : (cutoff : ℝ) = 32 * (2 ^ heightExponent * seedBound + 1) := by
    rw [cutoff_def]; push_cast; ring
  have hZgt : (2 : ℝ) ^ heightExponent * seedBound < Z := by
    rw [hcut] at hX
    linarith
  obtain ⟨n, hn, hZ⟩ := exists_isAdmissibleScale_of_goodSeed hM hZgt
  have hn' : 2 * 10 ^ 10 ≤ n := by
    have := le_finalGenerationThreshold; omega
  have hZpos : 0 < Z := hZ.pos
  set S := sources n Z (M : ℚ)
  have hpos : ∀ x ∈ S, 0 < x := fun x hx => by
    exact_mod_cast hZpos.trans_le (hM.sources_subset_Ico hZ ⟨x, hx, rfl⟩).1
  have hU := lt_unweightedMass_of_goodSeed hM hn hZ
  have hch := hM.mul_unweightedMass_le hZ
  have hm : (0 : ℝ) < (modulusExponent : ℝ) := by exact_mod_cast modulusExponent_pos
  have hr : (0 : ℝ) < (modulusExponent : ℝ) ^ (5633 / 2048 : ℝ) := rpow_pos_of_pos hm _
  have hMB : (0 : ℝ) < seedBound := by exact_mod_cast seedBound_pos
  have hMle : (M : ℝ) ≤ seedBound := by exact_mod_cast hM.upper.le
  have hcount : densityConst * X ≤ (S.ncard : ℝ) := by
    have hc0 : (2 : ℝ) ^ (-28 : ℤ) * (modulusExponent : ℝ) ^ (-(5633 / 2048) : ℝ) =
        1 / (2 ^ 28 * (modulusExponent : ℝ) ^ (5633 / 2048 : ℝ)) := by
      rw [rpow_neg hm.le, zpow_neg]
      field_simp
    rw [hc0] at hU
    have h1 : Z * (1 / (2 ^ 28 * (modulusExponent : ℝ) ^ (5633 / 2048 : ℝ))) ≤
        seedBound * (S.ncard : ℝ) := by
      calc _ ≤ Z * unweightedMass n Z M := mul_le_mul_of_nonneg_left hU.le hZpos.le
        _ ≤ M * S.ncard := hch
        _ ≤ _ := mul_le_mul_of_nonneg_right hMle (Nat.cast_nonneg _)
    rw [densityConst_def, show X = 32 * Z by rw [hZdef]; ring, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    rw [mul_one_div, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have hinj : Set.InjOn Int.toNat S := fun a ha b hb hab => by
    simpa [Int.toNat_of_nonneg (hpos a ha).le, Int.toNat_of_nonneg (hpos b hb).le] using
      congrArg (fun k : ℕ => (k : ℤ)) hab
  rw [← hinj.ncard_image] at hcount
  refine hcount.trans (Nat.cast_le.2 (Set.ncard_le_ncard ?_ ?_))
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hlo, hhi⟩ := hM.sources_subset_Ico hZ ⟨x, hx, rfl⟩
    have hcast : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hpos x hx).le]
    refine ⟨by have := hpos x hx; omega, ?_, ?_, ?_⟩
    · rw [hcast]; linarith
    · rw [hcast]; exact collatzOneWithin_of_mem_sources hM hn' hZpos hx
    · rw [hcast]; exact collatzAccelOneWithin_of_mem_sources hM hn' hZpos hx
  · exact (Set.finite_Iio ⌈X⌉₊).subset fun _ hk => Set.mem_Iio.2 (Nat.lt_ceil.2 hk.2.1)

end CollatzPosDens
