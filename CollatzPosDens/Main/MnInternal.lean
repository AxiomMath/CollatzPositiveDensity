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
public import CollatzPosDens.OrdinaryTime.SourceOdd
public import CollatzPosDens.OrdinaryTime.Time
public import CollatzPosDens.OrdinaryTime.CkAccelTime

/-!
# Joint count with the construction's constants

Fix an odd endpoint `s ≥ 1` with `3 ∤ s`. For every real `X ≥ X₀(s)`, at least `c_M(s) X` odd
integers `1 ≤ n < X` reach `s` within `⌊(523/50) log(n/s)⌋₊` Collatz steps and within
`⌊(34881/10000) log(n/s)⌋₊` accelerated Collatz steps. Here
`c_M(s) = 1 / (2^33 𝓜(s) m(s)^{4097/2048})` and `X₀(s) = 32 (2^{B_ht(s)} 𝓜(s) + 1)` are the
construction's own constants.

The proof fixes an `s`-good seed `M`, puts `Z = X / 32`, chooses a generation `n ≥ J_*(s)` for
which `Z` is admissible, and counts the source set `𝒮_{n,Z}(M)`: the unweighted terminal mass
bound and the source charge give `#𝒮_{n,Z}(M) ≥ c_M(s) X`, the source window places
`𝒮_{n,Z}(M)` in `[X/32, X)`, every source is odd, and the two time lemmas give both clocks on
every source.

## Main results

* `CollatzPosDens.densityConst_mul_le_ncard_reach`: the joint count `c_M(s) X ≤ #{…}`.

## Implementation notes

The counted set is a subset of `ℕ` and its size is `Set.ncard`; the set is finite, being
contained in `{n | n < X}`, so this is its genuine number of elements. The source set lives in
`ℤ` and is transported to `ℕ` along `Int.toNat`, which is injective on positive integers. The
quotient `n / s` inside the logarithm is real division.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Joint count with the construction's constants**. For every odd
`s ≥ 1` with `3 ∤ s` and every real `X ≥ X₀(s)`, at least `c_M(s) X` odd integers `1 ≤ n < X`
reach `s` within `⌊(523/50) log(n/s)⌋₊` Collatz steps and within `⌊(34881/10000) log(n/s)⌋₊`
accelerated Collatz steps. -/
@[collatz_pos_dens "prop_mn_internal"]
theorem densityConst_mul_le_ncard_reach {s : ℕ} (hs : 0 < s) (hso : Odd s) (hs3 : ¬ 3 ∣ s)
    {X : ℝ} (hX : (cutoff s : ℝ) ≤ X) :
    densityConst s * X ≤
      ({n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (Odd n ∧ ReachWithin collatz s n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / s)⌋₊ ∧
          ReachWithin collatzAccel s n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / s)⌋₊)}.ncard : ℝ) := by
  obtain ⟨M, hM⟩ := exists_goodSeed s hs hs3
  set Z : ℝ := X / 32 with hZdef
  have hcut : (cutoff s : ℝ) = 32 * (2 ^ heightExponent s * seedBound s + 1) := by
    rw [cutoff_def]; push_cast; ring
  have hZgt : (2 : ℝ) ^ heightExponent s * seedBound s < Z := by
    rw [hZdef]; rw [hcut] at hX; linarith
  obtain ⟨n, hn, hZ⟩ := exists_isAdmissibleScale_of_goodSeed hM hs hZgt
  have hn' : 2 * 10 ^ 10 ≤ n := by
    have := le_finalGenerationThreshold s; omega
  have hZpos : 0 < Z := hZ.pos
  set S := sources n Z (M : ℚ) with hSdef
  -- counting
  have hU := lt_unweightedMass_of_goodSeed hM hs hn hZ
  have hch := hM.mul_unweightedMass_le hs hZ
  have hm : (0 : ℝ) < (modulusExponent s : ℝ) := by exact_mod_cast modulusExponent_pos s
  have hr : (0 : ℝ) < (modulusExponent s : ℝ) ^ (4097 / 2048 : ℝ) := rpow_pos_of_pos hm _
  have hMB : (0 : ℝ) < seedBound s := by exact_mod_cast seedBound_pos hs
  have hMle : (M : ℝ) ≤ seedBound s := by exact_mod_cast hM.upper.le
  have hS0 : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  have hcount : densityConst s * X ≤ (S.ncard : ℝ) := by
    have hc0 : (2 : ℝ) ^ (-28 : ℤ) * (modulusExponent s : ℝ) ^ (-(4097 / 2048) : ℝ) =
        1 / (2 ^ 28 * (modulusExponent s : ℝ) ^ (4097 / 2048 : ℝ)) := by
      rw [rpow_neg hm.le, zpow_neg]; field_simp
    rw [hc0] at hU
    have h1 : Z * (1 / (2 ^ 28 * (modulusExponent s : ℝ) ^ (4097 / 2048 : ℝ))) ≤
        seedBound s * (S.ncard : ℝ) := by
      calc _ ≤ Z * unweightedMass n Z M := mul_le_mul_of_nonneg_left hU.le hZpos.le
        _ ≤ M * S.ncard := hch
        _ ≤ _ := mul_le_mul_of_nonneg_right hMle hS0
    rw [densityConst_def]
    have hX' : X = 32 * Z := by rw [hZdef]; ring
    rw [hX']
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [mul_one_div, div_le_iff₀ (by positivity)] at h1
    nlinarith
  -- location, parity and both clocks
  have hsub : Int.toNat '' S ⊆ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (Odd n ∧ ReachWithin collatz s n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / s)⌋₊ ∧
          ReachWithin collatzAccel s n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / s)⌋₊)} := by
    rintro _ ⟨x, hx, rfl⟩
    have hw := hM.sources_subset_Ico hs hZ ⟨x, hx, rfl⟩
    obtain ⟨hlo, hhi⟩ := hw
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hZpos hlo
    have hxpos' : 0 < x := by exact_mod_cast hxpos
    have hcast : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hxpos'.le]
    refine ⟨by omega, ?_, (hM.odd_toNat_of_mem_sources hx).2, ?_, ?_⟩
    · rw [hcast]; linarith
    · rw [hcast]; exact collatzOneWithin_of_mem_sources hM hs hn' hZpos hx
    · rw [hcast]; exact collatzAccelOneWithin_of_mem_sources hs hso hM hn' hZpos hx
  have hinj : Set.InjOn Int.toNat S := by
    intro a ha b hb hab
    have ha0 : (0 : ℝ) < a :=
      lt_of_lt_of_le hZpos (hM.sources_subset_Ico hs hZ ⟨a, ha, rfl⟩).1
    have hb0 : (0 : ℝ) < b :=
      lt_of_lt_of_le hZpos (hM.sources_subset_Ico hs hZ ⟨b, hb, rfl⟩).1
    have ha0' : 0 ≤ a := by exact_mod_cast ha0.le
    have hb0' : 0 ≤ b := by exact_mod_cast hb0.le
    simpa [Int.toNat_of_nonneg ha0', Int.toNat_of_nonneg hb0'] using
      congrArg (fun k : ℕ => (k : ℤ)) hab
  have hfin : {n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (Odd n ∧ ReachWithin collatz s n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / s)⌋₊ ∧
          ReachWithin collatzAccel s n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / s)⌋₊)}.Finite := by
    refine (Set.finite_Iio ⌈X⌉₊).subset fun k hk => ?_
    exact Set.mem_Iio.2 (Nat.lt_ceil.2 hk.2.1)
  rw [← hinj.ncard_image] at hcount
  exact hcount.trans (by exact_mod_cast Set.ncard_le_ncard hsub hfin)

end CollatzPosDens
