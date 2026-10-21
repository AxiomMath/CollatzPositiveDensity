/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Mixing.MxSubmassTotal
public import CollatzPosDens.Mixing.MxOffsetTail
public import CollatzPosDens.Terminal.S06ClipLeRef
public import CollatzPosDens.Terminal.S06ClipCentralLoss
public import CollatzPosDens.Terminal.S06ClipFloorLoss
public import CollatzPosDens.Terminal.S06ClipWidthBound

/-!
# Mean deficit of the clipped subdensity

For integers `1 ≤ m ≤ n` with `n ≥ 3` and every real `B > 0`,
$$\langle \rho_m - g^{\mathrm{clp}}_{m,n,B} \rangle_m
  ≤ 2 n^{-8} + \frac{2^{13}\sqrt{n \log n}}{B}.$$

Write `𝒱 = 𝒱^clp_{m,n,B}`, `w = w^clp_{m,n}` and `L = L^clp_{m,n,B}`. The reference density has
mean `1` and the clipped subdensity has mean `𝐩(𝒱)`, so the deficit is `1 - 𝐩(𝒱)`, which is at
most the mass of the words of length `m` outside `𝒱`. Such a word has valuation sum outside the
central window `[2m - w, 2m + w]`, or below the degree floor `A^clp_{m,B}`, or offset above `L`;
the three losses are at most `2 n^{-8}`, `8 / B` and `7 / (L + 2) < 28 (2w + 1) / B`. The width
bound `2w + 1 ≤ 256 √(n log n)` and `√(n log n) ≥ 1` give the total `7176 √(n log n) / B`, and
`7176 < 2^{13}`.

## Main results

* `CollatzPosDens.residueAvg_clipDensity`: `⟨g^clp_{m,n,B}⟩_m = 𝐩(𝒱^clp_{m,n,B})`.
* `CollatzPosDens.residueAvg_refDensity_sub_clipDensity_le`: the mean deficit bound above.

## Implementation notes

The power `n^{-8}` is written `((n : ℝ) ^ 8)⁻¹` and `log` is `Real.log`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The clipped words have finite geometric mass, at most `1`. -/
theorem geomMass_clipWords_le_one (m n : ℕ) (B : ℝ) : geomMass (clipWords m n B) ≤ 1 :=
  (geomMass_mono fun _ hu => length_of_mem_clipWords hu).trans (geomMass_setOf_length_eq m).le

/-- The clipped subdensity has mean `⟨g^clp_{m,n,B}⟩_m = 𝐩(𝒱^clp_{m,n,B})`. -/
theorem residueAvg_clipDensity (m n : ℕ) (B : ℝ) :
    residueAvg m (clipDensity m n B) = (geomMass (clipWords m n B)).toReal := by
  have hfin : ∀ y : ResidueGroup m, subMass m (clipWords m n B) y ≠ ⊤ := fun y =>
    ((subMass_le_geomMass m _ y).trans (geomMass_clipWords_le_one m n B)).trans_lt
      ENNReal.one_lt_top |>.ne
  rw [residueAvg_def]
  simp_rw [clipDensity_def]
  rw [← Finset.mul_sum, ← ENNReal.toReal_sum fun y _ => hfin y, sum_subMass, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- **Mean deficit of the clipped subdensity.** For integers `1 ≤ m ≤ n` with `n ≥ 3` and every
real `B > 0`, `⟨ρ_m - g^clp_{m,n,B}⟩_m ≤ 2 n^{-8} + 2^{13} √(n log n) / B`. -/
@[collatz_pos_dens "lem_s06_clip_deficit"]
theorem residueAvg_refDensity_sub_clipDensity_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : 3 ≤ n) {B : ℝ} (hB : 0 < B) :
    residueAvg m (fun y => refDensity m y - clipDensity m n B y) ≤
      2 * ((n : ℝ) ^ 8)⁻¹ + 2 ^ 13 * √(n * Real.log n) / B := by
  set L : ℝ := clipCap m n B with hL
  set x : ℝ := (geomMass (clipWords m n B)).toReal with hx
  have hL0 : 0 < L := clipCap_pos m n hB
  have havg : residueAvg m (fun y => refDensity m y - clipDensity m n B y) = 1 - x := by
    have h1 := residueAvg_refDensity m
    have h2 := residueAvg_clipDensity m n B
    rw [residueAvg_def] at h1 h2 ⊢
    rw [Finset.sum_sub_distrib, mul_sub, h1, h2]
  set C : Set Word := {u : Word | u.length = m ∧ ((u.valSum : ℤ) < 2 * m - clipWidth m n ∨
    2 * m + clipWidth m n < (u.valSum : ℤ))} with hC
  set F : Set Word := {u : Word | u.length = m ∧ (u.valSum : ℤ) < clipFloor m B} with hF
  set T : Set Word := {u : Word | u.length = m ∧ L ≤ (off u : ℝ)} with hT
  have hcover : {u : Word | u.length = m} ⊆ clipWords m n B ∪ C ∪ F ∪ T := by
    intro u hu
    have hlen : u.length = m := hu
    have hmA : (m : ℤ) ≤ u.valSum := by
      rw [← hlen]
      exact_mod_cast Word.length_le_valSum u
    by_cases hV : u ∈ clipWords m n B
    · exact Or.inl (Or.inl (Or.inl hV))
    · simp only [mem_clipWords, mem_clipWindow, max_le_iff, not_and, not_le] at hV
      by_cases hoff : (off u : ℝ) ≤ L
      · by_cases hc : (2 * m - clipWidth m n : ℤ) ≤ u.valSum ∧
            (u.valSum : ℤ) ≤ 2 * m + clipWidth m n
        · have hf : (u.valSum : ℤ) < clipFloor m B := by
            by_contra hf
            exact absurd hoff (not_le.2 (hV hlen ⟨hc.1, hc.2, hmA, not_lt.1 hf⟩))
          exact Or.inl (Or.inr ⟨hlen, hf⟩)
        · refine Or.inl (Or.inl (Or.inr ⟨hlen, ?_⟩))
          omega
      · exact Or.inr ⟨hlen, (not_le.1 hoff).le⟩
  have hmass : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (x + 2 * ((n : ℝ) ^ 8)⁻¹ + 8 / B + 7 / (L + 2)) := by
    have hxfin : geomMass (clipWords m n B) ≠ ⊤ :=
      ((geomMass_clipWords_le_one m n B).trans_lt ENNReal.one_lt_top).ne
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), hx, ENNReal.ofReal_toReal hxfin,
      ← geomMass_setOf_length_eq m]
    refine (geomMass_mono hcover).trans ?_
    refine (geomMass_union_le _ _).trans (add_le_add ?_ (geomMass_offsetTail_le m hL0.le))
    refine (geomMass_union_le _ _).trans (add_le_add ?_ (geomMass_valSum_lt_clipFloor_lt m hB).le)
    refine (geomMass_union_le _ _).trans (add_le_add le_rfl ?_)
    exact geomMass_valSum_not_mem_central_le hm (by omega)
  have hreal := ENNReal.one_le_ofReal.1 hmass
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_68_div_25]
  set s : ℝ := √(n * Real.log n) with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith)
  have hwidth := two_mul_clipWidth_add_one_le hmn hn
  have hT7 : 7 / (L + 2) ≤ 7168 * s / B := by
    have hLdef : 4 * (2 * clipWidth m n + 1) * L = B := mul_clipCap m n B
    have h1 : 7 / (L + 2) ≤ 7 / L := by gcongr; linarith
    have h2 : 7 / L = 28 * (2 * clipWidth m n + 1) / B := by
      rw [← hLdef]
      field_simp
      ring
    rw [h2] at h1
    refine h1.trans (div_le_div_of_nonneg_right ?_ hB.le)
    rw [hs]
    linarith
  have h8 : 8 / B ≤ 8 * s / B := by gcongr; linarith
  have hfin : 7168 * s / B + 8 * s / B ≤ 2 ^ 13 * s / B := by
    rw [← add_div]
    gcongr
    nlinarith
  rw [havg]
  linarith

end CollatzPosDens
