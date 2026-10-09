/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.Jstar
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.RbLower
public import CollatzPosDens.FirstCrossing.ScalesB42
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.UpperScale
public import CollatzPosDens.Terminal.EndpointHeight
public import CollatzPosDens.Terminal.Overlap
public import CollatzPosDens.Terminal.UpperScaleHeight

/-!
# Coverage of large scales by admissible generations

Let `M` be a good seed and let `X > 2^{B_ht} 𝓜` be real. Then there is a generation
`n ≥ J_*` such that `X` is admissible for generation `n`, i.e.
`L_{b_n}(R_h) < X ≤ U_{b_n}(R_h)` for every central history `h ∈ 𝓗_n(M)`.

The proof takes the least generation `n ≥ J_*` at which `X ≤ U_{b_n}(R_h)` for every
`h ∈ 𝓗_n(M)`. Such generations exist: for `n ≥ J_*` the scale satisfies `b_n ≥ 256`, so
`r_{b_n} ≥ 0` and `U_{b_n}(R_h) ≥ 2^{b_n}` because `R_h ≥ 16^{b_n}`, while `b_n ≥ n → ∞`.
At generation `J_*` every upper scale lies below `2^{⌊2 b_{J_*}/3⌋} 2^{𝓔(J_*)} 𝓜 =
2^{B_ht} 𝓜 < X`, so if `n = J_*` the family `𝓗_{J_*}(M)` is empty; otherwise the minimality
of `n` and the overlap of consecutive scale windows give the lower bound `L_{b_n}(R_h) < X`.

## Main results

* `CollatzPosDens.exists_isAdmissibleScale_of_goodSeed`: every `X > 2^{B_ht} 𝓜` is
  admissible for some generation `n ≥ J_*`.

## Implementation notes

The source derives `b_n ≥ 256` for `n ≥ J_*` from `b_n ≥ 9 𝗀^n`; here the cruder bound
`n ≤ b_n`, which follows from the strict monotonicity of the scales, already suffices since
`J_* ≥ 20 · 10^9`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `n ≥ J_*` the scale satisfies `b_n ≥ 256`. -/
private theorem coverage_le_scale {n : ℕ} (hn : finalGenerationThreshold ≤ n) :
    256 ≤ scale n :=
  two_hundred_fifty_six_le_scale (le_trans (by have := le_finalGenerationThreshold; omega) hn)

/-- For `b ≥ 256` and `R ≥ 16^b`, the upper scale satisfies `U_b(R) ≥ 2^b`. -/
private theorem coverage_two_pow_le_upperScale {b : ℕ} (hb : 256 ≤ b) {R : ℝ}
    (hR : 16 ^ b ≤ R) : (2 : ℝ) ^ b ≤ upperScale b R := by
  have hrb : (0 : ℤ) ≤ rb b := by
    have h := rb_lower hb
    have hb' : (256 : ℝ) ≤ b := by exact_mod_cast hb
    have : (0 : ℝ) ≤ rb b := by linarith
    exact_mod_cast this
  have h4 : (4 : ℝ) ≤ 4 ^ b := le_self_pow₀ (by norm_num) (by omega)
  have h6 : (6 : ℝ) ^ b ≤ 16 ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
  rw [upperScale_eq, le_div_iff₀ (by positivity)]
  calc (2 : ℝ) ^ b * (4 * 3 ^ b) = 4 * 6 ^ b := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]
        ring
    _ ≤ 4 ^ b * 16 ^ b := by gcongr
    _ ≤ 4 ^ b * R := by gcongr
    _ ≤ 4 ^ b * R * 2 ^ rb b :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) (le_trans (by positivity) hR))
          (one_le_zpow₀ (by norm_num) hrb)

/-- The endpoint of a central history from a good seed satisfies `R_h ≥ 16^{b_n}`. -/
private theorem coverage_sixteen_pow_le {M : ℕ} (hM : GoodSeed M) {n : ℕ}
    {h : Fin n → Word} (hh : h ∈ centralHistories (M : ℚ) n) :
    (16 : ℝ) ^ scale n ≤ (historyEndpoint (M : ℚ) h : ℝ) := by
  have hh' : h ∈ centralHistories ((M : ℤ) : ℚ) n := by rwa [Int.cast_natCast]
  simpa using historyEndpointAt_large_sixteen_pow_le_endpoint (M := (M : ℤ))
    (by exact_mod_cast hM.odd) (by exact_mod_cast hM.lower.le) hh'

/-- At generation `J_*`, every upper scale of a good seed lies below `X > 2^{B_ht} 𝓜`. -/
private theorem coverage_upperScale_lt {M : ℕ} (hM : GoodSeed M) {X : ℝ}
    (hX : (2 : ℝ) ^ heightExponent * seedBound < X) {h : Fin finalGenerationThreshold → Word}
    (hh : h ∈ centralHistories (M : ℚ) finalGenerationThreshold) :
    upperScale (scale finalGenerationThreshold) (historyEndpoint (M : ℚ) h) < X := by
  have h16 := coverage_sixteen_pow_le hM hh
  have hR : (0 : ℝ) ≤ historyEndpoint (M : ℚ) h := le_trans (by positivity) h16
  have hh' : h ∈ centralHistories ((M : ℤ) : ℚ) finalGenerationThreshold := by
    rwa [Int.cast_natCast]
  have hE : (historyEndpoint (M : ℚ) h : ℝ) ≤ 2 ^ erec finalGenerationThreshold * seedBound := by
    have := historyEndpoint_le_two_pow_erec_mul_seedBound (M := (M : ℤ))
      (by exact_mod_cast hM.odd) (by exact_mod_cast hM.pos) (by exact_mod_cast hM.upper) hh'
    rw [Int.cast_natCast] at this
    exact_mod_cast this
  refine lt_of_le_of_lt ((upperScale_le_two_pow_two_mul_div_three
    (coverage_le_scale le_rfl) hR).trans ?_) hX
  calc (2 : ℝ) ^ (2 * scale finalGenerationThreshold / 3) * (historyEndpoint (M : ℚ) h : ℝ)
      ≤ 2 ^ (2 * scale finalGenerationThreshold / 3) *
          (2 ^ erec finalGenerationThreshold * seedBound) := by gcongr
    _ = 2 ^ heightExponent * seedBound := by
      rw [heightExponent_def, pow_add]
      ring

/-- For a good seed, some generation `n ≥ J_*` has all its upper scales at least `X`. -/
private theorem coverage_exists_le_upperScale {M : ℕ} (hM : GoodSeed M) (X : ℝ) :
    ∃ n, finalGenerationThreshold ≤ n ∧ ∀ h ∈ centralHistories (M : ℚ) n,
      X ≤ upperScale (scale n) (historyEndpoint (M : ℚ) h) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)
  refine ⟨max finalGenerationThreshold k, le_max_left _ _, fun h hh => ?_⟩
  calc X ≤ 2 ^ k := hk.le
    _ ≤ 2 ^ scale (max finalGenerationThreshold k) :=
        pow_le_pow_right₀ (by norm_num) ((le_max_right _ k).trans (scale_strictMono.id_le _))
    _ ≤ _ := coverage_two_pow_le_upperScale (coverage_le_scale (le_max_left _ _))
        (coverage_sixteen_pow_le hM hh)

/-- **Coverage.** Let `M` be a good seed and let `X > 2^{B_ht} 𝓜` be real. Then there is a
generation `n ≥ J_*` such that `X` is admissible for generation `n`. -/
@[collatz_pos_dens "lem_coverage"]
theorem exists_isAdmissibleScale_of_goodSeed {M : ℕ} (hM : GoodSeed M) {X : ℝ}
    (hX : (2 : ℝ) ^ heightExponent * seedBound < X) :
    ∃ n ≥ finalGenerationThreshold, IsAdmissibleScale (M : ℚ) n X := by
  classical
  have hex := coverage_exists_le_upperScale hM X
  obtain ⟨n, ⟨hJn, hup⟩, hmin⟩ : ∃ n, (finalGenerationThreshold ≤ n ∧
      ∀ h ∈ centralHistories (M : ℚ) n, X ≤ upperScale (scale n) (historyEndpoint (M : ℚ) h)) ∧
      ∀ m < n, ¬ (finalGenerationThreshold ≤ m ∧
        ∀ h ∈ centralHistories (M : ℚ) m,
          X ≤ upperScale (scale m) (historyEndpoint (M : ℚ) h)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨n, hJn, lt_of_le_of_lt (by positivity) hX, fun h hh => ⟨?_, hup h hh⟩⟩
  rcases hJn.eq_or_lt with rfl | hlt
  · exact absurd (hup h hh) (not_le.2 (coverage_upperScale_lt hM hX hh))
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h'', hh'', hlt''⟩ : ∃ h ∈ centralHistories (M : ℚ) k,
        upperScale (scale k) (historyEndpoint (M : ℚ) h) < X := by
      by_contra! H
      exact hmin k k.lt_succ_self ⟨by omega, H⟩
    have hk : 20 * 10 ^ 9 ≤ k := by have := le_finalGenerationThreshold; omega
    have hov := lowerScale_lt_upperScale_of_mem_centralHistories (M := (M : ℤ))
      (by exact_mod_cast hM.odd) (by exact_mod_cast hM.lower.le) hk
      (by rwa [Int.cast_natCast] : h'' ∈ centralHistories ((M : ℤ) : ℚ) k)
      (by rwa [Int.cast_natCast] : h ∈ centralHistories ((M : ℤ) : ℚ) (k + 1))
    simp only [Int.cast_natCast] at hov
    exact hov.trans hlt''

end CollatzPosDens
