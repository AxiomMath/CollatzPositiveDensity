/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.CovExp
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.S04BhtLe
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.FirstCrossing.RbLower
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.UpperScale
public import CollatzPosDens.Terminal.EndpointHeight
public import CollatzPosDens.Terminal.Overlap
public import CollatzPosDens.Terminal.UpperScaleHeight

/-!
# Reachability: coverage of large scales by admissible generations

Let `t ≥ t_min` (`targetFloor`, equal to `16^{b_0}`) be an odd integer and let
`X ≥ 2^{Λ_cov} t` be real, where `Λ_cov = 2^{352}` is the coverage exponent (`covExp`). Then
there is a generation `j ≥ J_c = 23000` (`covGen`) such that `X` is admissible for
generation `j`, i.e. `L_{b_j}(R_h) < X ≤ U_{b_j}(R_h)` for every central history `h ∈ 𝓗_j(t)`.

The proof takes the least generation `j ≥ J_c` at which `X ≤ U_{b_j}(R_h)` for every
`h ∈ 𝓗_j(t)`. Such generations exist: since `t ≥ t_min`, the endpoints satisfy `R_h ≥ 16^{b_n}`;
every scale satisfies `b_n ≥ 16544 ≥ 256`, so `r_{b_n} ≥ 0` and `U_{b_n}(R_h) ≥ 2^{b_n}`,
while `b_n ≥ n → ∞`. At generation `J_c` every upper scale lies below
`2^{⌊2 b_{J_c}/3⌋} 2^{𝓔(J_c)} t = 2^{B_ht} t < 2^{Λ_cov} t ≤ X`, so if `j = J_c` the family
`𝓗_{J_c}(t)` is empty; otherwise the minimality of `j` and the overlap of consecutive scale
windows give the lower bound `L_{b_j}(R_h) < X`.

## Main results

* `CollatzPosDens.exists_isAdmissibleScale_of_goodSeed`: every `X ≥ 2^{Λ_cov} t` is admissible
  for some generation `j ≥ J_c`.

## Implementation notes

The unboundedness of the scales is usually derived from `b_n ≥ 16544 𝗀^n`; here the cruder
bound `n ≤ b_n`, which follows from the strict monotonicity of the scales, already suffices.
The odd integer `t ≥ t_min` is taken in `ℕ`, which loses nothing since `t_min > 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Every scale satisfies `b_n ≥ 256`. -/
private theorem coverage_le_scale (n : ℕ) : 256 ≤ scale n :=
  le_trans (by norm_num) (sixteen544_le_scale n)

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

/-- For odd `t ≥ t_min`, the endpoint of a central history from `t` satisfies
`R_h ≥ 16^{b_n}`. -/
private theorem coverage_sixteen_pow_le {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t) {n : ℕ}
    {h : Fin n → Word} (hh : h ∈ centralHistories (t : ℚ) n) :
    (16 : ℝ) ^ scale n ≤ (historyEndpoint (t : ℚ) h : ℝ) := by
  have hh' : h ∈ centralHistories ((t : ℤ) : ℚ) n := by rwa [Int.cast_natCast]
  obtain ⟨m, hm, -, hle⟩ := historyEndpointAt_large (t := (t : ℤ)) (by exact_mod_cast hodd)
    (by exact_mod_cast ht) hh' le_rfl
  have hm' : historyEndpoint (t : ℚ) h = m := by
    rw [historyEndpoint, ← hm, Int.cast_natCast]
  rw [hm', Rat.cast_intCast]
  exact_mod_cast hle

/-- `2^{B_ht} t < 2^{Λ_cov} t` for `t > 0`. -/
private theorem coverage_two_pow_heightExponent_mul_lt {t : ℕ} (ht : 0 < t) :
    (2 : ℝ) ^ heightExponent * t < (2 : ℝ) ^ covExp * t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  exact mul_lt_mul_of_pos_right (pow_lt_pow_right₀ (by norm_num) heightExponent_lt_covExp) htR

/-- At every generation `J`, every upper scale from odd `t ≥ t_min` is at most
`2^{𝓔(J) + ⌊2b_J/3⌋} t`. -/
private theorem coverage_upperScale_le {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t) {J : ℕ}
    {h : Fin J → Word} (hh : h ∈ centralHistories (t : ℚ) J) :
    upperScale (scale J) (historyEndpoint (t : ℚ) h) ≤ (2 : ℝ) ^ heightExponentOf J * t := by
  have h16 := coverage_sixteen_pow_le hodd ht hh
  have hR : (0 : ℝ) ≤ historyEndpoint (t : ℚ) h := le_trans (by positivity) h16
  have hh' : h ∈ centralHistories ((t : ℤ) : ℚ) J := by
    rwa [Int.cast_natCast]
  have hE : (historyEndpoint (t : ℚ) h : ℝ) ≤ 2 ^ erec J * t := by
    have := historyEndpoint_le_two_pow_erec_mul (t := (t : ℤ))
      (by exact_mod_cast hodd) (by exact_mod_cast targetFloor_pos.trans_le ht) hh'
    rw [Int.cast_natCast] at this
    exact_mod_cast this
  refine (upperScale_le_two_pow_two_mul_div_three (scale J) hR).trans ?_
  calc (2 : ℝ) ^ (2 * scale J / 3) * (historyEndpoint (t : ℚ) h : ℝ)
      ≤ 2 ^ (2 * scale J / 3) * (2 ^ erec J * t) := by gcongr
    _ = 2 ^ heightExponentOf J * t := by
      rw [heightExponentOf_def, pow_add]
      ring

/-- At generation `J_c`, every upper scale from odd `t ≥ t_min` lies below `X ≥ 2^{Λ_cov} t`. -/
private theorem coverage_upperScale_lt {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t) {X : ℝ}
    (hX : (2 : ℝ) ^ covExp * t ≤ X) {h : Fin covGen → Word}
    (hh : h ∈ centralHistories (t : ℚ) covGen) :
    upperScale (scale covGen) (historyEndpoint (t : ℚ) h) < X := by
  have hle := coverage_upperScale_le hodd ht hh
  rw [← heightExponent_eq_heightExponentOf] at hle
  exact (hle.trans_lt (coverage_two_pow_heightExponent_mul_lt
    (targetFloor_pos.trans_le ht))).trans_le hX

/-- For odd `t ≥ t_min`, some generation `n ≥ J_c` has all its upper scales at least `X`. -/
private theorem coverage_exists_le_upperScale {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t)
    (X : ℝ) :
    ∃ n, covGen ≤ n ∧ ∀ h ∈ centralHistories (t : ℚ) n,
      X ≤ upperScale (scale n) (historyEndpoint (t : ℚ) h) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)
  refine ⟨max covGen k, le_max_left _ _, fun h hh => ?_⟩
  calc X ≤ 2 ^ k := hk.le
    _ ≤ 2 ^ scale (max covGen k) :=
        pow_le_pow_right₀ (by norm_num) ((le_max_right _ k).trans (scale_strictMono.id_le _))
    _ ≤ _ := coverage_two_pow_le_upperScale (coverage_le_scale _)
        (coverage_sixteen_pow_le hodd ht hh)

/-- `lowerScale_lt_upperScale_of_mem_centralHistories` for a natural-number target `t`. -/
private theorem coverage_lowerScale_lt_upperScale {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t)
    {j : ℕ} (hj : covGen ≤ j) {h : Fin j → Word}
    {h' : Fin (j + 1) → Word} (hh : h ∈ centralHistories (t : ℚ) j)
    (hh' : h' ∈ centralHistories (t : ℚ) (j + 1)) :
    lowerScale (scale (j + 1)) (historyEndpoint (t : ℚ) h') <
      upperScale (scale j) (historyEndpoint (t : ℚ) h) := by
  have hq : ((t : ℤ) : ℚ) = (t : ℚ) := Int.cast_natCast t
  have := lowerScale_lt_upperScale_of_mem_centralHistories (t := (t : ℤ))
    (by exact_mod_cast hodd) (by exact_mod_cast ht) hj (hq ▸ hh) (hq ▸ hh')
  rwa [hq] at this

/-- **Reachability.** Let `t ≥ t_min` (`targetFloor`) be an odd integer. Every real
`X ≥ 2^{Λ_cov} t`, with `Λ_cov = covExp`, is admissible for some generation `j` with
`j ≥ J_c = covGen`. -/
@[collatz_pos_dens "lem_coverage"]
theorem exists_isAdmissibleScale_of_goodSeed {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t) {X : ℝ}
    (hX : (2 : ℝ) ^ covExp * t ≤ X) :
    ∃ j : ℕ, covGen ≤ j ∧ IsAdmissibleScale (t : ℚ) j X := by
  classical
  have hex := coverage_exists_le_upperScale hodd ht X
  obtain ⟨n, ⟨hJn, hup⟩, hmin⟩ : ∃ n, (covGen ≤ n ∧
      ∀ h ∈ centralHistories (t : ℚ) n, X ≤ upperScale (scale n) (historyEndpoint (t : ℚ) h)) ∧
      ∀ m < n, ¬ (covGen ≤ m ∧
        ∀ h ∈ centralHistories (t : ℚ) m,
          X ≤ upperScale (scale m) (historyEndpoint (t : ℚ) h)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have htpos := targetFloor_pos.trans_le ht
  refine ⟨n, hJn, lt_of_lt_of_le (by positivity) hX, fun h hh => ⟨?_, hup h hh⟩⟩
  rcases hJn.eq_or_lt with rfl | hlt
  · exact absurd (hup h hh) (not_le.2 (coverage_upperScale_lt hodd ht hX hh))
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h'', hh'', hlt''⟩ : ∃ h ∈ centralHistories (t : ℚ) k,
        upperScale (scale k) (historyEndpoint (t : ℚ) h) < X := by
      by_contra! H
      exact hmin k k.lt_succ_self ⟨by omega, H⟩
    have hk : covGen ≤ k := by omega
    exact (coverage_lowerScale_lt_upperScale hodd ht hk hh'' hh).trans hlt''

end CollatzPosDens
