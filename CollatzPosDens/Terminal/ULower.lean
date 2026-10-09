/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Jstar
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.MAvailable
public import CollatzPosDens.Recipe.MGate
public import CollatzPosDens.Recipe.MixingErrorSmall
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.Census
public import CollatzPosDens.Terminal.MarkLower
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Transfer.Log2C
public import CollatzPosDens.Mixing.Mixing
public import CollatzPosDens.Mixing.MxSubdensityDeficit

/-!
# Lower bound for the unweighted mass

Let `M` be a good seed, let `n ≥ finalGenerationThreshold`, and let `X` be an admissible scale
for generation `n`. Then the unweighted mass satisfies
`2^{-28} m^{-5633/2048} < unweightedMass n X M`, where `m = modulusExponent`.

For such `n` the marked mass exceeds `2^{-25}` and `2^131072 ≤ m`. Combining the census bound
for the marked mass with the mixing estimate and the subdensity deficit at `m` gives
`2^{-25} < (64/9) m^{5633/2048} Υ + (88/3) M (C + 1) / m^{9/8}`, where `Υ` is the unweighted
mass and `C = mixingConst`, and the error term is below `(11/6144) 2^{-24}` because
`M < seedBound`, `C + 1 < 2C` and `m^{9/8} > 2^39 seedBound C`.

## Main results

* `CollatzPosDens.lt_unweightedMass_of_goodSeed`: `2^{-28} m^{-5633/2048} < unweightedMass n X M`
  for a good seed `M`, `finalGenerationThreshold ≤ n` and an admissible scale `X`.

## Implementation notes

The power `m^{-5633/2048}` is the real power `(m : ℝ) ^ (-(5633 / 2048) : ℝ)`.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `M` is a good seed, `finalGenerationThreshold ≤ n` and `X` is an admissible scale for
generation `n`, then `2^{-28} m^{-5633/2048} < unweightedMass n X M`, where
`m = modulusExponent`. -/
@[collatz_pos_dens "lem_U_lower"]
theorem lt_unweightedMass_of_goodSeed {M : ℕ} (hM : GoodSeed M) {n : ℕ}
    (hn : finalGenerationThreshold ≤ n) {X : ℝ} (hX : IsAdmissibleScale M n X) :
    (2 : ℝ) ^ (-28 : ℤ) * (modulusExponent : ℝ) ^ (-(5633 / 2048) : ℝ) <
      unweightedMass n X M := by
  have hΘ :=
    two_zpow_neg_twentyFive_lt_markedMass hM (add_le_finalGenerationThreshold.trans hn) hX
  obtain ⟨-, hmk⟩ := modulusExponent_available (lg_sub_le_finalGenerationThreshold.trans hn)
  have hgate := two_pow_lt_modulusExponent.le
  have h16 : 16 ≤ modulusExponent := by
    have h4 : 4 ≤ (131072 : ℕ) := by norm_num
    revert hgate h4
    generalize (131072 : ℕ) = k
    intro hgate h4
    exact (Nat.pow_le_pow_right (n := 2) (by norm_num) h4).trans hgate
  have hcen := hM.markedMass_le_census hX h16 hmk
  have hsmall := lt_modulusExponent_rpow
  have hC : (1 : ℝ) ≤ mixingConst := one_le_mixingConst
  have hMle : (M : ℝ) ≤ seedBound := by exact_mod_cast hM.upper.le
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  have hS0 : (0 : ℝ) < seedBound := by exact_mod_cast seedBound_pos
  have hm0 : (0 : ℝ) < modulusExponent :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by positivity) hgate)
  set u : ℝ := (modulusExponent : ℝ) ^ (9 / 8 : ℝ)
  have hu0 : 0 < u := by positivity
  set t : ℝ := (modulusExponent : ℝ) ^ ((5633 : ℝ) / 2048) with ht
  have ht0 : 0 < t := by positivity
  have hneg : (modulusExponent : ℝ) ^ (-(5633 / 2048) : ℝ) = t⁻¹ := by
    rw [ht, ← Real.rpow_neg hm0.le]
  rw [hneg]
  have e24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 := by norm_num
  have herr : 44 * (M : ℝ) * (2 * mixingConst / (3 * u) + 2 / (3 * u)) <
      11 / 6144 * (2 : ℝ) ^ (-24 : ℤ) := by
    have e1 : 44 * (M : ℝ) * (2 * mixingConst / (3 * u) + 2 / (3 * u)) =
        88 / 3 * (M * (mixingConst + 1)) / u := by
      field_simp
      ring
    rw [e1, div_lt_iff₀ hu0, e24]
    have h2 : (M : ℝ) * (mixingConst + 1) ≤ seedBound * (2 * mixingConst) :=
      mul_le_mul hMle (by linarith) (by linarith) hS0.le
    nlinarith
  have key : (2 : ℝ) ^ (-25 : ℤ) < 64 / 9 * t * unweightedMass n X M +
      11 / 6144 * (2 : ℝ) ^ (-24 : ℤ) := by
    refine hΘ.trans_le (hcen.trans ?_)
    have := mul_le_mul_of_nonneg_left
      (add_le_add (residueAvg_abs_refDensity_sub_le_of_two_pow_le hgate hmk)
        (residueAvg_refDensity_sub_mxSubdensity_le modulusExponent hgate))
      (by positivity : (0 : ℝ) ≤ 44 * M)
    linarith
  rw [show (2 : ℝ) ^ (-25 : ℤ) = 1 / 2 ^ 25 by norm_num, e24] at key
  rw [show (2 : ℝ) ^ (-28 : ℤ) = 1 / 2 ^ 28 by norm_num, ← div_eq_mul_inv,
    div_div, div_lt_iff₀ (by positivity)]
  nlinarith

end CollatzPosDens
