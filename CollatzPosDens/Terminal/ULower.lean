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

Let `s ≥ 1`, let `M` be an `s`-good seed, `n ≥ J_*(s)`, and let `X` be admissible for
generation `n`. Then the unweighted mass satisfies `Υ_{n,X}(M) > 2^{-28} m(s)^{-5633/2048}`,
where `m(s)` is the modulus exponent.

Since `n ≥ N_* + N_t`, the marked mass satisfies `Θ_{n,X}(M) > 2^{-25}`; since
`n ≥ 200 max(lg m(s) - 1, 0)`, the exponent satisfies `2^131072 ≤ m(s) ≤ k_n`. The census at
`m' = m(s)`, the mixing lemma at `(m(s), k_n)` and the subdensity deficit at `m(s)` give
`2^{-25} < (64/9) m(s)^{5633/2048} Υ + (88/3) M (C + 1) / m(s)^{9/8}`, and the error term is
below `(11/6144) 2^{-24}` because `M < 𝓜(s)`, `C + 1 < 2C` and `m(s)^{9/8} > 2^39 𝓜(s) C`.

## Main results

* `CollatzPosDens.lt_unweightedMass_of_goodSeed`: `2^{-28} m(s)^{-5633/2048} < Υ_{n,X}(M)`.

## Implementation notes

The power `m^{-5633/2048}` is the real power `(modulusExponent s : ℝ) ^ (-(5633 / 2048) : ℝ)`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Unweighted mass lower bound**. Let `s ≥ 1`, let `M` be an `s`-good seed,
`n ≥ J_*(s)`, and let `X` be admissible for generation `n`. Then
`Υ_{n,X}(M) > 2^{-28} m(s)^{-5633/2048}`. -/
@[collatz_pos_dens "lem_U_lower"]
theorem lt_unweightedMass_of_goodSeed {s M : ℕ} (hM : GoodSeed s M) (hs : 0 < s)
    {n : ℕ} (hn : finalGenerationThreshold s ≤ n) {X : ℝ} (hX : IsAdmissibleScale M n X) :
    (2 : ℝ) ^ (-28 : ℤ) * (modulusExponent s : ℝ) ^ (-(5633 / 2048) : ℝ) <
      unweightedMass n X M := by
  have hΘ :=
    two_zpow_neg_twentyFive_lt_markedMass hM hs ((add_le_finalGenerationThreshold s).trans hn) hX
  obtain ⟨-, hmk⟩ := modulusExponent_available s ((lg_sub_le_finalGenerationThreshold s).trans hn)
  have hgate := (two_pow_lt_modulusExponent hs).le
  have h16 : 16 ≤ modulusExponent s := by
    have h4 : 4 ≤ (131072 : ℕ) := by norm_num
    revert hgate h4
    generalize (131072 : ℕ) = k
    intro hgate h4
    exact (Nat.pow_le_pow_right (n := 2) (by norm_num) h4).trans hgate
  have hcen := hM.markedMass_le_census hs hX h16 hmk
  have hsmall := lt_modulusExponent_rpow s
  have hC : (1 : ℝ) ≤ mixingConst := one_le_mixingConst
  have hMle : (M : ℝ) ≤ seedBound s := by exact_mod_cast hM.upper.le
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  have hS0 : (0 : ℝ) < seedBound s := by exact_mod_cast seedBound_pos hs
  have hm0 : (0 : ℝ) < modulusExponent s :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by positivity) hgate)
  set u : ℝ := (modulusExponent s : ℝ) ^ (9 / 8 : ℝ)
  have hu0 : 0 < u := by positivity
  set t : ℝ := (modulusExponent s : ℝ) ^ ((5633 : ℝ) / 2048) with ht
  have ht0 : 0 < t := by positivity
  have hneg : (modulusExponent s : ℝ) ^ (-(5633 / 2048) : ℝ) = t⁻¹ := by
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
    have h2 : (M : ℝ) * (mixingConst + 1) ≤ seedBound s * (2 * mixingConst) :=
      mul_le_mul hMle (by linarith) (by linarith) hS0.le
    nlinarith
  have key : (2 : ℝ) ^ (-25 : ℤ) < 64 / 9 * t * unweightedMass n X M +
      11 / 6144 * (2 : ℝ) ^ (-24 : ℤ) := by
    refine hΘ.trans_le (hcen.trans ?_)
    have := mul_le_mul_of_nonneg_left
      (add_le_add (residueAvg_abs_refDensity_sub_le_of_two_pow_le hgate hmk)
        (residueAvg_refDensity_sub_mxSubdensity_le (modulusExponent s) hgate))
      (by positivity : (0 : ℝ) ≤ 44 * M)
    linarith
  have e25 : (2 : ℝ) ^ (-25 : ℤ) = 1 / 2 ^ 25 := by norm_num
  have e28 : (2 : ℝ) ^ (-28 : ℤ) = 1 / 2 ^ 28 := by norm_num
  rw [e25, e24] at key
  rw [e28, ← div_eq_mul_inv, div_div, div_lt_iff₀ (by positivity)]
  nlinarith

end CollatzPosDens
