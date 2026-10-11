/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.PhMLog
public import CollatzPosDens.Recipe.PhSeedTower

/-!
# The density bridge

For every endpoint `s ≥ 1`, the stated density `c_end(s) = 1 / (s^4 2^{2^{2^{140214}}})` is
below the construction's density constant `c_M(s)`, compared in `ℝ`.

Write `α = 5633/2048`, so `0 < α ≤ 3`. Since `1 ≤ m(s) < 𝓜(s)`, we get
`m(s)^α < 𝓜(s)^α ≤ 𝓜(s)^3`, hence, using `𝓜(s) = s 𝓜(1)`,
$$c_M(s)^{-1} = 2^{33} 𝓜(s) m(s)^α < 2^{33} 𝓜(s)^4 = s^4 \cdot 2^{33} 𝓜(1)^4
  < s^4 \cdot 2^{2^{2^{140214}}},$$
by the seed tower bound. Taking reciprocals gives `c_end(s) < c_M(s)`.

## Main results

* `CollatzPosDens.inv_densityConst_lt`: `c_M(s)⁻¹ < s^4 2^{2^{2^{140214}}}` for `0 < s`.
* `CollatzPosDens.collatzDensityDep_lt_densityConst`: `c_end(s) < c_M(s)` for `0 < s`.

## Implementation notes

The tower `2^{2^{2^{140214}}}` is never evaluated: it enters only as the natural number in the
seed tower bound `two_pow_mul_seedBound_one_pow_lt` and through its cast to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `c_M(s)⁻¹ < s^4 2^{2^{2^{140214}}}` for every `s ≥ 1`. -/
theorem inv_densityConst_lt {s : ℕ} (hs : 0 < s) :
    (densityConst s)⁻¹ < (s : ℝ) ^ 4 * ((2 ^ 2 ^ 2 ^ 140214 : ℕ) : ℝ) := by
  have hT : ((2 ^ 33 * seedBound 1 ^ 4 : ℕ) : ℝ) < ((2 ^ 2 ^ 2 ^ 140214 : ℕ) : ℝ) :=
    Nat.cast_lt.2 two_pow_mul_seedBound_one_pow_lt
  generalize ((2 ^ 2 ^ 2 ^ 140214 : ℕ) : ℝ) = T at hT ⊢
  have hM1 : (1 : ℝ) ≤ seedBound s := by exact_mod_cast one_le_seedBound hs
  have hm0 : (0 : ℝ) ≤ modulusExponent s := Nat.cast_nonneg _
  have hmM : (modulusExponent s : ℝ) < seedBound s := by
    exact_mod_cast modulusExponent_lt_seedBound hs
  have hpow : (modulusExponent s : ℝ) ^ (5633 / 2048 : ℝ) < (seedBound s : ℝ) ^ 3 := by
    calc (modulusExponent s : ℝ) ^ (5633 / 2048 : ℝ)
        < (seedBound s : ℝ) ^ (5633 / 2048 : ℝ) :=
          Real.rpow_lt_rpow hm0 hmM (by norm_num)
      _ ≤ (seedBound s : ℝ) ^ ((3 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
      _ = (seedBound s : ℝ) ^ 3 := Real.rpow_natCast _ 3
  have hs4 : (0 : ℝ) < (s : ℝ) ^ 4 := by positivity
  rw [inv_densityConst]
  calc 2 ^ 33 * (seedBound s : ℝ) * (modulusExponent s : ℝ) ^ (5633 / 2048 : ℝ)
      < 2 ^ 33 * (seedBound s : ℝ) * (seedBound s : ℝ) ^ 3 := by
        gcongr
    _ = (s : ℝ) ^ 4 * ((2 ^ 33 * seedBound 1 ^ 4 : ℕ) : ℝ) := by
        rw [seedBound_eq_mul s]
        push_cast
        ring
    _ < (s : ℝ) ^ 4 * T := mul_lt_mul_of_pos_left hT hs4

/-- **The density bridge**: for every `s ≥ 1`, the stated density
`c_end(s) = 1 / (s^4 2^{2^{2^{140214}}})` is below the construction's density constant `c_M(s)`,
compared in `ℝ`. -/
@[collatz_pos_dens "lem_invc_tower"]
theorem collatzDensityDep_lt_densityConst {s : ℕ} (hs : 0 < s) :
    ((collatzDensityDep s : ℚ) : ℝ) < densityConst s := by
  have hcast : ((collatzDensityDep s : ℚ) : ℝ) =
      ((s : ℝ) ^ 4 * ((2 ^ 2 ^ 2 ^ 140214 : ℕ) : ℝ))⁻¹ := by
    simp only [collatzDensityDep, one_div, Rat.cast_inv, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have h := inv_densityConst_lt hs
  have hc := densityConst_pos hs
  rw [hcast, ← inv_inv (densityConst s)]
  exact (inv_lt_inv₀ (by positivity) (inv_pos.2 hc)).2 h

end CollatzPosDens
