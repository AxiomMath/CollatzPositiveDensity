/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Nt
public import CollatzPosDens.Recipe.PhBphys
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Recipe.NtValue
public import CollatzPosDens.Recipe.MomentTail

/-!
# The terminal tail after `N_t`

Let `F` be the error prefactor, `ϱ = (100/101)^{5/8}` the error decay ratio and `N_t` the
terminal threshold. Then
$$F \sum_{j \ge N_{\mathrm t}} j^{9/2} \varrho^j < 2^{-30}.$$

Since `ϱ = 𝗀^{-5/8} = 2^{-5δ/8}` and `5 δ N_t / 8 ≥ B_ph + 121 = 144 + log₂ F`
(`le_terminalThreshold`), we get `ϱ^{N_t} ≤ 2^{-144} / F`. As `N_t = 9772294 ≥ 9200000`, the
moment tail bound `moment_tail_lt` gives `F ∑_{j ≥ N_t} j^{9/2} ϱ^j < 162 N_t^{9/2} 2^{-144}`,
and `162 N_t^{9/2} < 2^{114}` follows after squaring from the exact comparison
`162² N_t⁹ < 2^{228}`.

## Main results

* `CollatzPosDens.errorDecayRatio_pow_terminalThreshold_le`: `ϱ^{N_t} ≤ 2^{-144} / F`.
* `CollatzPosDens.errorPrefactor_mul_terminalTail_lt`: the tail series is summable and
  `F ∑_{j ≥ N_t} j^{9/2} ϱ^j < 2^{-30}`.

## Implementation notes

The tail is the sum over the subtype `Set.Ici N_t` of `ℕ`, and `j^{9/2}` is `Real.rpow`.
Summability is part of the conclusion so that the bound on the `tsum` is not vacuous. Where
[mazur2026] bounds `N_t ≤ 13 · 10^6`, we use the exact value `N_t = 9772294`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- `ϱ^{N_t} ≤ 2^{-144} / F`, from the definition of `N_t`. -/
theorem errorDecayRatio_pow_terminalThreshold_le :
    errorDecayRatio ^ terminalThreshold ≤ (2 : ℝ) ^ (-144 : ℝ) / errorPrefactor := by
  have hδ := logGrowthRate_pos
  have hF := errorPrefactor_pos
  have hN := le_terminalThreshold
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 5 * logGrowthRate)] at hN
  rw [errorDecayRatio_pow_eq_rpow, ← rpow_logGrowthRate, ← Real.rpow_mul (by norm_num),
    show (2 : ℝ) ^ (-144 : ℝ) / errorPrefactor =
      (2 : ℝ) ^ (-144 - Real.logb 2 errorPrefactor) by
      rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hF]]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [physicalExponent_def] at hN
  nlinarith

/-- **Terminal tail after `N_t`.** The series `∑_{j ≥ N_t} j^{9/2} ϱ^j` is summable and
`F ∑_{j ≥ N_t} j^{9/2} ϱ^j < 2^{-30}`. -/
@[collatz_pos_dens "lem_Nt_term"]
theorem errorPrefactor_mul_terminalTail_lt :
    Summable (fun j : Set.Ici terminalThreshold =>
        ((j : ℕ) : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ)) ∧
      errorPrefactor * ∑' j : Set.Ici terminalThreshold,
        ((j : ℕ) : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ) < (2 : ℝ) ^ (-30 : ℝ) := by
  obtain ⟨hs, ht⟩ := moment_tail_lt (d := 9 / 2) le_rfl
    (n := terminalThreshold) (by rw [terminalThreshold_eq]; norm_num)
  refine ⟨hs, ?_⟩
  have hF := errorPrefactor_pos
  have hρ := errorDecayRatio_pow_terminalThreshold_le
  set N : ℝ := (terminalThreshold : ℝ) with hNdef
  have hN : N = 9772294 := by rw [hNdef, terminalThreshold_eq]; norm_num
  have hNp : 0 ≤ N ^ (9 / 2 : ℝ) := by rw [hN]; positivity
  have hkey : 162 * N ^ (9 / 2 : ℝ) < 2 ^ (114 : ℝ) := by
    have h0 : 0 ≤ 162 * N ^ (9 / 2 : ℝ) := by positivity
    refine (pow_lt_pow_iff_left₀ h0 (by positivity) (n := 2) (by norm_num)).1 ?_
    rw [mul_pow, ← Real.rpow_natCast (N ^ (9 / 2 : ℝ)), ← Real.rpow_mul (by rw [hN]; norm_num),
      ← Real.rpow_natCast ((2 : ℝ) ^ (114 : ℝ)), ← Real.rpow_mul (by norm_num), hN]
    norm_num
  calc errorPrefactor * ∑' j : Set.Ici terminalThreshold,
        ((j : ℕ) : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ)
      < errorPrefactor * (162 * (N ^ (9 / 2 : ℝ) * errorDecayRatio ^ terminalThreshold)) :=
        mul_lt_mul_of_pos_left ht hF
    _ ≤ errorPrefactor * (162 * (N ^ (9 / 2 : ℝ) * ((2 : ℝ) ^ (-144 : ℝ) / errorPrefactor))) := by
        gcongr
    _ = 162 * N ^ (9 / 2 : ℝ) * (2 : ℝ) ^ (-144 : ℝ) := by field_simp
    _ < 2 ^ (114 : ℝ) * (2 : ℝ) ^ (-144 : ℝ) :=
        mul_lt_mul_of_pos_right hkey (by positivity)
    _ = (2 : ℝ) ^ (-30 : ℝ) := by rw [← Real.rpow_add (by norm_num)]; norm_num

end CollatzPosDens
