/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.Concentration
public import CollatzPosDens.Mixing.MxBlockMarginal
public import CollatzPosDens.Mixing.MxShWidth
public import CollatzPosDens.Monotone.MoLogSqrt

/-!
# Degree deviations at a fixed index

Let `n ≥ 2^80` and `t ≤ n`, and let `h = h^sh_n = ⌈√(128 n log n)⌉` be the half-width of the
shell window. Among the words `w ∈ ℤ_{≥1}^n`, those whose prefix `w_{≤t}` has valuation sum
deviating from `2t` by at least `2h` have geometric mass
`𝐩({w : |A(w_{≤t}) - 2t| ≥ 2h}) ≤ 2 n^{-16}`.

By the block-marginal identity the mass equals that of the deviation event
`{u ∈ ℤ_{≥1}^t : |A(u) - 2t| ≥ 2h}`, which the concentration bound controls by
`2 exp (-min {4h²/(32t), 2h/8})`. Write `L = log n`. Since `h² ≥ 128 n L` and `t ≤ n`,
`4h²/(32t) ≥ h²/(8n) ≥ 16 L`. Since `L ≤ √n` and `√n ≥ 2^40 ≥ 32`, `32 L ≤ n`, so
`h² ≥ 128 n L ≥ 4096 L²`, `h ≥ 64 L` and `2h/8 ≥ 16 L`. Hence the mass is at most
`2 e^{-16 L} = 2 n^{-16}`.

## Main results

* `CollatzPosDens.geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le`: the tail bound.

## Implementation notes

The prefix `w_{≤t}` is `w.take t` and the bound `2 n^{-16}` is written
`ENNReal.ofReal (2 * n ^ (-16))` with a real power. No hypothesis `t ≥ 1` is needed: for `t = 0`
the event is empty, since `h^sh_n > 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Real

namespace CollatzPosDens

/-- The exponent estimate behind the tail bound: for `n ≥ 2^80`, `1 ≤ t ≤ n` and `v = 2 h^sh_n`,
`16 log n ≤ min (v²/(32t)) (v/8)`. -/
private lemma geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le_exponent {n t : ℕ}
    (hn : 2 ^ 80 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n) :
    16 * Real.log n ≤ min ((2 * (shWidth n : ℝ)) ^ 2 / (32 * t)) (2 * (shWidth n : ℝ) / 8) := by
  have hn' : ((2 : ℝ) ^ 80) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith [show (0 : ℝ) < 2 ^ 80 by positivity]
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  set L := Real.log n with hL
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg n
  set h := (shWidth n : ℝ) with hh
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  -- `h² ≥ 128 n L`
  have hsq : 128 * n * L ≤ h ^ 2 := by
    have h1 := sqrt_le_shWidth n
    have h2 : (0 : ℝ) ≤ 128 * n * L := by positivity
    calc 128 * n * L = Real.sqrt (128 * n * L) ^ 2 := (Real.sq_sqrt h2).symm
      _ ≤ h ^ 2 := by gcongr
  -- `32 L ≤ n`
  have hLs : L ≤ Real.sqrt n := log_le_sqrt hn0.le
  have hs32 : 32 ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) hn0.le]
    linarith [show (32 : ℝ) ^ 2 ≤ 2 ^ 80 by norm_num]
  have h32 : 32 * L ≤ n := by
    have := Real.mul_self_sqrt hn0.le
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  -- `h ≥ 64 L`
  have h64 : 64 * L ≤ h := by
    have : (64 * L) ^ 2 ≤ h ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hh0 two_ne_zero).1 this
  refine le_min ?_ (by linarith)
  rw [le_div_iff₀ (by positivity)]
  have : 16 * L * (32 * t) ≤ 16 * L * (32 * n) := by gcongr
  nlinarith

/-- **Degree deviations at a fixed index.** For `n ≥ 2^80` and `t ≤ n`,
`𝐩({w ∈ ℤ_{≥1}^n : |A(w_{≤t}) - 2t| ≥ 2 h^sh_n}) ≤ 2 n^{-16}`. -/
@[collatz_pos_dens "lem_mx_sh_probe_tail"]
theorem geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le {n t : ℕ} (hn : mxGateLevel ≤ n)
    (htn : t ≤ n) :
    geomMass {w : Word | w.length = n ∧
        2 * (shWidth n : ℝ) ≤ |(Word.valSum (w.take t) : ℝ) - 2 * t|} ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ (-16 : ℝ)) := by
  rw [mxGateLevel_def] at hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (by positivity) hn
    exact_mod_cast this
  set v := 2 * (shWidth n : ℝ) with hv
  have hv0 : 0 < v := by
    have := shWidth_pos (n := n) (le_trans (by norm_num) hn)
    have : (0 : ℝ) < shWidth n := by exact_mod_cast this
    positivity
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine (geomMass_mono (V := ∅) ?_).trans (by simp)
    rintro w ⟨-, h⟩
    simp at h
    linarith
  have hset : {w : Word | w.length = n ∧ v ≤ |(Word.valSum (w.take t) : ℝ) - 2 * t|} =
      {w : Word | w.length = n ∧ (w.drop 0).take t ∈
        {u : Word | u.length = t ∧ v ≤ |(u.valSum : ℝ) - 2 * t|}} := by
    ext w
    simp only [Set.mem_ofPred_eq, List.drop_zero]
    exact ⟨fun ⟨hw, h⟩ => ⟨hw, by simp [hw, htn], h⟩, fun ⟨hw, _, h⟩ => ⟨hw, h⟩⟩
  rw [hset, geomMass_setOf_block_mem (by omega) (fun u hu => hu.1)]
  refine (geomMass_abs_valSum_sub_ge_le t v hv0.le).trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp := geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le_exponent hn ht htn
  rw [← hv] at hexp
  have : Real.exp (-min (v ^ 2 / (32 * t)) (v / 8)) ≤ (n : ℝ) ^ (-16 : ℝ) := by
    rw [Real.rpow_def_of_pos hn0]
    exact Real.exp_le_exp.2 (by linarith)
  linarith

end CollatzPosDens
