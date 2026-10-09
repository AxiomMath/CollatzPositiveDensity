/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.FirstCrossing.Overshoot
public import CollatzPosDens.Mixing.MxLevel

/-!
# Excessive overshoot is rare

Let `V` be a real level and `K ≥ 0` an integer. Among the words `w ∈ ℤ_{≥1}^n`, consider those
whose prefix sums cross `V` at some step `i` (that is, `A(w_{≤ i-1}) ≤ V < A(w_{≤ i})`) and
overshoot it by a lot, namely `⌊V⌋ + 1 + K < A(w_{≤ i})`. Their geometric mass is at most
`2^{-(K+1)}`: lowering the crossing letter by `K + 1` maps these words injectively onto words
of length `n` and multiplies the weight `2^{-A(w)}` by exactly `2^{K+1}`, while the words of
length `n` have total mass `1`.

With `V = mxLevel n` and `K = ⌈(9/8) log₂ n⌉` this gives the bound
`2^{-K-1} ≤ (1/2) n^{-9/8}`.

## Main results

* `CollatzPosDens.geomMass_mxOvershootTail_le_two_inv_pow`: for every real level `V` and
  every `K ∈ ℕ`, the overshooting words have mass at most `2^{-(K+1)}`.
* `CollatzPosDens.geomMass_mxOvershootTail_le`: with `V = mxLevel n` and
  `K = ⌈(9/8) log₂ n⌉`, the mass is at most `(1/2) n^{-9/8}`.

## Implementation notes

Words of length `n` are lists of length `n`, and `w_{≤ i}` is `w.take i`. The level conditions
are compared in `ℝ`, the overshoot condition in `ℤ`, and the bound `(1/2) n^{-9/8}` is a real
number embedded by `ENNReal.ofReal`.

The source assumes `n ≥ 2^131072` in order to have `mxLevel n > 0`. The argument does not need it:
if the level is negative no word crosses it, and for `n ≥ 1` the integer `⌈(9/8) log₂ n⌉` is
nonnegative, while for `n = 0` the set is empty. The bound is therefore stated for every `n`.

The general-level bound is the overshoot loss `geomMass_overshoot_le_of_monotone` for the
constant barrier `⌊V⌋ + 1`: a word crossing `V` at step `i` stays below `⌊V⌋ + 1` before `i`,
because its prefix sums are monotone.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For a real level `V` and `K ∈ ℕ`, the words `w ∈ ℤ_{≥1}^n` with some `1 ≤ i ≤ n` such that
`A(w_{≤ i-1}) ≤ V < A(w_{≤ i})` and `⌊V⌋ + 1 + K < A(w_{≤ i})` have geometric mass at most
`2^{-(K+1)}`. -/
theorem geomMass_mxOvershootTail_le_two_inv_pow (n : ℕ) (V : ℝ) (K : ℕ) :
    geomMass {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
      (Word.valSum (w.take (i - 1)) : ℝ) ≤ V ∧ V < (Word.valSum (w.take i) : ℝ) ∧
      ⌊V⌋ + 1 + (K : ℤ) < (Word.valSum (w.take i) : ℤ)} ≤ 2⁻¹ ^ (K + 1) := by
  refine le_trans (geomMass_mono ?_)
    (geomMass_overshoot_le_of_monotone (H := fun _ => ⌊V⌋ + 1) monotone_const 0 n K)
  rintro w ⟨hn, i, hi, hin, h1, -, h3⟩
  refine ⟨hn, i, by omega, hin, fun j _ hj => ?_, h3⟩
  have hpre : Word.valSum (w.take j) ≤ Word.valSum (w.take (i - 1)) :=
    Word.valSum_le_of_isPrefix (List.take_prefix_take_left (by omega))
  have hle : (((Word.valSum (w.take j) : ℕ) : ℤ) : ℝ) ≤ V :=
    le_trans (by exact_mod_cast hpre) h1
  have := Int.le_floor.2 hle
  omega

/-- The words `w ∈ ℤ_{≥1}^n` with some `1 ≤ i ≤ n` such that
`A(w_{≤ i-1}) ≤ mxLevel n < A(w_{≤ i})` and `⌊mxLevel n⌋ + 1 + ⌈(9/8) log₂ n⌉ < A(w_{≤ i})` have
geometric mass at most `(1/2) n^{-9/8}`. -/
@[collatz_pos_dens "lem_mx_overshoot_tail"]
theorem geomMass_mxOvershootTail_le (n : ℕ) :
    geomMass {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
      (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
      mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
      ⌊mxLevel n⌋ + 1 + ⌈(9 / 8 : ℝ) * Real.logb 2 n⌉ < (Word.valSum (w.take i) : ℤ)} ≤
      ENNReal.ofReal (1 / 2 * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine le_of_eq_of_le ?_ zero_le
    rw [← geomMass_empty]
    congr 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨i, hi, hi0, -⟩
    omega
  set c : ℝ := (9 / 8 : ℝ) * Real.logb 2 n with hc
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc0 : 0 ≤ c := mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) hn')
  set K : ℕ := ⌈c⌉.toNat with hK
  have hKc : (K : ℤ) = ⌈c⌉ := Int.toNat_of_nonneg (Int.ceil_nonneg hc0)
  calc _ ≤ (2⁻¹ : ℝ≥0∞) ^ (K + 1) := by
        rw [← hKc]; exact geomMass_mxOvershootTail_le_two_inv_pow n (mxLevel n) K
    _ = ENNReal.ofReal ((2⁻¹ : ℝ) ^ (K + 1)) := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal (1 / 2 * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        have hcK : c ≤ (K : ℝ) := by
          have := Int.le_ceil c
          rw [← hKc] at this
          exact_mod_cast this
        have hpow : (n : ℝ) ^ (-(9 / 8 : ℝ)) = (2 : ℝ) ^ (-c) := by
          rw [hc, show -((9 / 8 : ℝ) * Real.logb 2 n) = Real.logb 2 n * (-(9 / 8 : ℝ)) by ring,
            Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
              (by positivity)]
        have hK2 : (2⁻¹ : ℝ) ^ K = (2 : ℝ) ^ (-(K : ℝ)) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
        rw [hpow, pow_succ, hK2]
        have : (2 : ℝ) ^ (-(K : ℝ)) ≤ (2 : ℝ) ^ (-c) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        linarith

end CollatzPosDens
