/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.Concentration
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.Mixing.MxRootVsLog

/-!
# Tail bound for the valuation sum of a prefix

Let `n ≥ 2^131072` and `t ≤ n`. Among the words `w ∈ ℤ_{≥1}^n`, those whose
prefix `w_{≤t}` has valuation sum deviating from `2t` by at least `½ n^{2049/4096}` have
geometric mass `𝐩({w : |A(w_{≤t}) - 2t| ≥ ½ n^{2049/4096}}) ≤ 2 n^{-10}`.

By `geomMass_setOf_take_mem` the mass equals that of the deviation event
`{u ∈ ℤ_{≥1}^t : |A(u) - 2t| ≥ v}` with `v = ½ n^{2049/4096}`, which
`geomMass_abs_valSum_sub_ge_le` bounds by `2 exp (-min {v²/(32t), v/8})`. Both terms of the
minimum exceed `10 log n`: `v²/(32t) ≥ v²/(32n) = n^{1/2048}/128 > 10 log n` because
`1280 log n < n^{1/2048}`, and `v/8 = n^{2049/4096}/16 ≥ n^{1/2048}/128`.

## Main results

* `CollatzPosDens.geomMass_abs_valSum_take_sub_ge_le`: the tail bound.

## Implementation notes

The prefix `w_{≤t}` is `w.take t`, and the bound `2 n^{-10}` is written
`ENNReal.ofReal (2 * n ^ (-10))` with a real power. No hypothesis `t ≥ 1` is needed: for
`t = 0` the event is empty. The comparison `v/8 ≥ v²/(32n)` is made directly from
`n^{2049/4096} ≥ n^{1/2048}`.

## References

* [Mazur, *Collatz positive density*], §13.5.
-/

@[expose] public section

open Real

namespace CollatzPosDens

/-- The exponent estimate behind the tail bound: for `n ≥ 2^131072`, `1 ≤ t ≤ n` and
`v = ½ n^{2049/4096}`, `10 log n ≤ min (v²/(32t)) (v/8)`. -/
private lemma geomMass_abs_valSum_take_sub_ge_le_exponent {n t : ℕ}
    (hn : (2 : ℝ) ^ 131072 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n) :
    10 * Real.log n ≤ min (((1 / 2 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096)) ^ 2 / (32 * t))
      ((1 / 2 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) / 8) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (one_le_pow₀ (by norm_num)) hn
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hroot := mul_log_lt_rpow_of_two_pow_131072_le hn
  set y := (n : ℝ) ^ ((2049 : ℝ) / 4096) with hy
  set z := (n : ℝ) ^ ((1 : ℝ) / 2048) with hz
  have hsq : y ^ 2 = n * z := by
    rw [hy, hz, sq, ← Real.rpow_add hn0, ← Real.rpow_one_add' hn0.le (by norm_num)]
    norm_num
  have hzy : z ≤ y := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hz0 : 0 < z := Real.rpow_pos_of_pos hn0 _
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (by positivity)]
    have : 10 * Real.log n * (32 * t) ≤ 10 * Real.log n * (32 * n) := by
      have := Real.log_nonneg hn1
      gcongr
    nlinarith
  · nlinarith

/-- **Tail bound for the valuation sum of a prefix.** For `n ≥ 2^131072` and `t ≤ n`,
`𝐩({w ∈ ℤ_{≥1}^n : |A(w_{≤t}) - 2t| ≥ ½ n^{2049/4096}}) ≤ 2 n^{-10}`. -/
@[collatz_pos_dens "lem_mx_probe_tail"]
theorem geomMass_abs_valSum_take_sub_ge_le {n t : ℕ} (hn : (2 : ℝ) ^ 131072 ≤ n)
    (htn : t ≤ n) :
    geomMass {w : Word | w.length = n ∧
        (1 / 2 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) ≤
          |(Word.valSum (w.take t) : ℝ) - 2 * t|} ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ (-10 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  set v := (1 / 2 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) with hv
  have hv0 : 0 < v := by positivity
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine (geomMass_mono (V := ∅) ?_).trans (by simp)
    rintro w ⟨-, h⟩
    simp at h
    linarith
  have hset : {w : Word | w.length = n ∧ v ≤ |(Word.valSum (w.take t) : ℝ) - 2 * t|} =
      {w : Word | w.length = n ∧ w.take t ∈
        {u : Word | u.length = t ∧ v ≤ |(u.valSum : ℝ) - 2 * t|}} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun ⟨hw, h⟩ => ⟨hw, by simp [hw, htn], h⟩, fun ⟨hw, _, h⟩ => ⟨hw, h⟩⟩
  rw [hset, geomMass_setOf_take_mem htn (fun u hu => hu.1)]
  refine (geomMass_abs_valSum_sub_ge_le t v hv0.le).trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp := geomMass_abs_valSum_take_sub_ge_le_exponent hn ht htn
  rw [← hv] at hexp
  have : Real.exp (-min (v ^ 2 / (32 * t)) (v / 8)) ≤ (n : ℝ) ^ (-10 : ℝ) := by
    rw [Real.rpow_def_of_pos hn0]
    exact Real.exp_le_exp.2 (by linarith)
  linarith

end CollatzPosDens
