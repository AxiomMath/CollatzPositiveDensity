/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxOffsetMoment

/-!
# Large offsets are rare

For every integer `n ≥ 2^{131072}`, the words `w ∈ ℤ_{≥1}^n` whose offset exceeds
`n^{4609/4096}` have geometric mass at most `(1/3) n^{-9/8}`:
$$\mathbf{p}\bigl(\{w \in \mathbb{Z}_{\ge 1}^n : \operatorname{off}(w) > n^{4609/4096}\}\bigr)
  \le \tfrac13 n^{-9/8}.$$

The proof is Markov's inequality for the fractional moment of the offset: with
`σ = 65535/65536` and `e = (4609/4096) σ`, every word in the set satisfies
`1 < off(w)^σ n^{-e}`, so its mass is less than `2^{20} n^{-e}` by the moment bound. Since
`e - 9/8 = 60927 / 2^{28}` and `n^{60927/2^{28}} ≥ 2^{60927/2048} ≥ 2^{22}`, the mass is at most
`(1/4) n^{-9/8}`.

## Main results

* `CollatzPosDens.geomMass_offsetTail_le`: the tail bound.

## Implementation notes

The mass is the geometric mass `geomMass` in `ℝ≥0∞`, and the bound `(1/3) n^{-9/8}` is the
real number embedded by `ENNReal.ofReal`. The comparison `off(w) > n^{4609/4096}` is made in `ℝ`,
with the offset cast from `ℚ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For `n ≥ 2^{131072}`,
`2^{20} n^{-(4609/4096)(65535/65536)} ≤ (1/3) n^{-9/8}`. -/
private lemma offsetTail_numeric {n : ℝ} (hn : (2 : ℝ) ^ (131072 : ℕ) ≤ n) :
    2 ^ 20 * n ^ (-((4609 / 4096 : ℝ) * (65535 / 65536))) ≤ 1 / 3 * n ^ (-(9 / 8 : ℝ)) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (131072 : ℕ) := by positivity
  have hn0 : 0 < n := h2.trans_le hn
  have hsplit : n ^ (-((4609 / 4096 : ℝ) * (65535 / 65536))) =
      n ^ (-(9 / 8 : ℝ)) * (n ^ (60927 / 2 ^ 28 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
    norm_num
  have hbig : (2 : ℝ) ^ (22 : ℝ) ≤ n ^ (60927 / 2 ^ 28 : ℝ) := by
    calc (2 : ℝ) ^ (22 : ℝ) ≤ (2 : ℝ) ^ ((131072 : ℕ) * (60927 / 2 ^ 28 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = ((2 : ℝ) ^ (131072 : ℕ)) ^ (60927 / 2 ^ 28 : ℝ) := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ n ^ (60927 / 2 ^ 28 : ℝ) := Real.rpow_le_rpow h2.le hn (by norm_num)
  have h22 : (2 : ℝ) ^ (22 : ℝ) = 2 ^ 22 := by norm_num
  rw [h22] at hbig
  have hp : 0 < n ^ (60927 / 2 ^ 28 : ℝ) := by positivity
  have hq : 0 < n ^ (-(9 / 8 : ℝ)) := by positivity
  rw [hsplit]
  have hinv : (n ^ (60927 / 2 ^ 28 : ℝ))⁻¹ ≤ 1 / 2 ^ 22 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hbig
  calc (2 : ℝ) ^ 20 * (n ^ (-(9 / 8 : ℝ)) * (n ^ (60927 / 2 ^ 28 : ℝ))⁻¹)
      ≤ 2 ^ 20 * (n ^ (-(9 / 8 : ℝ)) * (1 / 2 ^ 22)) := by gcongr
    _ ≤ 1 / 3 * n ^ (-(9 / 8 : ℝ)) := by nlinarith

/-- **Large offsets are rare.** For every integer `n ≥ 2^{131072}`,
`𝐩({w ∈ ℤ_{≥1}^n : off(w) > n^{4609/4096}}) ≤ (1/3) n^{-9/8}`. -/
@[collatz_pos_dens "lem_mx_offset_tail"]
theorem geomMass_offsetTail_le (n : ℕ) (hn : 2 ^ 131072 ≤ n) :
    geomMass {w : Word | w.length = n ∧ (n : ℝ) ^ (4609 / 4096 : ℝ) < (off w : ℝ)} ≤
      ENNReal.ofReal (1 / 3 * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  set σ : ℝ := 65535 / 65536 with hσ
  set e : ℝ := (4609 / 4096 : ℝ) * σ with he
  have hnR : (2 : ℝ) ^ (131072 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := (by positivity : (0 : ℝ) < (2 : ℝ) ^ (131072 : ℕ)).trans_le hnR
  set c : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) ^ (-e)) with hc
  have hpt : ∀ w : Word, (n : ℝ) ^ (4609 / 4096 : ℝ) < (off w : ℝ) →
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (off w : ℝ) ^ σ * c := by
    intro w hw
    have hoff0 : (0 : ℝ) ≤ off w := by exact_mod_cast off_nonneg w
    rw [hc, ENNReal.ofReal_rpow_of_nonneg hoff0 (by norm_num [hσ]),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlt : ((n : ℝ) ^ (4609 / 4096 : ℝ)) ^ σ ≤ (off w : ℝ) ^ σ :=
      Real.rpow_le_rpow (by positivity) hw.le (by norm_num [hσ])
    rw [← Real.rpow_mul hn0.le, ← he] at hlt
    calc (1 : ℝ) = (n : ℝ) ^ e * (n : ℝ) ^ (-e) := by
          rw [← Real.rpow_add hn0]; simp
      _ ≤ (off w : ℝ) ^ σ * (n : ℝ) ^ (-e) := by gcongr
  calc geomMass {w : Word | w.length = n ∧ (n : ℝ) ^ (4609 / 4096 : ℝ) < (off w : ℝ)}
      ≤ ∑' w : {w : Word | w.length = n ∧ (n : ℝ) ^ (4609 / 4096 : ℝ) < (off w : ℝ)},
          (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ * c := by
        rw [geomMass_def]
        refine ENNReal.tsum_le_tsum fun w => ?_
        rw [mul_assoc]
        exact le_mul_of_one_le_right' (hpt w w.2.2)
    _ ≤ ∑' w : {w : Word | w.length = n},
          (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ * c :=
        ENNReal.tsum_mono_subtype
          (fun w : Word => (2⁻¹ : ℝ≥0∞) ^ w.valSum * ENNReal.ofReal (off w : ℝ) ^ σ * c)
          fun w hw => hw.1
    _ = (∑' w : {w : Word | w.length = n},
          (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ) * c :=
        ENNReal.tsum_mul_right
    _ ≤ 2 ^ 20 * c := by gcongr; exact (offsetMoment_lt n).le
    _ ≤ ENNReal.ofReal (1 / 3 * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
        rw [hc, show (2 : ℝ≥0∞) ^ 20 = ENNReal.ofReal (2 ^ 20) by
          rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat],
          ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (offsetTail_numeric hnR)

end CollatzPosDens
