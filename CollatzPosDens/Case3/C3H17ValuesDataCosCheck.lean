/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataCos
public import CollatzPosDens.Case3.C3H17ValuesDataCosTab
public import Mathlib.Tactic.IntervalCases

/-!
# Verification of the table of cosine bounds

Every lane of the table `CollatzPosDens.C3H17Values.cosLevels` is checked, by kernel
evaluation, to be the shifted cosine bound `cosI (2^v 3^J) + 10^{18}` at its point, computed
from the residue `2^v 3^J mod 2^17` by the natural-number evaluation `cosExpect`; every lane is
below `2^62` and every packed number below `2^{72 · 256}`.

Since `3^{p_v} ≡ 1 (mod 2^{17 - v})`, the cosine bound at `2^v 3^J` depends only on
`J mod p_v`.

## Main definitions

* `CollatzPosDens.C3H17Values.cosPer`: the period `p_v`.
* `CollatzPosDens.C3H17Values.cosLaneAt`: the lane of index `J` of level `v`.

## Main results

* `CollatzPosDens.C3H17Values.cosLaneAt_spec`: `cosLaneAt v J = cosI (2^v 3^J) + 10^{18}` for
  `v ≤ 16` and `J < p_v + 256`.
* `CollatzPosDens.C3H17Values.cosI_two_pow_mul_three_pow_mod`: `cosI (2^v 3^J)` depends only on
  `J mod p_v`.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The period `p_v = 2^{15 - v}` (`v ≤ 14`), `p_v = 2` (`v ≥ 15`) of `J ↦ 2^v 3^J mod 2^17`. -/
def cosPer (v : ℕ) : ℕ := if v ≤ 14 then 2 ^ (15 - v) else 2

/-- The number of packed numbers of level `v`. -/
def cosNumChunks (v : ℕ) : ℕ := (cosPer v + 511) / 256

/-- The lane of index `J` of level `v` of the table. -/
def cosLaneAt (v J : ℕ) : ℕ := lane 72 (cosChunk v (J / 256)) (J % 256)

/-- The check of the packed number of index `q` of level `v`; the residue
`2^v 3^{256 q + i} mod 2^17` is computed as `(2^v 3^{256 q} mod 2^17) 3^i mod 2^17`. -/
def cosChunkOK (v q : ℕ) : Bool :=
  Nat.blt (cosChunk v q) (2 ^ (72 * 256)) &&
    (List.range 256).all fun i =>
      Nat.ble (cosPer v + 256) (256 * q + i) ||
        (cosExpectOK ((2 ^ v * 3 ^ (256 * q) % 2 ^ 17) * 3 ^ i % 2 ^ 17) &&
          (lane 72 (cosChunk v q) i ==
            cosExpect ((2 ^ v * 3 ^ (256 * q) % 2 ^ 17) * 3 ^ i % 2 ^ 17)) &&
          Nat.blt (lane 72 (cosChunk v q) i) (2 ^ 62))

/-- `(2^v 3^{256 q} mod 2^17) 3^i mod 2^17 = 2^v 3^{256 q + i} mod 2^17`. -/
theorem cosResidue_eq (v q i : ℕ) :
    (2 ^ v * 3 ^ (256 * q) % 2 ^ 17) * 3 ^ i % 2 ^ 17 = 2 ^ v * 3 ^ (256 * q + i) % 2 ^ 17 := by
  rw [Nat.mod_mul_mod, pow_add, mul_assoc]

/-- The check of the packed numbers of indices `q₀, …, q₀ + n - 1` of level `v`. -/
def cosRangeOK (v q₀ n : ℕ) : Bool := (List.range' q₀ n).all (cosChunkOK v)

/-- The checks of two consecutive ranges of packed numbers combine into the check of their union.
-/
theorem cosRangeOK_append {v q₀ n m : ℕ} (h₁ : cosRangeOK v q₀ n = true)
    (h₂ : cosRangeOK v (q₀ + n) m = true) : cosRangeOK v q₀ (n + m) = true := by
  simp only [cosRangeOK, List.all_eq_true] at *
  intro q hq
  rw [List.mem_range'_1] at hq
  by_cases h : q < q₀ + n
  · exact h₁ q (List.mem_range'_1.2 ⟨hq.1, h⟩)
  · exact h₂ q (List.mem_range'_1.2 ⟨by omega, by omega⟩)

/-- The packed numbers of indices `0, …, 16` of level `0` pass the check. -/
theorem cosCheck_0_0 : cosRangeOK 0 0 17 = true := by decide +kernel
/-- The packed numbers of indices `17, …, 32` of level `0` pass the check. -/
theorem cosCheck_0_1 : cosRangeOK 0 17 16 = true := by decide +kernel
/-- The packed numbers of indices `33, …, 48` of level `0` pass the check. -/
theorem cosCheck_0_2 : cosRangeOK 0 33 16 = true := by decide +kernel
/-- The packed numbers of indices `49, …, 64` of level `0` pass the check. -/
theorem cosCheck_0_3 : cosRangeOK 0 49 16 = true := by decide +kernel
/-- The packed numbers of indices `65, …, 80` of level `0` pass the check. -/
theorem cosCheck_0_4 : cosRangeOK 0 65 16 = true := by decide +kernel
/-- The packed numbers of indices `81, …, 96` of level `0` pass the check. -/
theorem cosCheck_0_5 : cosRangeOK 0 81 16 = true := by decide +kernel
/-- The packed numbers of indices `97, …, 112` of level `0` pass the check. -/
theorem cosCheck_0_6 : cosRangeOK 0 97 16 = true := by decide +kernel
/-- The packed numbers of indices `113, …, 128` of level `0` pass the check. -/
theorem cosCheck_0_7 : cosRangeOK 0 113 16 = true := by decide +kernel
/-- The packed numbers of indices `0, …, 16` of level `1` pass the check. -/
theorem cosCheck_1_0 : cosRangeOK 1 0 17 = true := by decide +kernel
/-- The packed numbers of indices `17, …, 32` of level `1` pass the check. -/
theorem cosCheck_1_1 : cosRangeOK 1 17 16 = true := by decide +kernel
/-- The packed numbers of indices `33, …, 48` of level `1` pass the check. -/
theorem cosCheck_1_2 : cosRangeOK 1 33 16 = true := by decide +kernel
/-- The packed numbers of indices `49, …, 64` of level `1` pass the check. -/
theorem cosCheck_1_3 : cosRangeOK 1 49 16 = true := by decide +kernel
/-- The packed numbers of indices `0, …, 16` of level `2` pass the check. -/
theorem cosCheck_2_0 : cosRangeOK 2 0 17 = true := by decide +kernel
/-- The packed numbers of indices `17, …, 32` of level `2` pass the check. -/
theorem cosCheck_2_1 : cosRangeOK 2 17 16 = true := by decide +kernel
/-- The packed numbers of indices `0, …, 16` of level `3` pass the check. -/
theorem cosCheck_3 : cosRangeOK 3 0 17 = true := by decide +kernel
/-- The packed numbers of indices `0, …, 8` of level `4` pass the check. -/
theorem cosCheck_4 : cosRangeOK 4 0 9 = true := by decide +kernel
/-- For `5 ≤ v ≤ 16`, every packed number of level `v` passes the check. -/
theorem cosCheck_5to16 : ∀ v ∈ List.range' 5 12, cosRangeOK v 0 (cosNumChunks v) = true := by
  decide +kernel

/-- For `v ≤ 16`, every packed number of level `v` passes the check. -/
theorem cosRangeOK_all {v : ℕ} (hv : v ≤ 16) : cosRangeOK v 0 (cosNumChunks v) = true := by
  rcases (show v ≤ 4 ∨ 5 ≤ v by omega) with h | h
  · interval_cases v
    · rw [show cosNumChunks 0 = 17 + 16 + 16 + 16 + 16 + 16 + 16 + 16 by decide]
      exact cosRangeOK_append (cosRangeOK_append (cosRangeOK_append (cosRangeOK_append
        (cosRangeOK_append (cosRangeOK_append (cosRangeOK_append cosCheck_0_0 cosCheck_0_1)
          cosCheck_0_2) cosCheck_0_3) cosCheck_0_4) cosCheck_0_5) cosCheck_0_6) cosCheck_0_7
    · rw [show cosNumChunks 1 = 17 + 16 + 16 + 16 by decide]
      exact cosRangeOK_append (cosRangeOK_append (cosRangeOK_append cosCheck_1_0 cosCheck_1_1)
        cosCheck_1_2) cosCheck_1_3
    · rw [show cosNumChunks 2 = 17 + 16 by decide]
      exact cosRangeOK_append cosCheck_2_0 cosCheck_2_1
    · rw [show cosNumChunks 3 = 17 by decide]
      exact cosCheck_3
    · rw [show cosNumChunks 4 = 9 by decide]
      exact cosCheck_4
  · exact cosCheck_5to16 v (List.mem_range'_1.2 ⟨h, by omega⟩)

/-- For `v ≤ 16`, the packed number of index `q < cosNumChunks v` of level `v` passes the check.
-/
theorem cosChunkOK_of_lt {v q : ℕ} (hv : v ≤ 16) (hq : q < cosNumChunks v) :
    cosChunkOK v q = true := by
  have := cosRangeOK_all hv
  simp only [cosRangeOK, List.all_eq_true] at this
  exact this q (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)

/-- For `v ≤ 16`, the packed number of index `q < cosNumChunks v` of level `v` is below
`2^{72 · 256}`. -/
theorem cosChunk_lt {v q : ℕ} (hv : v ≤ 16) (hq : q < cosNumChunks v) :
    cosChunk v q < 2 ^ (72 * 256) := by
  have := cosChunkOK_of_lt hv hq
  simp only [cosChunkOK, Bool.and_eq_true, Nat.blt_eq] at this
  exact this.1

/-- The period `p_v` is positive. -/
theorem cosPer_pos (v : ℕ) : 0 < cosPer v := by
  unfold cosPer; split_ifs <;> positivity

/-- For `v ≤ 16` and `J < p_v + 256`, the lane of index `J` of level `v` is
`cosI (2^v 3^J) + 10^{18}` and is below `2^62`. -/
theorem cosLaneAt_spec {v J : ℕ} (hv : v ≤ 16) (hJ : J < cosPer v + 256) :
    (cosLaneAt v J : ℤ) = cosI (2 ^ v * 3 ^ J) + 10 ^ 18 ∧ cosLaneAt v J < 2 ^ 62 := by
  have hq : J / 256 < cosNumChunks v := by unfold cosNumChunks; omega
  have := cosChunkOK_of_lt hv hq
  simp only [cosChunkOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  have h := this.2 (J % 256) (Nat.mod_lt _ (by norm_num))
  rw [cosResidue_eq, show 256 * (J / 256) + J % 256 = J by omega] at h
  simp only [Bool.or_eq_true, Nat.ble_eq, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
  rcases h with h | ⟨⟨hok, heq⟩, hlt⟩
  · omega
  · refine ⟨?_, hlt⟩
    rw [cosLaneAt, heq, cosExpect_eq (Nat.mod_lt _ (by norm_num)) hok]
    congr 1
    apply cosI_of_emod_eq
    push_cast
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- `3^{p_v} ≡ 1 (mod 2^{17 - v})`. -/
theorem three_pow_cosPer : ∀ v ∈ List.range 17, (3 ^ cosPer v - 1) % 2 ^ (17 - v) = 0 := by
  decide +kernel

/-- For `v ≤ 16`, `cosI (2^v 3^J) = cosI (2^v 3^{J mod p_v})`. -/
theorem cosI_two_pow_mul_three_pow_mod {v : ℕ} (hv : v ≤ 16) (J : ℕ) :
    cosI (2 ^ v * 3 ^ J) = cosI (2 ^ v * 3 ^ (J % cosPer v)) := by
  apply cosI_of_emod_eq
  have h := three_pow_cosPer v (List.mem_range.2 (by omega))
  have hd : (2 : ℤ) ^ (17 - v) ∣ 3 ^ cosPer v - 1 := by
    have h' : ((2 : ℕ) ^ (17 - v) : ℤ) ∣ ((3 ^ cosPer v - 1 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero h)
    push_cast [Nat.one_le_pow _ _ (by norm_num : 0 < 3)] at h'
    exact h'
  have hd' : (2 : ℤ) ^ (17 - v) ∣ 3 ^ J - 3 ^ (J % cosPer v) := by
    have h3 : (3 : ℤ) ^ J = 3 ^ (J % cosPer v) * (3 ^ cosPer v) ^ (J / cosPer v) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have : (3 : ℤ) ^ J - 3 ^ (J % cosPer v) =
        3 ^ (J % cosPer v) * ((3 ^ cosPer v) ^ (J / cosPer v) - 1) := by
      rw [h3]; ring
    rw [this]
    exact dvd_mul_of_dvd_right (dvd_trans hd (sub_one_dvd_pow_sub_one _ _)) _
  have : (2 : ℤ) ^ 17 ∣ 2 ^ v * 3 ^ J - 2 ^ v * 3 ^ (J % cosPer v) := by
    rw [← mul_sub, show (2 : ℤ) ^ 17 = 2 ^ v * 2 ^ (17 - v) by rw [← pow_add]; congr 1; omega]
    exact mul_dvd_mul_left _ hd'
  push_cast
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd this)

end C3H17Values

end CollatzPosDens
