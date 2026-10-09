/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.D1
public import CollatzPosDens.Transfer.Dbad
public import CollatzPosDens.Transfer.Dcap
public import CollatzPosDens.Transfer.Dexp
public import CollatzPosDens.Transfer.Dpt
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.Lb
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.Transfer.LbValue
public import CollatzPosDens.Transfer.PBits

/-!
# The renewal threshold equals the scale threshold

The renewal threshold `D_*` is the maximum of `D_1`, `D_pt`, `D_exp`, `D_bad`, `D_sc`, `1`
and `2`. We show that this maximum is attained by the scale threshold: `D_* = D_sc`.

Since `L_B = 17484` and `2^(L_B - 1) ≤ B_*`, the scale cap satisfies
`D_cap = (B_* L_B)^2 ≥ 2^34966`, hence `D_sc > D_cap ≥ 2^34966`. Every other entry is below
`2^34966`: `D_1 < D_pt < 2^31`, `D_exp = 2^33495`, and, from `P_* < 2^17451`,
`D_bad < 2^17506`.

## Main results

* `CollatzPosDens.Dstar_eq_Dsc`: `D_* = D_sc`.
* `CollatzPosDens.two_pow_34966_le_Dsc`: `2^34966 ≤ D_sc`.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `a = 2 b` and `2^b ≤ x`, then `2^a ≤ x^2`. -/
private theorem two_pow_le_sq_of_eq {a b x : ℕ} (hab : a = b * 2) (h : 2 ^ b ≤ x) :
    2 ^ a ≤ x ^ 2 := by
  subst hab
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left h 2

/-- `2^34966 ≤ D_cap`. -/
theorem two_pow_34966_le_Dcap : 2 ^ 34966 ≤ Dcap := by
  have h := two_pow_LB_sub_one_le_Bstar
  rw [show LB - 1 = 17483 by rw [LB_eq]] at h
  rw [Dcap_def]
  exact two_pow_le_sq_of_eq (by norm_num) (h.trans (Nat.le_mul_of_pos_right _ LB_pos))

/-- `2^34966 ≤ D_sc`. -/
theorem two_pow_34966_le_Dsc : 2 ^ 34966 ≤ Dsc :=
  le_trans two_pow_34966_le_Dcap Dcap_lt_Dsc.le

/-- `(2^41 · 10241)^2 + 2^53 (P_* + 65) < 2^34966`. -/
private theorem Dbad_lt_aux :
    (2 ^ 41 * 10241) ^ 2 + 2 ^ 53 * (pStar + 65) < 2 ^ 34966 := by
  have hp := pStar_lt_two_pow.le
  calc (2 ^ 41 * 10241) ^ 2 + 2 ^ 53 * (pStar + 65)
      ≤ (2 ^ 41 * 10241) ^ 2 + 2 ^ 53 * (2 ^ 17451 + 65) := by gcongr
    _ < 2 ^ 34966 := by decide +kernel

/-- **The renewal threshold is the scale threshold.** `D_* = D_sc`. -/
@[collatz_pos_dens "lem_s02_Dstar_eq"]
theorem Dstar_eq_Dsc : Dstar = (Dsc : ℚ) := by
  have hsc : (2 : ℚ) ^ 34966 ≤ (Dsc : ℚ) := by
    have h := (Nat.cast_le (α := ℚ)).2 two_pow_34966_le_Dsc
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have hbad : (2 ^ 41 * 10241) ^ 2 + 2 ^ 53 * ((pStar : ℚ) + 65) ≤ (2 : ℚ) ^ 34966 := by
    have h := (Nat.cast_le (α := ℚ)).2 Dbad_lt_aux.le
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hexp : (2 : ℚ) ^ 33495 ≤ (2 : ℚ) ^ 34966 :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h31 : (2 : ℚ) ^ 31 ≤ (2 : ℚ) ^ 34966 :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hpt := Dpt_lt
  rw [← Dexp_cast (R := ℚ)] at hexp
  rw [← Dbad_eq] at hbad
  generalize (2 : ℚ) ^ 34966 = X at hsc hbad hexp h31
  refine le_antisymm (Dstar_le_iff.2 ⟨?_, ?_, ?_, ?_, le_rfl, ?_, ?_⟩) Dsc_le_Dstar <;>
    linarith [D1_lt_Dpt, show (2 : ℚ) ≤ 2 ^ 31 by norm_num]

end CollatzPosDens
