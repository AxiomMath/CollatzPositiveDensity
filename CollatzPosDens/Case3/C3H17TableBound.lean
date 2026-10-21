/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CapRange
public import CollatzPosDens.Case3.C3H17CapUpBound
public import CollatzPosDens.Case3.C3H17CostLip
public import CollatzPosDens.Case3.C3H17CostRange
public import CollatzPosDens.Case3.C3H17FirstCost
public import CollatzPosDens.Case3.C3H17NodeUpper
public import CollatzPosDens.Case3.C3H17Table
public import CollatzPosDens.Case3.C3NarrowFactor
public import CollatzPosDens.StoppingTrace.TrCapLipschitz

/-!
# The cost table bounds the crossing cost on whole cells

Let `c ≤ 16` and `1 ≤ o` be integers, `m` an odd integer and `β` a real number with
`|β| ≤ 10^{-6}`. Then the crossing cost satisfies `xc_{c,o}(m + β) ≤ ct_{c,o}(m)`.

Put `x = m + β`. Both factors of `xc_{c,o}` lie in `[0, 1]`, so `xc_{c,o}(x)` is at most `1` and at
most `Φ^cap_c(x / 2^o)`. Each candidate value entering `c3H17Table` then bounds `xc_{c,o}(x)`:

* the *packet value* (`c ≥ 3`), by the narrow-factor bound `Φ^cap_c(x / 2^o) ≤ 1 - δ'_{c,o}`;
* the *direct value* (`c ≥ 3`), by the Lipschitz bound
  `Φ^cap_c(x / 2^o) ≤ Φ^cap_c(m / 2^o) + 10^{-6} ℓ_c 2^{-o}` and the grid majorant `Ū_c`;
* the *joint value* (`c ∉ {4, 5}`), since for `a, a', b, b' ∈ [0, 1]` one has
  `ab - a'b' ≤ |a - a'| + |b - b'|`, together with the Lipschitz bounds of both factors and the
  majorants `Ū_c` and `cf⁺_o`.

Rounding up on the mesh `10^{-8}` only increases each bound.

## Main results

* `CollatzPosDens.c3H17FirstCost_le_c3H17Table`: `xc_{c,o}(m + β) ≤ ct_{c,o}(m)`.

## Implementation notes

The statement is usually given under `2 ≤ c ≤ 16` and `1 ≤ o ≤ c`. The bounds `2 ≤ c` and
`o ≤ c` are not used and are dropped; `c ≤ 16` and `1 ≤ o` are needed only for the packet value.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Rounding up on the mesh `10^{-8}` does not decrease a rational. -/
private theorem cast_le_ceil_div (q : ℚ) :
    (q : ℝ) ≤ (((⌈(10 ^ 8 : ℚ) * q⌉ : ℚ) / 10 ^ 8 : ℚ) : ℝ) := by
  have : q ≤ (⌈(10 ^ 8 : ℚ) * q⌉ : ℚ) / 10 ^ 8 := by
    rw [le_div_iff₀ (by norm_num), mul_comm]
    exact Int.le_ceil _
  exact_mod_cast this

/-- For `a, a', b, b' ∈ [0, 1]`, `ab ≤ a'b' + |a - a'| + |b - b'|`. -/
private theorem mul_le_mul_add_abs {a a' b b' : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (ha' : a' ∈ Set.Icc (0 : ℝ) 1) :
    a * b ≤ a' * b' + |a - a'| + |b - b'| := by
  have h₁ : (a - a') * b ≤ |a - a'| := by
    calc (a - a') * b ≤ |a - a'| * b := mul_le_mul_of_nonneg_right (le_abs_self _) hb.1
      _ ≤ |a - a'| * 1 := mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
      _ = |a - a'| := mul_one _
  have h₂ : a' * (b - b') ≤ |b - b'| := by
    calc a' * (b - b') ≤ a' * |b - b'| := mul_le_mul_of_nonneg_left (le_abs_self _) ha'.1
      _ ≤ 1 * |b - b'| := mul_le_mul_of_nonneg_right ha'.2 (abs_nonneg _)
      _ = |b - b'| := one_mul _
  nlinarith

/-- **The cost table bounds the crossing cost on whole cells.** Let `c ≤ 16` and `1 ≤ o` be
integers, `m` an odd integer and `β` a real number with `|β| ≤ 10^{-6}`. Then
`xc_{c,o}(m + β) ≤ ct_{c,o}(m)`. -/
@[collatz_pos_dens "lem_c3_h17_table_bound"]
theorem c3H17FirstCost_le_c3H17Table {c o : ℤ} (hc : c ≤ 16) (ho : 1 ≤ o) {m : ℤ} (hm : Odd m)
    {β : ℝ} (hβ : |β| ≤ 1 / 10 ^ 6) :
    c3H17FirstCost c o (m + β) ≤ c3H17Table c o m := by
  set x : ℝ := m + β with hx
  have h2o : (0 : ℝ) < (2 : ℝ) ^ o := zpow_pos (by norm_num) o
  have hA := trCapFactor_mem_Icc c (x / (2 : ℝ) ^ o)
  have hA' := trCapFactor_mem_Icc c ((m : ℝ) / (2 : ℝ) ^ o)
  have hB := c3H17Cost_mem_Icc o (9 * x)
  have hxa : c3H17FirstCost c o x ≤ trCapFactor c (x / (2 : ℝ) ^ o) := by
    unfold c3H17FirstCost
    split_ifs
    · exact le_rfl
    · exact mul_le_of_le_one_right hA.1 hB.2
  have hx1 : c3H17FirstCost c o x ≤ 1 := hxa.trans hA.2
  have hU : trCapFactor c ((m : ℝ) / (2 : ℝ) ^ o) ≤ (c3H17CapUp c ((m : ℚ) / 2 ^ o) : ℝ) := by
    have := trCapFactor_le_c3H17CapUp c ((m : ℚ) / 2 ^ o)
    push_cast at this
    exact this
  have hθ : |x / (2 : ℝ) ^ o - (m : ℝ) / (2 : ℝ) ^ o| ≤ (10 ^ 6 : ℝ)⁻¹ * (2 : ℝ) ^ (-o) := by
    rw [← sub_div, hx, add_sub_cancel_left, abs_div, abs_of_pos h2o, zpow_neg, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 h2o.le)
    simpa [one_div] using hβ
  have hℓ0 : (0 : ℝ) ≤ trLipConst c := by exact_mod_cast trLipConst_nonneg c
  have hLa : |trCapFactor c (x / (2 : ℝ) ^ o) - trCapFactor c ((m : ℝ) / (2 : ℝ) ^ o)| ≤
      (10 ^ 6 : ℝ)⁻¹ * ((trLipConst c : ℝ) * (2 : ℝ) ^ (-o)) := by
    refine (abs_trCapFactor_sub_le c _ _).trans ?_
    calc (trLipConst c : ℝ) * |x / (2 : ℝ) ^ o - (m : ℝ) / (2 : ℝ) ^ o|
        ≤ (trLipConst c : ℝ) * ((10 ^ 6 : ℝ)⁻¹ * (2 : ℝ) ^ (-o)) :=
          mul_le_mul_of_nonneg_left hθ hℓ0
      _ = (10 ^ 6 : ℝ)⁻¹ * ((trLipConst c : ℝ) * (2 : ℝ) ^ (-o)) := by ring
  have hLb : |c3H17Cost o (9 * x) - c3H17Cost o (9 * (m : ℝ))| ≤
      (10 ^ 6 : ℝ)⁻¹ * (9 * (c3H17Lip o : ℝ)) := by
    refine (abs_c3H17Cost_sub_le o _ _).trans ?_
    have hL0 : (0 : ℝ) ≤ c3H17Lip o := by exact_mod_cast c3H17Lip_nonneg o
    have : |9 * x - 9 * (m : ℝ)| ≤ 9 * (10 ^ 6 : ℝ)⁻¹ := by
      rw [← mul_sub, hx, add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
      have : |β| ≤ (10 ^ 6 : ℝ)⁻¹ := by simpa [one_div] using hβ
      linarith
    calc (c3H17Lip o : ℝ) * |9 * x - 9 * (m : ℝ)| ≤ (c3H17Lip o : ℝ) * (9 * (10 ^ 6 : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left this hL0
      _ = (10 ^ 6 : ℝ)⁻¹ * (9 * (c3H17Lip o : ℝ)) := by ring
  have hpacket : 3 ≤ c → c3H17FirstCost c o x ≤ ((1 - c3NarrowDeficit c o : ℚ) : ℝ) := by
    intro h3
    refine hxa.trans ?_
    push_cast
    exact trCapFactor_le_one_sub_c3NarrowDeficit h3 hc ho hm hβ
  have hdirect : c3H17FirstCost c o x ≤ ((c3H17CapUp c ((m : ℚ) / 2 ^ o) +
      (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o)))⌉ : ℚ) / 10 ^ 8 : ℚ) : ℝ) := by
    have hc := cast_le_ceil_div ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o)))
    push_cast at hc ⊢
    have := (abs_le.1 hLa).2
    linarith
  have hjoint : c ∉ ({4, 5} : Finset ℤ) → c3H17FirstCost c o x ≤
      (((⌈(10 ^ 8 : ℚ) * (c3H17CapUp c ((m : ℚ) / 2 ^ o) * c3H17Node o (9 * m))⌉ : ℚ) / 10 ^ 8 +
        (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o) + 9 * c3H17Lip o))⌉ : ℚ) /
          10 ^ 8 : ℚ) : ℝ) := by
    intro h45
    rw [c3H17FirstCost_of_not_mem h45]
    have hG : c3H17Cost o (9 * (m : ℝ)) ≤ (c3H17Node o (9 * m) : ℝ) := by
      have := c3H17Cost_le_c3H17Node o (9 * m)
      push_cast at this
      exact this
    have hB' := c3H17Cost_mem_Icc o (9 * (m : ℝ))
    have hcentre : trCapFactor c ((m : ℝ) / (2 : ℝ) ^ o) * c3H17Cost o (9 * (m : ℝ)) ≤
        (c3H17CapUp c ((m : ℚ) / 2 ^ o) : ℝ) * (c3H17Node o (9 * m) : ℝ) :=
      mul_le_mul hU hG hB'.1 (by exact_mod_cast c3H17CapUp_nonneg c _)
    have hmain := mul_le_mul_add_abs (a := trCapFactor c (x / (2 : ℝ) ^ o))
      (b' := c3H17Cost o (9 * (m : ℝ))) hB hA'
    have hc₁ := cast_le_ceil_div (c3H17CapUp c ((m : ℚ) / 2 ^ o) * c3H17Node o (9 * m))
    have hc₂ := cast_le_ceil_div ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o) + 9 * c3H17Lip o))
    push_cast at hc₁ hc₂ ⊢
    linarith
  unfold c3H17Table
  rw [Rat.cast_min, Rat.cast_min]
  refine le_min (le_min (by exact_mod_cast hx1) ?_) ?_
  · split_ifs with h3
    · rw [Rat.cast_min]
      exact le_min (hpacket h3) hdirect
    · exact_mod_cast hx1
  · by_cases h45 : c ∈ ({4, 5} : Finset ℤ)
    · rw [ite_eq_right (not_not_intro h45)]
      exact_mod_cast hx1
    · rw [ite_eq_left h45]
      exact hjoint h45

end CollatzPosDens
