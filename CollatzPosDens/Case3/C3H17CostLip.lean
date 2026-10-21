/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Cost
public import CollatzPosDens.Case3.C3H17Lip
public import CollatzPosDens.Case3.C3H17CostRange
public import CollatzPosDens.Case3.C3CapRange
public import CollatzPosDens.StoppingTrace.TrCapLipschitz

/-!
# The future costs are Lipschitz

For every integer `h` and all reals `z, z'`, the future cost `cf_h` (`CollatzPosDens.c3H17Cost`)
satisfies `|cf_h(z) - cf_h(z')| ≤ 𝖫_h |z - z'|`, where `𝖫_h` is the rational constant
`CollatzPosDens.c3H17Lip`.

The proof is by downward induction on `h`; for `h ≥ 15` both sides vanish. For `h ≤ 14`,
`cf_h(z) - cf_h(z') = ∑_{d=2}^{17-h} ϖ(d) [Φ_d G_d - Φ'_d G'_d]` with
`Φ_d = Φ^cap_d(z / 2^{h+d})`, `Φ'_d = Φ^cap_d(z' / 2^{h+d})` and `G_d, G'_d` the second factors.
All four lie in `[0, 1]`, so `|Φ_d G_d - Φ'_d G'_d| ≤ |Φ_d - Φ'_d| + |G_d - G'_d|`. The capped
factor is `ℓ_d`-Lipschitz, which bounds the first term by `ℓ_d 2^{-h-d} |z - z'|`, and `ℓ_2 = 0`.
If `d ∉ {4, 5}` and `h + d ≤ 15` the induction hypothesis bounds the second term by
`9 𝖫_{h+d} |z - z'|`; otherwise `G_d = G'_d = 1`. Summing with the weights `ϖ(d) ≥ 0` gives
`𝖫_h |z - z'|`.

## Main results

* `CollatzPosDens.abs_c3H17Cost_sub_le`: `|cf_h(z) - cf_h(z')| ≤ 𝖫_h |z - z'|`.

## Implementation notes

The bound is stated for every integer `h`, not only for `h ≥ 1`; the proof uses no lower bound
on `h`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The future costs are Lipschitz: `|cf_h(z) - cf_h(z')| ≤ 𝖫_h |z - z'|`. -/
@[collatz_pos_dens "lem_c3_h17_cost_lip"]
theorem abs_c3H17Cost_sub_le (h : ℤ) (z z' : ℝ) :
    |c3H17Cost h z - c3H17Cost h z'| ≤ (c3H17Lip h : ℝ) * |z - z'| := by
  induction hn : (15 - h).toNat using Nat.strong_induction_on generalizing h z z' with
  | _ n ih =>
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Cost_of_le hh, c3H17Cost_of_le hh, c3H17Lip_of_le hh]
    simp
  rw [c3H17Cost_of_lt hh, c3H17Cost_of_lt hh, c3H17Lip_cast_of_lt hh]
  set s := Finset.Icc (2 : ℤ) (17 - h)
  set P : ℤ → Prop := fun d => d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 with hP
  set G : ℤ → ℝ → ℝ := fun d w => if P d then c3H17Cost (h + d) (9 * w) else 1 with hG
  set A : ℤ → ℝ := fun d => varpi d * trLipConst d * (2 : ℝ) ^ (-d) * ((2 : ℝ) ^ (-h) * |z - z'|)
    with hA
  set B : ℤ → ℝ := fun d => if P d then varpi d * c3H17Lip (h + d) * (9 * |z - z'|) else 0
    with hB
  have hterm : ∀ d ∈ s,
      |varpi d * (1 - trCapFactor d (z / (2 : ℝ) ^ (h + d)) * G d z) -
        varpi d * (1 - trCapFactor d (z' / (2 : ℝ) ^ (h + d)) * G d z')| ≤ A d + B d := by
    intro d hd
    have hds := Finset.mem_Icc.mp hd
    have hw := varpi_nonneg d
    have hGI : ∀ w, G d w ∈ Set.Icc (0 : ℝ) 1 := by
      intro w
      simp only [hG]
      split_ifs
      · exact c3H17Cost_mem_Icc _ _
      · exact ⟨zero_le_one, le_rfl⟩
    have hGL : |G d z - G d z'| ≤ if P d then c3H17Lip (h + d) * (9 * |z - z'|) else 0 := by
      simp only [hG]
      split_ifs with hc
      · have := ih (15 - (h + d)).toNat (by simp only [hP] at hc; omega) (h + d) (9 * z) (9 * z')
          rfl
        rwa [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)] at this
      · simp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (h + d) := zpow_pos (by norm_num) _
    have hΦL : |trCapFactor d (z / (2 : ℝ) ^ (h + d)) - trCapFactor d (z' / (2 : ℝ) ^ (h + d))| ≤
        trLipConst d * (2 : ℝ) ^ (-d) * ((2 : ℝ) ^ (-h) * |z - z'|) := by
      refine (abs_trCapFactor_sub_le d _ _).trans (le_of_eq ?_)
      rw [← sub_div, abs_div, abs_of_pos hpos, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg,
        zpow_neg]
      field_simp
    obtain ⟨hΦ0, hΦ1⟩ := trCapFactor_mem_Icc d (z / (2 : ℝ) ^ (h + d))
    obtain ⟨hΦ0', hΦ1'⟩ := trCapFactor_mem_Icc d (z' / (2 : ℝ) ^ (h + d))
    obtain ⟨hG0, hG1⟩ := hGI z
    obtain ⟨hG0', hG1'⟩ := hGI z'
    set a := trCapFactor d (z / (2 : ℝ) ^ (h + d))
    set a' := trCapFactor d (z' / (2 : ℝ) ^ (h + d))
    set b := G d z
    set b' := G d z'
    have hprod : |a * b - a' * b'| ≤ |a - a'| + |b - b'| := by
      have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hG0]
        exact mul_le_of_le_one_right (abs_nonneg _) hG1
      · rw [abs_mul, abs_of_nonneg hΦ0']
        exact mul_le_of_le_one_left (abs_nonneg _) hΦ1'
    have e : varpi d * (1 - a * b) - varpi d * (1 - a' * b') = varpi d * (a' * b' - a * b) := by
      ring
    rw [e, abs_mul, abs_of_nonneg hw, abs_sub_comm]
    calc varpi d * |a * b - a' * b'| ≤ varpi d * (|a - a'| + |b - b'|) :=
          mul_le_mul_of_nonneg_left hprod hw
      _ ≤ varpi d * (trLipConst d * (2 : ℝ) ^ (-d) * ((2 : ℝ) ^ (-h) * |z - z'|) +
            if P d then c3H17Lip (h + d) * (9 * |z - z'|) else 0) :=
          mul_le_mul_of_nonneg_left (add_le_add hΦL hGL) hw
      _ = A d + B d := by
          simp only [hA, hB]
          split_ifs <;> ring
  have hsum : |(1 - ∑ d ∈ s, varpi d * (1 - trCapFactor d (z / (2 : ℝ) ^ (h + d)) * G d z)) -
      (1 - ∑ d ∈ s, varpi d * (1 - trCapFactor d (z' / (2 : ℝ) ^ (h + d)) * G d z'))| ≤
      ∑ d ∈ s, A d + ∑ d ∈ s, B d := by
    rw [sub_sub_sub_cancel_left, abs_sub_comm, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  refine hsum.trans (le_of_eq ?_)
  have hAs : ∑ d ∈ s, A d = (2 : ℝ) ^ (-h) * ∑ d ∈ Finset.Icc (3 : ℤ) (17 - h),
      varpi d * trLipConst d * (2 : ℝ) ^ (-d) * |z - z'| := by
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_subset (fun d hd => ?_) (fun d hd hd' => ?_) |>.trans
      (Finset.sum_congr rfl fun d _ => by simp only [hA]; ring)
    · simp only [s, Finset.mem_Icc] at hd ⊢
      omega
    · simp only [s, Finset.mem_Icc] at hd hd'
      rw [trLipConst_of_not_mem (by omega)]
      simp
  have hBs : ∑ d ∈ s, B d = 9 * ∑ d ∈ (Finset.Icc (2 : ℤ) (15 - h)).filter
      (· ∉ ({4, 5} : Finset ℤ)), varpi d * c3H17Lip (h + d) * |z - z'| := by
    simp only [hB]
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun d _ => by ring
    ext d
    simp only [s, hP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hAs, hBs, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

end CollatzPosDens
