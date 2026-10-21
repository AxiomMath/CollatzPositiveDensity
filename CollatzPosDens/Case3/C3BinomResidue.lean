/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Binomial residue classes

For `n : ℕ`, an integer `m ≥ 2` and an integer `a`, the probability that a
`Binomial(n, 1/2)` variable lies in the residue class of `a` modulo `m` is within
`exp (-2 n / m ^ 2)` of `1 / m`:
`|∑_{0 ≤ k ≤ n, k ≡ a (mod m)} C(n, k) 2⁻ⁿ - 1 / m| ≤ exp (-2 n / m ^ 2)`.

The proof is by discrete Fourier analysis. With `ζ = exp (2 π i / m)`, the indicator of
`k ≡ a (mod m)` is `(1 / m) ∑_{t < m} ζ ^ (t (k - a))`, so by the binomial theorem the sum
equals `(1 / m) ∑_{t < m} ζ ^ (-t a) ((1 + ζ ^ t) / 2) ^ n`, whose `t = 0` term is `1 / m`.
For `1 ≤ t < m`, `|(1 + ζ ^ t) / 2| = |cos (π t / m)|`, and Jordan's inequality
`sin x ≥ 2 x / π` on `[0, π / 2]` (applied to `π t / m` or `π - π t / m`) gives
`sin ^ 2 (π t / m) ≥ 4 / m ^ 2`, so `cos ^ 2 (π t / m) ≤ 1 - 4 / m ^ 2 ≤ exp (-4 / m ^ 2)`.
The triangle inequality bounds the deviation by `(m - 1) / m · exp (-2 n / m ^ 2)`.

## Main results

* `CollatzPosDens.abs_sum_choose_filter_modEq_div_sub_inv_le`: the residue-class bound.

## Implementation notes

The bound `|cos (π t / m)| ≤ exp (-2 / m ^ 2)` is obtained from
`cos ^ 2 = 1 - sin ^ 2` and Jordan's inequality directly, rather than through the
intermediate inequality `|cos (π t / m)| ≤ cos (π / m) ≤ 1 - 2 / m ^ 2`; the resulting
estimate is the same.

## References

* [Mazur, *Collatz positive density*, §10.1]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Finset Real

/-- For `1 ≤ t < m`, the Fourier coefficient `(1 + ζ ^ t) / 2` of the fair coin, with
`ζ = exp (2 π i / m)`, has norm at most `exp (-2 / m ^ 2)`. -/
theorem norm_one_add_exp_pow_div_two_le {m t : ℕ} (ht1 : 1 ≤ t) (ht2 : t < m) :
    ‖(1 + cexp (2 * π * I / m) ^ t) / 2‖ ≤ Real.exp (-2 / (m : ℝ) ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set x : ℝ := π * t / m with hx
  have key : (1 + cexp (2 * π * I / m) ^ t) / 2 = cexp (x * I) * Complex.cos x := by
    rw [← Complex.exp_nat_mul, Complex.cos]
    have h1 : (t : ℂ) * (2 * π * I / m) = 2 * (x * I) := by
      rw [hx]; push_cast; field_simp
    have h3 : cexp (-(x : ℂ) * I) * cexp (x * I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [h1, two_mul, Complex.exp_add]
    linear_combination (-1 / 2 : ℂ) * h3
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.ofReal_cos,
    Complex.norm_real, Real.norm_eq_abs]
  have hsin : 2 / (m : ℝ) ≤ Real.sin x := by
    have htm : (t : ℝ) + 1 ≤ m := by exact_mod_cast ht2
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    rcases le_or_gt (2 * t) m with h | h
    · have h' : (2 * t : ℝ) ≤ m := by exact_mod_cast h
      have hx0 : 0 ≤ x := by positivity
      have hxπ : x ≤ π / 2 := by
        rw [hx, div_le_iff₀ hm0]; nlinarith [Real.pi_pos]
      refine le_trans ?_ (Real.mul_le_sin hx0 hxπ)
      rw [hx]; field_simp; nlinarith [Real.pi_pos]
    · have h' : (m : ℝ) < 2 * t := by exact_mod_cast h
      rw [← Real.sin_pi_sub]
      have hy0 : 0 ≤ π - x := by
        rw [hx, sub_nonneg, div_le_iff₀ hm0]; nlinarith [Real.pi_pos]
      have hyπ : π - x ≤ π / 2 := by
        have : π / 2 ≤ x := by
          rw [hx, div_le_div_iff₀ two_pos hm0]; nlinarith [Real.pi_pos]
        linarith
      refine le_trans ?_ (Real.mul_le_sin hy0 hyπ)
      rw [hx]; field_simp; nlinarith [Real.pi_pos]
  have hsq : Real.cos x ^ 2 ≤ Real.exp (-2 / (m : ℝ) ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul, Real.cos_sq']
    have h2m : (0 : ℝ) ≤ 2 / m := by positivity
    have h4 : (2 / (m : ℝ)) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ h2m hsin 2
    have he := Real.add_one_le_exp (-(4 / (m : ℝ) ^ 2))
    have : ((2 : ℕ) : ℝ) * (-2 / (m : ℝ) ^ 2) = -(4 / (m : ℝ) ^ 2) := by push_cast; ring
    rw [this]
    have : (2 / (m : ℝ)) ^ 2 = 4 / (m : ℝ) ^ 2 := by ring
    linarith
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (Real.exp_pos _).le)

/-- **Binomial residue classes.** For `n : ℕ`, an integer `m ≥ 2` and an integer `a`,
`|∑_{0 ≤ k ≤ n, k ≡ a (mod m)} C(n, k) / 2 ^ n - 1 / m| ≤ exp (-2 n / m ^ 2)`. -/
@[collatz_pos_dens "lem_c3_binom_residue"]
theorem abs_sum_choose_filter_modEq_div_sub_inv_le (n : ℕ) {m : ℤ} (hm : 2 ≤ m) (a : ℤ) :
    |∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ a [ZMOD m]),
        (n.choose k : ℝ) / 2 ^ n - 1 / m| ≤ Real.exp (-2 * n / (m : ℝ) ^ 2) := by
  lift m to ℕ using (by omega)
  have hm' : 2 ≤ m := by exact_mod_cast hm
  have hm0 : m ≠ 0 := by omega
  set ζ : ℂ := cexp (2 * π * I / m) with hζdef
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hm0
  have ind : ∀ j : ℤ, ∑ t ∈ range m, (ζ ^ j) ^ t = if (m : ℤ) ∣ j then (m : ℂ) else 0 := by
    intro j
    split_ifs with h
    · rw [(hζ.zpow_eq_one_iff_dvd j).2 h]; simp
    · have hne : ζ ^ j ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd j).1 h')
      rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hζ.pow_eq_one, one_zpow, sub_self, zero_div]
  set u : ℂ := (ζ ^ a)⁻¹ with hu
  set f : ℕ → ℂ := fun t => u ^ t * ((1 + ζ ^ t) / 2) ^ n with hf
  have hS : ((∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ a [ZMOD (m : ℤ)]),
      (n.choose k : ℝ) / 2 ^ n : ℝ) : ℂ) = (1 / m) * ∑ t ∈ range m, f t := by
    push_cast
    rw [Finset.sum_filter]
    have hk : ∀ k ∈ range (n + 1),
        (if (k : ℤ) ≡ a [ZMOD (m : ℤ)] then (n.choose k : ℂ) / 2 ^ n else 0) =
          (1 / m) * ∑ t ∈ range m, u ^ t * ((ζ ^ t) ^ k * (n.choose k : ℂ) / 2 ^ n) := by
      intro k _
      have e : ∀ t : ℕ, u ^ t * ((ζ ^ t) ^ k * (n.choose k : ℂ) / 2 ^ n) =
          (n.choose k : ℂ) / 2 ^ n * (ζ ^ ((k : ℤ) - a)) ^ t := by
        intro t
        rw [zpow_sub₀ hζ0, div_eq_mul_inv (ζ ^ (k : ℤ)), mul_pow, zpow_natCast, hu,
          ← pow_mul, ← pow_mul, mul_comm t k]
        ring
      simp_rw [e, ← Finset.mul_sum, ind, Int.modEq_comm (a := (k : ℤ)), Int.modEq_iff_dvd]
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
      split_ifs
      · field_simp
      · simp
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hf]
    simp only
    rw [← Finset.mul_sum, add_comm (1 : ℂ), div_pow, add_pow, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  set E : ℝ := Real.exp (-2 / (m : ℝ) ^ 2) with hE
  have hfle : ∀ i ∈ range (m - 1), ‖f (i + 1)‖ ≤ E ^ n := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hf]
    simp only
    rw [norm_mul, norm_pow, norm_pow, hu, norm_inv, norm_zpow, hζn, one_zpow, inv_one,
      one_pow, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_one_add_exp_pow_div_two_le (by omega)
      (by omega)) n
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hEn : E ^ n = Real.exp (-2 * n / (m : ℝ) ^ 2) := by
    rw [hE, ← Real.exp_nat_mul]; ring_nf
  have hsplit : ∑ t ∈ range m, f t = ∑ i ∈ range (m - 1), f (i + 1) + f 0 := by
    rw [← Finset.sum_range_succ']; congr 2; omega
  have hf0 : f 0 = 1 := by simp [hf]
  have hdev : ((∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ a [ZMOD (m : ℤ)]),
      (n.choose k : ℝ) / 2 ^ n - 1 / (m : ℝ) : ℝ) : ℂ) =
        (1 / m) * ∑ i ∈ range (m - 1), f (i + 1) := by
    rw [Complex.ofReal_sub, hS, hsplit, hf0]; push_cast; ring
  push_cast
  rw [← hEn, ← Real.norm_eq_abs, ← Complex.norm_real, hdev, norm_mul]
  have hsum : ‖∑ i ∈ range (m - 1), f (i + 1)‖ ≤ (m - 1 : ℕ) * E ^ n := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum hfle
  have hEn0 : 0 ≤ E ^ n := by positivity
  have hm1 : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  rw [norm_div, norm_one, Complex.norm_natCast]
  calc 1 / (m : ℝ) * ‖∑ i ∈ range (m - 1), f (i + 1)‖
      ≤ 1 / m * ((m - 1 : ℕ) * E ^ n) := by gcongr
    _ ≤ 1 / m * (m * E ^ n) := by gcongr
    _ = E ^ n := by field_simp

end CollatzPosDens
