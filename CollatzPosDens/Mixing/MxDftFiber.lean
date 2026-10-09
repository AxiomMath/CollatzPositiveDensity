/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterHom
public import CollatzPosDens.Characters.FxCharacterInt
public import CollatzPosDens.Mixing.MxFiberAvg
public import CollatzPosDens.Mixing.MxFiberSize
public import CollatzPosDens.Mixing.MxRootSum

/-!
# Fourier coefficients of a function minus its fibre average

Let `0 ≤ m ≤ n`, `c : G_n → ℝ`, and let `d = c - Avg_{m,n} c` be `c` minus its average over the
fibres of the reduction `π_{n,m} : G_n → G_m`. Then for every `ξ ∈ G_n`,
`d̂(ξ) = [3^m ξ ≠ 0] · ĉ(ξ)`: subtracting the fibre average kills exactly the frequencies
annihilated by `3^m` and leaves the others untouched.

The fibre of `π_{n,m}` through `y` is `{y + [3^m t]_n : t < 3^{n-m}}`, so the transform of the
fibre average is `ĉ(ξ)` times `3^{m-n} ∑_{t < 3^{n-m}} e_n(-3^m ξ t)`, and this normalised
sum of roots of unity is `1` if `3^m ξ = 0` and `0` otherwise.

## Main results

* `CollatzPosDens.fxDft_sub_fiberAvg`: `d̂(ξ) = [3^m ξ ≠ 0] · ĉ(ξ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Finset Real

/-- The sum of the character `z ↦ e_n(-ξ z)` over the fibre of `π_{n,m}` through `y'`
factors as `e_n(-ξ y')` times the sum over the kernel, parametrised by `t < 3^{n-m}`. -/
private theorem sum_fxChar_fiber_eq_mul {m n : ℕ} (h : m ≤ n) (ξ y' : ResidueGroup n) :
    ∑ y ∈ univ.filter (fun y => residueReduction h y = residueReduction h y'),
        fxChar n (-(ξ * y)) =
      fxChar n (-(ξ * y')) *
        ∑ t ∈ range (3 ^ (n - m)), fxChar n (-(ξ * ((3 ^ m * t : ℕ) : ResidueGroup n))) := by
  have hb := bijOn_add_three_pow_mul_residueReduction_fiber h y'
  rw [mul_sum]
  symm
  refine sum_nbij (fun t : ℕ => y' + ((3 ^ m * t : ℕ) : ResidueGroup n)) ?_ ?_ ?_ ?_
  · intro t ht
    have := hb.mapsTo (Set.mem_Iio.2 (mem_range.1 ht))
    simpa using this
  · intro s hs t ht hst
    exact hb.injOn (Set.mem_Iio.2 (mem_range.1 hs)) (Set.mem_Iio.2 (mem_range.1 ht)) hst
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := hb.surjOn (by simpa using hy)
    exact ⟨t, by simpa using ht, rfl⟩
  · intro t _
    rw [mul_add, neg_add, fxChar_add_eq_mul]

/-- The kernel sum `∑_{t < 3^{n-m}} e_n(-ξ [3^m t]_n)` is `3^{n-m}` if `3^m ξ = 0` and `0`
otherwise. -/
private theorem sum_fxChar_kernel_eq {m n : ℕ} (h : m ≤ n) (ξ : ResidueGroup n) :
    ∑ t ∈ range (3 ^ (n - m)), fxChar n (-(ξ * ((3 ^ m * t : ℕ) : ResidueGroup n))) =
      if (3 : ResidueGroup n) ^ m * ξ = 0 then ((3 ^ (n - m) : ℕ) : ℂ) else 0 := by
  have hpow : 3 ^ n = 3 ^ m * 3 ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' h]
  have hterm : ∀ t : ℕ, fxChar n (-(ξ * ((3 ^ m * t : ℕ) : ResidueGroup n))) =
      exp (2 * π * I * ((-(ξ.val : ℤ) : ℤ) : ℂ) * t / ((3 ^ (n - m) : ℕ) : ℂ)) := by
    intro t
    rw [fxChar_eq_exp_of_intModEq n _ (-(ξ.val * 3 ^ m * t : ℤ))]
    · congr 1
      have h3 : (3 : ℂ) ^ n = 3 ^ m * 3 ^ (n - m) := by exact_mod_cast hpow
      rw [h3]
      push_cast
      field_simp
    · have hc := (ZMod.intCast_eq_intCast_iff (-(ξ.val * 3 ^ m * t : ℤ))
        ((-(ξ * ((3 ^ m * t : ℕ) : ResidueGroup n))).val : ℤ) (3 ^ n)).1 (by
          push_cast
          simp only [ZMod.natCast_val, ZMod.cast_id', id]
          ring)
      exact_mod_cast hc
  simp_rw [hterm]
  rw [sum_exp_two_pi_mul_I_mul_div (by positivity)]
  congr 1
  apply propext
  rw [Int.dvd_neg, Int.natCast_dvd_natCast,
    ← Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : 0 < 3) m), ← hpow,
    ← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id]

/-- Let `0 ≤ m ≤ n`, `c, d : G_n → ℝ` with `d(y) = c(y) - Avg_{m,n} c (y)` for all `y`, and
`ξ ∈ G_n`. Then `d̂(ξ) = [3^m ξ ≠ 0] · ĉ(ξ)`. -/
@[collatz_pos_dens "lem_mx_dft_fiber"]
theorem fxDft_sub_fiberAvg {m n : ℕ} (h : m ≤ n) (c d : ResidueGroup n → ℝ)
    (hd : ∀ y, d y = c y - fiberAvg h c y) (ξ : ResidueGroup n) :
    fxDft n (fun y => (d y : ℂ)) ξ =
      (if (3 : ResidueGroup n) ^ m * ξ ≠ 0 then (1 : ℂ) else 0) *
        fxDft n (fun y => (c y : ℂ)) ξ := by
  set S := ∑ t ∈ range (3 ^ (n - m)),
    fxChar n (-(ξ * ((3 ^ m * t : ℕ) : ResidueGroup n))) with hS
  have havg : fxDft n (fun y => (fiberAvg h c y : ℂ)) ξ =
      ((3 : ℂ) ^ (n - m))⁻¹ * S * fxDft n (fun y => (c y : ℂ)) ξ := by
    simp only [fxDft_apply, fiberAvg, three_zpow_sub_eq_inv h]
    push_cast
    simp only [sum_filter, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun y' _ => ?_
    have := sum_fxChar_fiber_eq_mul h ξ y'
    rw [sum_filter] at this
    calc _ = ((3 : ℂ) ^ (n - m))⁻¹ * (c y' : ℂ) * ∑ y, (if residueReduction h y =
            residueReduction h y' then fxChar n (-(ξ * y)) else 0) := by
          rw [mul_sum]
          refine sum_congr rfl fun y _ => ?_
          simp only [eq_comm (a := residueReduction h y')]
          split_ifs <;> simp
      _ = _ := by rw [this, ← hS]; ring
  have hsplit : fxDft n (fun y => (d y : ℂ)) ξ =
      fxDft n (fun y => (c y : ℂ)) ξ - fxDft n (fun y => (fiberAvg h c y : ℂ)) ξ := by
    simp only [fxDft_apply, hd, ← sum_sub_distrib]
    push_cast
    exact sum_congr rfl fun y _ => by ring
  rw [hsplit, havg, hS, sum_fxChar_kernel_eq h ξ]
  by_cases h1 : (3 : ResidueGroup n) ^ m * ξ = 0
  · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
    ring
  · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte]
    ring

end CollatzPosDens
