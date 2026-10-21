/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3BinomResidue
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import Mathlib.Data.Nat.Periodic

/-!
# Crossing-index residue weights

Let `L = 2 ^ 14` and let `f : ℕ → [0, 1]` be `L`-periodic. For every integer `l`, the row
`r ↦ 𝖱(r - 1, l)` of raw-prefix masses, weighted by `f`, satisfies
`∑_{r ≥ 1} 𝖱(r - 1, l) f(r) ≥ (1 / 4L) ∑_{a < L} f(a) - 8192 exp (-(l - 1) / 2 ^ 29)`.

For `l ≥ 1` and `r ≥ 2`, `𝖱(r - 1, l) = binom(l - 1, 2r - 3) 2^{-l}`, while `𝖱(0, l) = 0`; the
map `r ↦ 2r - 3` identifies the class `r ≡ a (mod L)` with the class
`k ≡ 2a - 3 (mod 2L)` of odd `k`, so the mass `ρ_a` of the class of `a` is half the
`Binomial(l - 1, 1/2)` probability of a residue class modulo `2L = 2 ^ 15`. The binomial
residue bound gives `|ρ_a - 1 / 4L| ≤ exp (-(l - 1) / 2 ^ 29) / 2`, and summing over the `L`
classes against `0 ≤ f ≤ 1` gives the claim, with `L / 2 = 8192`. For `l ≤ 0` the right-hand
side is negative and the claim is trivial.

## Main results

* `CollatzPosDens.le_sum_rawMass_pred_mul`: the bound for the sum over any finite set of
  indices containing every `r ≥ 1` with `𝖱(r - 1, l)` possibly nonzero.

## Implementation notes

The bound is stated for every integer `l`, not only for `l ≥ 2`. The sum over `r ≥ 1` has
finitely many nonzero terms (`𝖱(r - 1, l) = 0` once `2r > l + 2`), so the statement takes the sum
over an arbitrary finite set `s` of indices containing the indices `r ≥ 1` with `2r ≤ l + 2`;
extra indices only add nonnegative terms.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **Crossing-index residue weights.** Let `L = 2 ^ 14`, let `l` be an integer and let
`f : ℕ → [0, 1]` satisfy `f (r + L) = f r`. For every finite set `s` of indices containing all
`r ≥ 1` with `2 r ≤ l + 2` (hence every `r ≥ 1` with `𝖱(r - 1, l) ≠ 0`),
`∑_{r ∈ s} 𝖱(r - 1, l) f(r) ≥ (1 / 4L) ∑_{a < L} f(a) - 8192 exp (-(l - 1) / 2 ^ 29)`. -/
@[collatz_pos_dens "lem_c3_row_residue"]
theorem le_sum_rawMass_pred_mul {l : ℤ} {f : ℕ → ℝ} (hf0 : ∀ r, 0 ≤ f r) (hf1 : ∀ r, f r ≤ 1)
    (hper : ∀ r, f (r + 2 ^ 14) = f r) (s : Finset ℕ)
    (hs : ∀ r : ℕ, 1 ≤ r → 2 * (r : ℤ) ≤ l + 2 → r ∈ s) :
    1 / (4 * 2 ^ 14) * ∑ a ∈ range (2 ^ 14), f a - 8192 * Real.exp (-((l : ℝ) - 1) / 2 ^ 29) ≤
      ∑ r ∈ s, rawMass (r - 1) l * f r := by
  have hS0 : 0 ≤ ∑ r ∈ s, rawMass (r - 1) l * f r :=
    sum_nonneg fun r _ => mul_nonneg (rawMass_nonneg _ _) (hf0 r)
  have hsumf : ∑ a ∈ range (2 ^ 14), f a ≤ 2 ^ 14 := by
    calc ∑ a ∈ range (2 ^ 14), f a ≤ ∑ a ∈ range (2 ^ 14), (1 : ℝ) := sum_le_sum fun a _ => hf1 a
      _ = 2 ^ 14 := by
        simp only [sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rcases lt_or_ge l 1 with hl | hl
  · have hl' : (l : ℝ) ≤ 0 := by exact_mod_cast (show l ≤ 0 by omega)
    have hE : 1 ≤ Real.exp (-((l : ℝ) - 1) / 2 ^ 29) :=
      Real.one_le_exp (div_nonneg (by linarith) (by positivity))
    have : 1 / (4 * 2 ^ 14) * ∑ a ∈ range (2 ^ 14), f a ≤ 1 / (4 * 2 ^ 14) * 2 ^ 14 :=
      mul_le_mul_of_nonneg_left hsumf (by norm_num)
    linarith
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, l = n + 1 := ⟨(l - 1).toNat, by omega⟩
  set F : Finset ℕ := (range (n + 1)).filter (fun k => k % 2 = 1) with hF
  let r : ℕ → ℕ := fun k => (k + 3) / 2
  have hr : ∀ k, r k = (k + 3) / 2 := fun _ => rfl
  set g : ℕ → ℝ := fun k => (n.choose k : ℝ) / 2 ^ n with hg
  have hterm : ∀ k ∈ F, rawMass (r k - 1) ((n : ℤ) + 1) = g k / 2 := by
    intro k hk
    simp only [hF, mem_filter, mem_range] at hk
    rw [rawMass_eq_choose (by rw [hr]; omega), show ((n : ℤ) + 1 - 1).toNat = n by omega,
      show 2 * (r k - 1) - 1 = k by rw [hr]; omega, hg, zpow_neg, zpow_add₀ two_ne_zero,
      zpow_natCast]
    field_simp
  have hinj : Set.InjOn r F := by
    intro x hx y hy hxy
    simp only [hF, coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
    simp only [hr] at hxy
    omega
  have hsub : F.image r ⊆ s := by
    intro x hx
    simp only [hF, mem_image, mem_filter, mem_range] at hx
    obtain ⟨k, ⟨hk, hk2⟩, rfl⟩ := hx
    exact hs _ (by rw [hr]; omega) (by rw [hr]; omega)
  have step1 : ∑ k ∈ F, g k / 2 * f (r k) ≤ ∑ x ∈ s, rawMass (x - 1) ((n : ℤ) + 1) * f x :=
    calc ∑ k ∈ F, g k / 2 * f (r k)
        = ∑ k ∈ F, rawMass (r k - 1) ((n : ℤ) + 1) * f (r k) :=
          sum_congr rfl fun k hk => by rw [hterm k hk]
      _ = ∑ x ∈ F.image r, rawMass (x - 1) ((n : ℤ) + 1) * f x :=
          (sum_image (f := fun x => rawMass (x - 1) ((n : ℤ) + 1) * f x) hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          mul_nonneg (rawMass_nonneg _ _) (hf0 x)
  have hfmod : ∀ x, f (x % 2 ^ 14) = f x := Function.Periodic.map_mod_nat hper
  have step2 : ∑ k ∈ F, g k / 2 * f (r k) = ∑ a ∈ range (2 ^ 14), f a *
      (∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ 2 * (a : ℤ) - 3 [ZMOD 2 * 2 ^ 14]),
        g k) / 2 := by
    rw [← sum_fiberwise_of_maps_to (g := fun k => r k % 2 ^ 14) (t := range (2 ^ 14))
      (fun k _ => mem_range.2 (Nat.mod_lt _ (by norm_num)))]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_range] at ha
    have hset : F.filter (fun k => r k % 2 ^ 14 = a) =
        (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ 2 * (a : ℤ) - 3 [ZMOD 2 * 2 ^ 14]) := by
      ext k
      rw [hF, mem_filter, mem_filter, mem_filter, mem_range, hr, Int.ModEq]
      omega
    rw [mul_sum, sum_div, ← hset]
    refine sum_congr rfl fun k hk => ?_
    simp only [mem_filter] at hk
    rw [← hk.2, hfmod]
    ring
  set E : ℝ := Real.exp (-(((n : ℤ) + 1 : ℤ) - 1 : ℝ) / 2 ^ 29) with hEdef
  have hres : ∀ a : ℕ, 1 / (2 * 2 ^ 14) - E ≤
      ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ 2 * (a : ℤ) - 3 [ZMOD 2 * 2 ^ 14]),
        g k := by
    intro a
    have h := abs_sum_choose_filter_modEq_div_sub_inv_le n (m := 2 * 2 ^ 14) (by norm_num)
      (2 * (a : ℤ) - 3)
    have hE : Real.exp (-2 * n / (((2 * 2 ^ 14 : ℤ)) : ℝ) ^ 2) = E := by
      rw [hEdef]; congr 1; push_cast; ring
    rw [hE] at h
    have h' := (abs_le.1 h).1
    push_cast at h'
    simp only [hg]
    linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have step3 : ∀ a ∈ range (2 ^ 14), f a / (4 * 2 ^ 14) - E / 2 ≤ f a *
      (∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℤ) ≡ 2 * (a : ℤ) - 3 [ZMOD 2 * 2 ^ 14]),
        g k) / 2 := by
    intro a _
    have h1 := mul_le_mul_of_nonneg_left (hres a) (hf0 a)
    have := hf1 a
    have := hf0 a
    nlinarith
  have step4 := sum_le_sum step3
  rw [← step2, sum_sub_distrib, ← sum_div] at step4
  simp only [sum_const, card_range, nsmul_eq_mul] at step4
  push_cast at step4 ⊢
  linarith

end CollatzPosDens
