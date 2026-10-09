/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChPairPoint
public import CollatzPosDens.Characters.FxCharacter
public import CollatzPosDens.Characters.FxCharacterAbs
public import CollatzPosDens.Renewal.RnPascal

/-!
# The fiber mass of a pair of letters

Fix `n : ℕ` and a frequency `ξ ∈ G_n`. For `j`, `s ∈ ℤ` and `b ≥ 2`, the sum over the `b - 1`
pairs `(a₁, a₂)` of positive integers with `a₁ + a₂ = b` of
`2^{-b} e_n(-(2^{a₂} + 3) px(j, s+b) ξ)` has modulus exactly `ϖ(b) Fp(j, s, b)`.

The map `(a₁, a₂) ↦ a₂` is a bijection from these pairs onto `{1, …, b - 1}`, so the sum is
`2^{-b} ∑_{t=1}^{b-1} e_n(-(2^t + 3) px(j, s+b) ξ)`, whose modulus is `2^{-b} (b - 1) Fp(j, s, b)`
by the definition of the pair factor; and `ϖ(b) = (b - 1) 2^{-b}`.

## Main results

* `CollatzPosDens.norm_sum_chFiber_eq`: the identity
  `|∑_{a₁+a₂=b, aᵢ ≥ 1} 2^{-b} e_n(-(2^{a₂}+3) px(j,s+b) ξ)| = ϖ(b) Fp(j,s,b)`.
* `CollatzPosDens.norm_sum_chFiber_eq_filter_eq_image`: the pairs are the image of
  `{1, …, b - 1}` under `t ↦ (b - t, t)`.

## Implementation notes

The index `b` is a natural number, cast to `ℤ` in `px`, `ϖ` and `Fp`, and the pairs are the
elements of the antidiagonal of `b` with both coordinates positive. No hypothesis `j ≥ 1` or
`b ≥ 2` is needed: for `b ≤ 1` the sum is empty and `ϖ(b) = 0`. Negative `b` contributes no
pairs, so a natural-number `b` loses nothing.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The pairs `(a₁, a₂)` of positive integers with `a₁ + a₂ = b` are the image of
`{1, …, b - 1}` under `t ↦ (b - t, t)`. -/
theorem norm_sum_chFiber_eq_filter_eq_image (b : ℕ) :
    (antidiagonal b).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ 1 ≤ p.2) =
      (Icc 1 (b - 1)).image (fun t => (b - t, t)) := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_antidiagonal, mem_image, mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨y, ⟨by omega, by omega⟩, by omega, rfl⟩
  · rintro ⟨t, ⟨h1, h2⟩, rfl, rfl⟩; omega

/-- The fiber-mass identity: for `j`, `s` and `b`,
`|∑_{a₁+a₂=b, a₁,a₂ ≥ 1} 2^{-b} e_n(-(2^{a₂}+3) px(j,s+b) ξ)| = ϖ(b) Fp(j,s,b)`. -/
@[collatz_pos_dens "lem_ch_fiber_mass"]
theorem norm_sum_chFiber_eq (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) (b : ℕ) :
    ‖∑ p ∈ (antidiagonal b).filter (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2),
        (2 : ℂ) ^ (-(b : ℤ)) *
          fxChar n (-((2 : ResidueGroup n) ^ p.2 + 3) * chPairPoint n j (s + b) * ξ)‖ =
      varpi b * chPairFactor n ξ j s b := by
  rw [norm_sum_chFiber_eq_filter_eq_image,
    sum_image (fun t _ k _ h => (Prod.mk.inj h).2), ← mul_sum, norm_mul, norm_zpow,
    Complex.norm_ofNat]
  rcases le_or_gt 2 b with h2 | h2
  · have h2' : (2 : ℤ) ≤ b := by exact_mod_cast h2
    rw [varpi_of_two_le h2', chPairFactor_of_two_le _ _ _ _ h2', Int.toNat_natCast]
    have hpos : ((b : ℤ) : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ ((b : ℤ) : ℝ) := by exact_mod_cast h2'
      linarith
    field_simp
  · rw [show b - 1 = 0 by omega, varpi_of_le_one (by omega)]
    simp

end CollatzPosDens
