/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairProduct
public import CollatzPosDens.Characters.FxCharacterHom
public import CollatzPosDens.Transfer.ResidueMap

/-!
# Pairing the letters of a word in a character value

Fix `n : ℕ` and `ξ ∈ G_n`. For `j ≥ 1`, `s ∈ ℤ` and a word `w` of positive integers, the
character value `e_n(-[3^{2(j-1)} 2^{-s} off(w)]_n ξ)` equals the paired character product
`Ep(j, s; w)`. The proof peels off the letters of `w` two at a time: for `w = (a₁, a₂) w'`,
`3^{2(j-1)} 2^{-s} off(w) = (2^{a₂} + 3) 3^{2(j-1)} 2^{-(s+a₁+a₂)}
  + 3^{2j} 2^{-(s+a₁+a₂)} off(w')`,
and the reduction `x ↦ [x]_n` is a ring homomorphism while `e_n` is additive.

## Main results

* `CollatzPosDens.fxChar_neg_dyadicRed_off_mul_eq_chPairProduct`:
  `e_n(-[3^{2(j-1)} 2^{-s} off(w)]_n ξ) = Ep(j, s; w)` for `j ≥ 1`.

## Implementation notes

The index `j` is a natural number with the hypothesis `1 ≤ j`, which is needed: the recursion
of `Ep` raises `j` by one for every two letters, matching the factor `9 = 3^2` in the weight of
a two-letter word only when `3^{2(j-1)} · 9 = 3^{2j}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rational number `3^{2(j-1)} 2^{-s} off(w)` is a dyadic rational. -/
theorem three_pow_mul_two_zpow_mul_off_mem_dyadicRationals (j : ℕ) (s : ℤ) (w : Word) :
    (3 : ℚ) ^ (2 * (j - 1)) * 2 ^ (-s) * off w ∈ dyadicRationals :=
  Subalgebra.mul_mem _ (three_pow_mul_two_zpow_mem_dyadicRationals j s)
    (off_mem_dyadicRationals w)

/-- The expansion with `j = k + 1`, by recursion on the word, two letters at a time. -/
private theorem chPairExpansion_aux (n : ℕ) (ξ : ResidueGroup n) :
    ∀ (k : ℕ) (s : ℤ) (w : Word),
      fxChar n (-(dyadicRed n ⟨(3 : ℚ) ^ (2 * (k + 1 - 1)) * 2 ^ (-s) * off w,
        three_pow_mul_two_zpow_mul_off_mem_dyadicRationals (k + 1) s w⟩ * ξ)) =
      chPairProduct n ξ (k + 1) s w
  | k, s, [] => by
    have h : (⟨(3 : ℚ) ^ (2 * (k + 1 - 1)) * 2 ^ (-s) * off [],
        three_pow_mul_two_zpow_mul_off_mem_dyadicRationals (k + 1) s []⟩ : dyadicRationals) =
        0 := Subtype.ext (by simp)
    rw [h, map_zero, zero_mul, neg_zero, fxChar_zero, chPairProduct_nil]
  | k, s, [a] => by
    have h : (⟨(3 : ℚ) ^ (2 * (k + 1 - 1)) * 2 ^ (-s) * off [a],
        three_pow_mul_two_zpow_mul_off_mem_dyadicRationals (k + 1) s [a]⟩ : dyadicRationals) =
        ⟨(3 : ℚ) ^ (2 * (k + 1 - 1)) * 2 ^ (-(s + a)),
          three_pow_mul_two_zpow_mem_dyadicRationals (k + 1) (s + a)⟩ := Subtype.ext (by
      simp only [off_cons, off_nil, mul_zero, add_zero, mul_one, neg_add,
        zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), zpow_neg, zpow_natCast]
      ring)
    rw [h, chPairProduct_singleton, chPairPoint_def]
  | k, s, a₁ :: a₂ :: w => by
    have h : (⟨(3 : ℚ) ^ (2 * (k + 1 - 1)) * 2 ^ (-s) * off (a₁ :: a₂ :: w),
        three_pow_mul_two_zpow_mul_off_mem_dyadicRationals (k + 1) s (a₁ :: a₂ :: w)⟩ :
          dyadicRationals) =
        (2 ^ (a₂ : ℕ) + 3) * ⟨(3 : ℚ) ^ (2 * (k + 1 - 1)) * 2 ^ (-(s + a₁ + a₂)),
          three_pow_mul_two_zpow_mem_dyadicRationals (k + 1) (s + a₁ + a₂)⟩ +
        ⟨(3 : ℚ) ^ (2 * (k + 1 + 1 - 1)) * 2 ^ (-(s + a₁ + a₂)) * off w,
          three_pow_mul_two_zpow_mul_off_mem_dyadicRationals (k + 1 + 1) (s + a₁ + a₂) w⟩ :=
      Subtype.ext (by
        have h2 : ((2 : dyadicRationals) : ℚ) = 2 := rfl
        have h3 : ((3 : dyadicRationals) : ℚ) = 3 := rfl
        simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, h2, h3,
          off_cons, neg_add, zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), zpow_neg, zpow_natCast,
          Nat.add_sub_cancel]
        field_simp
        ring)
    rw [h, map_add, map_mul, map_add, map_pow, map_ofNat, map_ofNat, ← chPairPoint_def,
      add_mul, neg_add, fxChar_add_eq_mul, chPairProduct_cons_cons,
      chPairExpansion_aux n ξ (k + 1) (s + a₁ + a₂) w]

/-- Pairing the letters: for `j ≥ 1`, `s ∈ ℤ` and every word `w`,
`e_n(-[3^{2(j-1)} 2^{-s} off(w)]_n ξ) = Ep(j, s; w)`. -/
@[collatz_pos_dens "lem_ch_pair_expansion"]
theorem fxChar_neg_dyadicRed_off_mul_eq_chPairProduct (n : ℕ) (ξ : ResidueGroup n) {j : ℕ}
    (hj : 1 ≤ j) (s : ℤ) (w : Word) :
    fxChar n (-(dyadicRed n ⟨(3 : ℚ) ^ (2 * (j - 1)) * 2 ^ (-s) * off w,
      three_pow_mul_two_zpow_mul_off_mem_dyadicRationals j s w⟩ * ξ)) =
      chPairProduct n ξ j s w := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
  exact chPairExpansion_aux n ξ k s w

end CollatzPosDens
