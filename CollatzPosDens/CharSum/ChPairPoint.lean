/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Units
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.DyadicReduction

/-!
# The pair point

Fix `n : ℕ`. For integers `j ≥ 1` and `l ∈ ℤ`, the rational number `3^{2(j-1)} 2^{-l}` is a
dyadic rational, and the *pair point* is its reduction modulo `3^n`,
`px(j, l) = [3^{2(j-1)} 2^{-l}]_n ∈ G_n`. Since `2` is a unit of `G_n`, this is the product of
`3^{2(j-1)}` with the `(-l)`-th power of the unit `2`.

## Main definitions

* `CollatzPosDens.chPairPoint n j l`: the pair point `px(j, l) = [3^{2(j-1)} 2^{-l}]_n`.

## Main results

* `CollatzPosDens.two_zpow_mem_dyadicRationals`: `2^l ∈ ℤ[1/2]` for every `l ∈ ℤ`.
* `CollatzPosDens.dyadicRed_two_zpow`: `[2^l]_n` is the `l`-th power of the unit `2` of `G_n`.
* `CollatzPosDens.chPairPoint_eq`: `px(j, l) = 3^{2(j-1)} · 2^{-l}`, computed in the units
  of `G_n`.

## Implementation notes

The index `j` is a natural number and `j - 1` is truncated subtraction, so `chPairPoint n 0 l`
agrees with `chPairPoint n 1 l`; the pair point is only of interest for `j ≥ 1`. The power
`2^{-l}` of the unit `2` of `G_n` is the integer power in the unit group `(ZMod (3 ^ n))ˣ`, the
unit being `ZMod.unitOfCoprime 2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Every integer power `2^l` of `2` is a dyadic rational. -/
theorem two_zpow_mem_dyadicRationals (l : ℤ) : (2 : ℚ) ^ l ∈ dyadicRationals := by
  rcases l with m | m
  · have : ((2 : ℚ) ^ (Int.ofNat m)) = ((2 ^ m : ℤ) : ℚ) / 2 ^ 0 := by simp
    rw [this]; exact intCast_div_two_pow_mem _ _
  · have : ((2 : ℚ) ^ (Int.negSucc m)) = ((1 : ℤ) : ℚ) / 2 ^ (m + 1) := by
      rw [zpow_negSucc]; simp
    rw [this]; exact intCast_div_two_pow_mem _ _

/-- The rational number `3^{2(j-1)} 2^{-l}` is a dyadic rational. -/
theorem three_pow_mul_two_zpow_mem_dyadicRationals (j : ℕ) (l : ℤ) :
    (3 : ℚ) ^ (2 * (j - 1)) * 2 ^ (-l) ∈ dyadicRationals := by
  refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) (two_zpow_mem_dyadicRationals _)
  simp

/-- The pair point `px(j, l) = [3^{2(j-1)} 2^{-l}]_n ∈ G_n`: the reduction modulo `3^n` of the
dyadic rational `3^{2(j-1)} 2^{-l}`. -/
@[collatz_pos_dens "def_ch_pair_point"]
noncomputable def chPairPoint (n j : ℕ) (l : ℤ) : ResidueGroup n :=
  dyadicRed n ⟨(3 : ℚ) ^ (2 * (j - 1)) * 2 ^ (-l),
    three_pow_mul_two_zpow_mem_dyadicRationals j l⟩

/-- `chPairPoint n j l` is the reduction modulo `3^n` of the dyadic rational
`3^{2(j-1)} 2^{-l}`. -/
theorem chPairPoint_def (n j : ℕ) (l : ℤ) :
    chPairPoint n j l = dyadicRed n ⟨(3 : ℚ) ^ (2 * (j - 1)) * 2 ^ (-l),
      three_pow_mul_two_zpow_mem_dyadicRationals j l⟩ := rfl

/-- The reduction of `2^l` modulo `3^n` is the `l`-th power of the unit `2` of `G_n`. -/
theorem dyadicRed_two_zpow (n : ℕ) (l : ℤ) :
    dyadicRed n ⟨(2 : ℚ) ^ l, two_zpow_mem_dyadicRationals l⟩ =
      ((ZMod.unitOfCoprime 2 (coprime_two_three_pow n) ^ l : (ZMod (3 ^ n))ˣ) :
        ResidueGroup n) := by
  set u := ZMod.unitOfCoprime 2 (coprime_two_three_pow n)
  have hu : (u : ResidueGroup n) = 2 := by simp [u]
  rcases l with m | m
  · have h : (⟨(2 : ℚ) ^ (Int.ofNat m), two_zpow_mem_dyadicRationals _⟩ : dyadicRationals) =
        (2 : dyadicRationals) ^ m := Subtype.ext (by
      rw [Subalgebra.coe_pow]; simp; rfl)
    rw [h, map_pow, map_ofNat, Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, hu]
  · have h : (⟨(2 : ℚ) ^ (Int.negSucc m), two_zpow_mem_dyadicRationals _⟩ : dyadicRationals) =
        ⟨((1 : ℤ) : ℚ) / 2 ^ (m + 1), intCast_div_two_pow_mem _ _⟩ :=
      Subtype.ext (by
        change (2 : ℚ) ^ (Int.negSucc m) = ((1 : ℤ) : ℚ) / 2 ^ (m + 1)
        rw [zpow_negSucc]; simp)
    rw [h, dyadicRed_div_two_pow, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val,
      ← ZMod.inv_coe_unit, hu, Int.cast_one, one_mul]

/-- The pair point is `3^{2(j-1)}` times the `(-l)`-th power of the unit `2` of `G_n`. -/
theorem chPairPoint_eq (n j : ℕ) (l : ℤ) :
    chPairPoint n j l = (3 : ResidueGroup n) ^ (2 * (j - 1)) *
      ((ZMod.unitOfCoprime 2 (coprime_two_three_pow n) ^ (-l) : (ZMod (3 ^ n))ˣ) :
        ResidueGroup n) := by
  have h : (⟨(3 : ℚ) ^ (2 * (j - 1)) * 2 ^ (-l),
      three_pow_mul_two_zpow_mem_dyadicRationals j l⟩ : dyadicRationals) =
      (3 : dyadicRationals) ^ (2 * (j - 1)) * ⟨(2 : ℚ) ^ (-l), two_zpow_mem_dyadicRationals _⟩ :=
    Subtype.ext (by rw [Subalgebra.coe_mul, Subalgebra.coe_pow]; rfl)
  rw [chPairPoint_def, h, map_mul, map_pow, map_ofNat, dyadicRed_two_zpow]

end CollatzPosDens
