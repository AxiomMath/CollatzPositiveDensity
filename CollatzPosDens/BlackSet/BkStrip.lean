/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkSfrRep
public import CollatzPosDens.BlackSet.BkSfrScaleBound

/-!
# The strip bound for the angle

Let `ξ ∈ G_n` be a unit and `(j, l) ∈ 𝒫` with `j ≤ ⌊n/2⌋`. Then
`1/3 ≤ 3^{n+1-2j} |ϑ(j, l)|`. Indeed, with `k = n + 1 - 2j ≥ 1` one has
`3^k r(j, l) = 3^{n-1} u` for the unit `u = [2^{1-l}]_n ξ`; since `3` does not divide the
representative of `u`, the residue `3^{n-1} u` is represented by `±3^{n-1}`, so its signed
fractional part has absolute value `1/3`, and the scaling bound `|sfr (3^k z)| ≤ 3^k |sfr z|`
concludes.

## Main results

* `CollatzPosDens.abs_sfr_three_pow_mul_eq`: for a unit `w ∈ G_{m+1}`,
  `|sfr (3^m w)| = 1/3`.
* `CollatzPosDens.one_third_le_three_zpow_mul_abs_bkTheta`: the strip bound
  `1/3 ≤ 3^{n+1-2j} |ϑ_{n,ξ}(j, l)|`.

## Implementation notes

The exponent `n + 1 - 2j` is an integer, and `3^{n+1-2j}` is written as an integer power of the
real number `3`; under the hypotheses it is a positive natural number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- For a unit `w ∈ G_{m+1}` the residue `3^m w` is represented by `±3^m`, so its signed
fractional part has absolute value `1/3`. -/
theorem abs_sfr_three_pow_mul_eq {m : ℕ} {w : ResidueGroup (m + 1)} (hw : IsResidueUnit w) :
    |sfr ((3 : ResidueGroup (m + 1)) ^ m * w)| = 1 / 3 := by
  have hc : w.val % 3 = 1 ∨ w.val % 3 = 2 := by
    unfold IsResidueUnit at hw; omega
  have hrep : (3 : ResidueGroup (m + 1)) ^ m * w = ((3 ^ m * (w.val % 3) : ℕ) : _) := by
    rw [← Nat.mul_mod_mul_left, ← pow_succ, ZMod.natCast_mod]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hN : ((3 ^ (m + 1) : ℕ) : ℝ) = 3 * 3 ^ m := by push_cast; ring
  have hpos : (0 : ℝ) < 3 ^ m := by positivity
  rcases hc with hc | hc
  · rw [hc, mul_one] at hrep
    rw [sfr_eq_of_abs_lt (m := (3 ^ m : ℕ)) (by rw [hrep, Int.cast_natCast]), hN]
    · push_cast
      rw [abs_of_pos (by positivity)]
      field_simp
    · rw [hN]; push_cast; rw [abs_of_pos hpos]; linarith
  · rw [hc] at hrep
    have hz : ((-(3 ^ m : ℕ) : ℤ) : ResidueGroup (m + 1)) =
        (3 : ResidueGroup (m + 1)) ^ m * w := by
      rw [hrep]
      have h0 : ((3 ^ (m + 1) : ℕ) : ResidueGroup (m + 1)) = 0 := ZMod.natCast_self _
      push_cast at h0 ⊢
      rw [pow_succ] at h0
      linear_combination -h0
    rw [sfr_eq_of_abs_lt hz, hN]
    · push_cast
      rw [abs_div, abs_neg, abs_of_pos hpos, abs_of_pos (by positivity)]
      field_simp
    · rw [hN]; push_cast; rw [abs_neg, abs_of_pos hpos]; linarith

/-- **Strip bound.** Let `ξ ∈ G_n` be a unit and `p = (j, l) ∈ 𝒫` with `j ≤ ⌊n/2⌋`. Then
`1/3 ≤ 3^{n+1-2j} |ϑ_{n,ξ}(j, l)|`. -/
@[collatz_pos_dens "lem_bk_strip"]
theorem one_third_le_three_zpow_mul_abs_bkTheta {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hj : bkJ p ≤ ((n / 2 : ℕ) : ℤ)) :
    (1 / 3 : ℝ) ≤ (3 : ℝ) ^ ((n : ℤ) + 1 - 2 * bkJ p) * |bkTheta n ξ p| := by
  rw [mem_bkPoints] at hp
  obtain ⟨a, ha⟩ : ∃ a : ℕ, bkJ p = a + 1 := ⟨(bkJ p - 1).toNat, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, n = 2 * a + b + 2 := ⟨n - 2 * a - 2, by omega⟩
  have hexp : (((2 * a + b + 2 : ℕ) : ℤ) + 1 - 2 * bkJ p) = ((b + 1 : ℕ) : ℤ) := by
    push_cast; omega
  have he : (2 * (bkJ p - 1)).toNat = 2 * a := by omega
  rw [hexp, zpow_natCast]
  set U : ResidueGroup (2 * a + b + 2) :=
    ((((isUnit_two_residueGroup (2 * a + b + 2)).unit ^ (1 - bkL p) :
      (ResidueGroup (2 * a + b + 2))ˣ) : ResidueGroup (2 * a + b + 2))) with hU
  have hξu : IsUnit ξ := (isResidueUnit_iff_isUnit (by omega) ξ).1 hξ
  have hw : IsResidueUnit (U * ξ) :=
    (isResidueUnit_iff_isUnit (q := 2 * a + b + 1 + 1) (by omega) _).2
      ((Units.isUnit _).mul hξu)
  have key : ((3 ^ (b + 1) : ℕ) : ResidueGroup (2 * a + b + 2)) * bkThetaResidue _ ξ p =
      (3 : ResidueGroup (2 * a + b + 1 + 1)) ^ (2 * a + b + 1) * (U * ξ) := by
    rw [bkThetaResidue_eq, he, ← hU]
    push_cast
    ring
  have h := abs_sfr_natCast_mul_le (bkThetaResidue _ ξ p) (3 ^ (b + 1))
  rw [key, abs_sfr_three_pow_mul_eq hw] at h
  rw [bkTheta_def]
  exact_mod_cast h

end CollatzPosDens
