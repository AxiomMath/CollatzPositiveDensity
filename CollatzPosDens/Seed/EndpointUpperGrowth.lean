/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.OffsetBound
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.WeightLower

/-!
# Growth of endpoints

For `b ≥ 1`, `K ≥ 0`, an odd positive integer `R` and a word `w ∈ 𝒲(b, r_b, K)` admissible
from `R`, the source satisfies `src(w, R) ≤ 2^{K+1} (4/3)^b R`.

By the affine identity, `ω(w) src(w, R) = R - off(w) ≤ R` since the offset is nonnegative, and
the weight bound with `u = r_b` gives `ω(w) ≥ 2^{-K-1} (3/4)^b`.

## Main results

* `CollatzPosDens.src_le_of_mem_firstCrossing_rb`: `src(w, R) ≤ 2^{K+1} (4/3)^b R` for
  every nonnegative rational `R` and every `w ∈ 𝒲(b, r_b, K)`.

## Implementation notes

The bound uses neither admissibility, nor oddness, nor `b ≥ 1`: it holds for every rational
`R ≥ 0` and every natural number `b`, and is stated in that generality.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Growth of endpoints.** Every word `w ∈ 𝒲(b, r_b, K)` satisfies
`src(w, R) ≤ 2^{K+1} (4/3)^b R` for every rational `R ≥ 0`; neither `b ≥ 1` nor admissibility
of `w` from an odd positive integer `R` is needed. -/
@[collatz_pos_dens "lem_endpoint_upper_growth"]
theorem src_le_of_mem_firstCrossing_rb {b K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b (rb b) K) {R : ℚ} (hR : 0 ≤ R) :
    src w R ≤ 2 ^ (K + 1) * (4 / 3) ^ b * R := by
  have hω := (le_weight_of_mem_firstCrossing hw).le
  rw [add_sub_cancel_right, show -(K : ℤ) - 1 = -((K + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast] at hω
  have hc : (0 : ℚ) < 2 ^ (K + 1) * (4 / 3) ^ b := by positivity
  have hprod :
      2 ^ (K + 1) * (4 / 3) ^ b * w.weight * src w R ≤ 2 ^ (K + 1) * (4 / 3) ^ b * R := by
    calc _ = 2 ^ (K + 1) * (4 / 3) ^ b * (w.weight * src w R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (by linarith [eq_weight_mul_src_add_off w R, off_nonneg w]) hc.le
  have hge : 1 ≤ 2 ^ (K + 1) * (4 / 3) ^ b * w.weight := by
    have : ((2 : ℚ) ^ (K + 1))⁻¹ * (3 / 4) ^ b * (2 ^ (K + 1) * (4 / 3) ^ b) = 1 := by
      rw [show ((4 : ℚ) / 3) = (3 / 4)⁻¹ by norm_num, inv_pow]
      field_simp
    calc (1 : ℚ) = ((2 : ℚ) ^ (K + 1))⁻¹ * (3 / 4) ^ b * (2 ^ (K + 1) * (4 / 3) ^ b) :=
          this.symm
      _ ≤ w.weight * (2 ^ (K + 1) * (4 / 3) ^ b) := mul_le_mul_of_nonneg_right hω hc.le
      _ = _ := by ring
  rcases le_or_gt (src w R) 0 with hs | hs
  · exact hs.trans (mul_nonneg hc.le hR)
  · exact (le_mul_of_one_le_left hs.le hge).trans hprod

end CollatzPosDens
