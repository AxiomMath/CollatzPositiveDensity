/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.PhHhist
public import CollatzPosDens.Transfer.MxProfile

/-!
# The propagation majorant `E_j`

For a natural number `j` the propagation majorant is the real number
$$\mathsf E_j := \mathcal H_{\mathrm{hist}}\, j^{5/2}\, \mathsf g^{j/2}
  \bigl(2\,\mathfrak M_{\mathrm b}(2^{12}\,\mathsf g^{j}) + \tfrac12\,\mathsf g^{-3j/2}
  + 2^{-29}\cdot 2^{-j/56}\bigr),$$
where `𝓗_hist = 344` is the histogram constant, `𝗀 = 101/100` the physical growth
ratio, `𝔐_b` the propagation mixing profile at the bootstrap Fourier index `b`, and all powers
are positive real powers.

## Main definitions

* `CollatzPosDens.propagationMajorant`: the propagation majorant `E_j`, as a function `ℕ → ℝ`.

## Main results

* `CollatzPosDens.propagationMajorant_def`: the defining formula of `E_j`.
* `CollatzPosDens.propagationMajorant_nonneg`: `0 ≤ E_j` for every `j`.
* `CollatzPosDens.propagationMajorant_pos`: `0 < E_j` for `1 ≤ j`.

## Implementation notes

The majorant is defined for every natural number `j`, through `Real.rpow`; at `j = 0` it
vanishes because of the factor `j ^ (5/2)`. The Fourier index of the profile is fixed at `b`, so
the majorant takes no index argument.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The propagation majorant
`E_j := 𝓗_hist j ^ (5/2) 𝗀 ^ (j/2) (2 𝔐_b(2 ^ 12 𝗀 ^ j) + 𝗀 ^ (-3j/2) / 2 + 2 ^ (-29) 2 ^ (-j/56))`
with positive real powers. -/
@[collatz_pos_dens "def_ph_Ej"]
noncomputable def propagationMajorant (j : ℕ) : ℝ :=
  (Hhist : ℝ) * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
    (2 * mxProfile .b (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) +
      1 / 2 * (growthRatio : ℝ) ^ (-(3 * (j : ℝ) / 2)) +
      (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)))

/-- The defining formula of the propagation majorant. -/
theorem propagationMajorant_def (j : ℕ) :
    propagationMajorant j =
      (Hhist : ℝ) * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
        (2 * mxProfile .b (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) +
          1 / 2 * (growthRatio : ℝ) ^ (-(3 * (j : ℝ) / 2)) +
          (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56))) := rfl

/-- The bracket of the propagation majorant is positive. -/
private lemma propagationMajorant_bracket_pos (j : ℕ) :
    0 < 2 * mxProfile .b (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) +
      1 / 2 * (growthRatio : ℝ) ^ (-(3 * (j : ℝ) / 2)) +
      (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)) := by
  have hg := growthRatio_cast_pos
  have hx : 1 ≤ 2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ) := by
    have : 1 ≤ (growthRatio : ℝ) ^ (j : ℝ) :=
      Real.one_le_rpow one_lt_growthRatio_cast.le (Nat.cast_nonneg j)
    linarith
  have h1 := mxProfile_pos .b hx
  have h2 : 0 < (growthRatio : ℝ) ^ (-(3 * (j : ℝ) / 2)) := Real.rpow_pos_of_pos hg _
  have h3 : 0 < (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)) :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos two_pos _)
  exact add_pos (add_pos (mul_pos two_pos h1) (mul_pos one_half_pos h2)) h3

/-- The propagation majorant is nonnegative. -/
theorem propagationMajorant_nonneg (j : ℕ) : 0 ≤ propagationMajorant j := by
  rw [propagationMajorant_def]
  have hH : (0 : ℝ) < Hhist := by exact_mod_cast Hhist_pos
  exact mul_nonneg (mul_nonneg (mul_nonneg hH.le (Real.rpow_nonneg (Nat.cast_nonneg j) _))
    (Real.rpow_nonneg growthRatio_cast_pos.le _)) (propagationMajorant_bracket_pos j).le

/-- The propagation majorant is positive for `1 ≤ j`. -/
theorem propagationMajorant_pos {j : ℕ} (hj : 1 ≤ j) : 0 < propagationMajorant j := by
  rw [propagationMajorant_def]
  have hH : (0 : ℝ) < Hhist := by exact_mod_cast Hhist_pos
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  exact mul_pos (mul_pos (mul_pos hH (Real.rpow_pos_of_pos hj' _))
    (Real.rpow_pos_of_pos growthRatio_cast_pos _)) (propagationMajorant_bracket_pos j)

end CollatzPosDens
