/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Transfer.MxProfile

/-!
# The terminal majorant `T_j`

For a natural number `j` the terminal majorant is the real number
$$\mathsf T_j := 5\,j^{9/2}\,\mathsf g^{j/2}\Bigl(2\,\mathfrak M_{\mathrm o}
  \bigl(2^{12}\,\mathsf g^{j}\bigr) + (2^{32} + 2^{29})\,\mathsf g^{-6j}
  + 2^{-29}\cdot 2^{-j/56}\Bigr),$$
where `𝗀 = 101/100` is the physical growth ratio, `𝔐_o` the propagation mixing profile at the
original Fourier index `o`, and all powers are positive real powers (the argument `2^12 𝗀^j` of
`𝔐_o` is positive).

## Main definitions

* `CollatzPosDens.terminalMajorant`: the terminal majorant `T_j`, as a function `ℕ → ℝ`.

## Main results

* `CollatzPosDens.terminalMajorant_def`: the defining formula of `T_j`.
* `CollatzPosDens.terminalMajorant_nonneg`: `0 ≤ T_j` for every `j`.
* `CollatzPosDens.terminalMajorant_pos`: `0 < T_j` for `1 ≤ j`.

## Implementation notes

The majorant is defined for every natural number `j`, through `Real.rpow`; at `j = 0` it
vanishes because of the factor `j ^ (9/2)`. The constants `2 ^ 12`, `2 ^ 32` and `2 ^ 29` are
written as natural-number powers, which agree with the corresponding real powers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The terminal majorant
`T_j := 5 j ^ (9/2) 𝗀 ^ (j/2) (2 𝔐_o(2 ^ 12 𝗀 ^ j) + (2 ^ 32 + 2 ^ 29) 𝗀 ^ (-6j)
  + 2 ^ (-29) 2 ^ (-j/56))`, with positive real powers. -/
@[collatz_pos_dens "def_s06_Tj"]
noncomputable def terminalMajorant (j : ℕ) : ℝ :=
  5 * (j : ℝ) ^ (9 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
    (2 * mxProfile .o (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) +
      (2 ^ 32 + 2 ^ 29) * (growthRatio : ℝ) ^ (-(6 * (j : ℝ))) +
      (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)))

/-- The defining formula of the terminal majorant. -/
theorem terminalMajorant_def (j : ℕ) :
    terminalMajorant j =
      5 * (j : ℝ) ^ (9 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
        (2 * mxProfile .o (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) +
          (2 ^ 32 + 2 ^ 29) * (growthRatio : ℝ) ^ (-(6 * (j : ℝ))) +
          (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56))) := rfl

/-- The bracket of the terminal majorant is positive. -/
private lemma terminalMajorant_bracket_pos (j : ℕ) :
    0 < 2 * mxProfile .o (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) +
      (2 ^ 32 + 2 ^ 29) * (growthRatio : ℝ) ^ (-(6 * (j : ℝ))) +
      (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)) := by
  have hg := growthRatio_cast_pos
  have hx : 1 ≤ 2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ) := by
    have : 1 ≤ (growthRatio : ℝ) ^ (j : ℝ) :=
      Real.one_le_rpow one_lt_growthRatio_cast.le (Nat.cast_nonneg j)
    linarith
  have h1 := mxProfile_pos .o hx
  have h2 : 0 < (2 ^ 32 + 2 ^ 29 : ℝ) * (growthRatio : ℝ) ^ (-(6 * (j : ℝ))) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hg _)
  have h3 : 0 < (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)) :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos two_pos _)
  exact add_pos (add_pos (mul_pos two_pos h1) h2) h3

/-- The terminal majorant is nonnegative. -/
theorem terminalMajorant_nonneg (j : ℕ) : 0 ≤ terminalMajorant j := by
  rw [terminalMajorant_def]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
    (Real.rpow_nonneg growthRatio_cast_pos.le _)) (terminalMajorant_bracket_pos j).le

/-- The terminal majorant is positive for `1 ≤ j`. -/
theorem terminalMajorant_pos {j : ℕ} (hj : 1 ≤ j) : 0 < terminalMajorant j := by
  rw [terminalMajorant_def]
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hj' _))
    (Real.rpow_pos_of_pos growthRatio_cast_pos _)) (terminalMajorant_bracket_pos j)

end CollatzPosDens
