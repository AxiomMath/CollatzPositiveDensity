/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Transfer.Z

/-!
# The white factor

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a point `p ∈ 𝒫` the *white
factor* is `w(p) = e^{-z_*}` if `p` is white for `n, ξ, ε` (`IsBkWhite`), and `w(p) = 1`
otherwise. Here `z_* = 21/500` is the white Fourier penalty `zStar`.

## Main definitions

* `CollatzPosDens.chWhiteFactor n ξ ε p`: the white factor `w(p)`.

## Main results

* `CollatzPosDens.chWhiteFactor_of_isBkWhite`,
  `CollatzPosDens.chWhiteFactor_of_not_isBkWhite`: the two cases of the definition.
* `CollatzPosDens.chWhiteFactor_of_isBkWhite'`: a white point has factor `e^{-21/500}`.
* `CollatzPosDens.chWhiteFactor_pos`, `CollatzPosDens.chWhiteFactor_le_one`:
  `0 < w(p) ≤ 1`; `CollatzPosDens.chWhiteFactor_nonneg`: `0 ≤ w(p)`.

## Implementation notes

The level `n`, the residue `ξ` and the threshold `ε` are explicit arguments. As for `IsBkWhite`,
the factor is defined for every `p : ℤ × ℤ`, not only for points of `𝒫 = bkPoints`. The rational
constant `z_*` is cast to `ℝ` in the exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The white factor `w(p)`: `e^{-z_*}` if `p` is white for `n, ξ, ε`, and `1` otherwise. -/
@[collatz_pos_dens "def_ch_white_factor"]
noncomputable def chWhiteFactor (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℝ :=
  if IsBkWhite n ξ ε p then Real.exp (-(zStar : ℝ)) else 1

/-- The white factor of a white point is `e^{-z_*}`. -/
theorem chWhiteFactor_of_isBkWhite {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) : chWhiteFactor n ξ ε p = Real.exp (-(zStar : ℝ)) := by
  simp [chWhiteFactor, h]

/-- The white factor of a white point is `e^{-21/500}`. -/
theorem chWhiteFactor_of_isBkWhite' {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) : chWhiteFactor n ξ ε p = Real.exp (-(21 / 500)) := by
  rw [chWhiteFactor_of_isBkWhite h, zStar_cast]

/-- The white factor of a non-white point is `1`. -/
theorem chWhiteFactor_of_not_isBkWhite {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : ¬ IsBkWhite n ξ ε p) : chWhiteFactor n ξ ε p = 1 := by
  simp [chWhiteFactor, h]

/-- The white factor is positive. -/
theorem chWhiteFactor_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    0 < chWhiteFactor n ξ ε p := by
  unfold chWhiteFactor
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

/-- The white factor is nonnegative. -/
theorem chWhiteFactor_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    0 ≤ chWhiteFactor n ξ ε p :=
  (chWhiteFactor_pos n ξ ε p).le

/-- The white factor is at most `1`. -/
theorem chWhiteFactor_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    chWhiteFactor n ξ ε p ≤ 1 := by
  unfold chWhiteFactor
  split_ifs
  · rw [zStar_cast, Real.exp_le_one_iff]; norm_num
  · exact le_rfl

end CollatzPosDens
