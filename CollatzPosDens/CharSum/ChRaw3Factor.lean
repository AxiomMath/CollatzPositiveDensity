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
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.Transfer.Z

/-!
# The raw-three factor

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a point `p ∈ 𝒫` the *raw-three
factor* is `w₃(p) = e^{-κ_* z_*}` if `p` is white (for `n, ξ, ε`), and `w₃(p) = 1` otherwise.
Here `κ_* = 4/25` and `z_* = 21/500`, so `κ_* z_* = 21/3125`. It is the factor charged to a
letter `3` in the penalty of a letter sequence.

## Main definitions

* `CollatzPosDens.chRaw3Factor n ξ ε p`: the raw-three factor `w₃(p)`.

## Main results

* `CollatzPosDens.chRaw3Factor_of_isBkWhite`,
  `CollatzPosDens.chRaw3Factor_of_not_isBkWhite`: the two cases of the definition.
* `CollatzPosDens.chRaw3Factor_exponent`: `κ_* z_* = 21/3125`.
* `CollatzPosDens.chRaw3Factor_pos`, `CollatzPosDens.chRaw3Factor_le_one`:
  `0 < w₃(p) ≤ 1`.

## Implementation notes

The level `n`, the residue `ξ` and the threshold `ε` are explicit arguments. As for `IsBkWhite`,
the factor is defined for every `p : ℤ × ℤ`, rather than only for `p ∈ 𝒫`. The rational constants
`κ_*` and `z_*` are cast to `ℝ` in the exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The raw-three factor `w₃(p)`: `e^{-κ_* z_*}` if `p` is white for `n, ξ, ε`, and `1`
otherwise. -/
@[collatz_pos_dens "def_ch_raw3_factor"]
noncomputable def chRaw3Factor (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℝ :=
  if IsBkWhite n ξ ε p then Real.exp (-((kappaStar : ℝ) * zStar)) else 1

/-- The exponent of the raw-three factor: `κ_* z_* = 21/3125`. -/
theorem chRaw3Factor_exponent : (kappaStar : ℝ) * zStar = 21 / 3125 := by
  rw [zStar_cast, kappaStar_def]; norm_num

/-- The raw-three factor of a white point is `e^{-κ_* z_*}`. -/
theorem chRaw3Factor_of_isBkWhite {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) :
    chRaw3Factor n ξ ε p = Real.exp (-((kappaStar : ℝ) * zStar)) := by
  simp [chRaw3Factor, h]

/-- The raw-three factor of a white point is `e^{-21/3125}`. -/
theorem chRaw3Factor_of_isBkWhite' {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) : chRaw3Factor n ξ ε p = Real.exp (-(21 / 3125)) := by
  rw [chRaw3Factor_of_isBkWhite h, chRaw3Factor_exponent]

/-- The raw-three factor of a non-white point is `1`. -/
theorem chRaw3Factor_of_not_isBkWhite {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : ¬ IsBkWhite n ξ ε p) : chRaw3Factor n ξ ε p = 1 := by
  simp [chRaw3Factor, h]

/-- The raw-three factor is positive. -/
theorem chRaw3Factor_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    0 < chRaw3Factor n ξ ε p := by
  unfold chRaw3Factor
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

/-- The raw-three factor is nonnegative. -/
theorem chRaw3Factor_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    0 ≤ chRaw3Factor n ξ ε p :=
  (chRaw3Factor_pos n ξ ε p).le

/-- The raw-three factor is at most `1`. -/
theorem chRaw3Factor_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    chRaw3Factor n ξ ε p ≤ 1 := by
  unfold chRaw3Factor
  split_ifs
  · rw [chRaw3Factor_exponent, Real.exp_le_one_iff]; norm_num
  · exact le_rfl

end CollatzPosDens
