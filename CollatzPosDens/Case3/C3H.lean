/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChWhiteFactor

/-!
# The penalty without the starting white factor

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a point `v ∈ 𝒫` the *penalty
without the starting white factor* is `H(v) := Q(v) / w(v)`, the renewal function `Q` divided by
the white factor `w`. Since `w(v) > 0`, this is equivalent to `Q(v) = w(v) H(v)`.

## Main definitions

* `CollatzPosDens.c3H n ξ ε v`: the function `H(v) = Q(v) / w(v)`.

## Main results

* `CollatzPosDens.c3H_def`: the defining equation `H(v) = Q(v) / w(v)`.
* `CollatzPosDens.chWhiteFactor_mul_c3H`: `w(v) H(v) = Q(v)`.
* `CollatzPosDens.c3H_nonneg`: `H(v) ≥ 0`.

## Implementation notes

As for `chQ` and `chWhiteFactor`, the point `v` ranges over all of `ℤ × ℤ`, not only over
`𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The penalty without the starting white factor, `H(v) := Q(v) / w(v)`, for `n, ξ, ε`. -/
@[collatz_pos_dens "def_c3_H"]
noncomputable def c3H (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) : ℝ :=
  chQ n ξ ε v / chWhiteFactor n ξ ε v

/-- Unfolding lemma for `c3H`: `H(v) = Q(v) / w(v)`. -/
theorem c3H_def (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    c3H n ξ ε v = chQ n ξ ε v / chWhiteFactor n ξ ε v :=
  rfl

/-- The renewal function factors as `Q(v) = w(v) H(v)`. -/
theorem chWhiteFactor_mul_c3H (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    chWhiteFactor n ξ ε v * c3H n ξ ε v = chQ n ξ ε v :=
  mul_div_cancel₀ _ (chWhiteFactor_pos n ξ ε v).ne'

/-- The renewal function factors as `Q(v) = H(v) w(v)`. -/
theorem c3H_mul_chWhiteFactor (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    c3H n ξ ε v * chWhiteFactor n ξ ε v = chQ n ξ ε v :=
  div_mul_cancel₀ _ (chWhiteFactor_pos n ξ ε v).ne'

/-- `H(v) = Q(v)` at a point that is not white. -/
theorem c3H_of_not_isBkWhite {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {v : ℤ × ℤ}
    (h : ¬ IsBkWhite n ξ ε v) : c3H n ξ ε v = chQ n ξ ε v := by
  rw [c3H_def, chWhiteFactor_of_not_isBkWhite h, div_one]

/-- `H(v) = e^{z_*} Q(v)` at a white point. -/
theorem c3H_of_isBkWhite {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {v : ℤ × ℤ}
    (h : IsBkWhite n ξ ε v) : c3H n ξ ε v = Real.exp (zStar : ℝ) * chQ n ξ ε v := by
  rw [c3H_def, chWhiteFactor_of_isBkWhite h, Real.exp_neg, div_inv_eq_mul, mul_comm]

/-- `H(v)` is nonnegative. -/
theorem c3H_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) : 0 ≤ c3H n ξ ε v :=
  div_nonneg (chQ_nonneg _ _ _ _) (chWhiteFactor_nonneg _ _ _ _)

/-- `Q(v) ≤ H(v)`, since `w(v) ≤ 1`. -/
theorem chQ_le_c3H (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    chQ n ξ ε v ≤ c3H n ξ ε v := by
  rw [← chWhiteFactor_mul_c3H n ξ ε v]
  exact mul_le_of_le_one_left (c3H_nonneg n ξ ε v) (chWhiteFactor_le_one n ξ ε v)

end CollatzPosDens
