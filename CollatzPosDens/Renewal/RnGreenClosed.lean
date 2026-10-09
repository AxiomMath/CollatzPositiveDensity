/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass

/-!
# The closed form of the Green's function

For `(j, s) ∈ ℤ × ℤ` the closed-form Green's function is
`𝒢ᶜˡ(j, s) = ϖ(4) 𝖱(j - 1, s - 4) + ϖ(5) 𝖱(j - 1, s - 5)` when `j ≥ 1`, `𝒢ᶜˡ(0, 0) = 1`, and
`𝒢ᶜˡ(j, s) = 0` otherwise. Here `ϖ` is the Pascal holding-time law and `𝖱` the raw-prefix
mass. For `j ≥ 1` this is the total weight of the words of length `j` with letters `≥ 2`,
letter sum `s` and last letter in `{4, 5}`, split according to the last letter.

## Main definitions

* `CollatzPosDens.greenClosed`: the closed form `𝒢ᶜˡ : ℤ → ℤ → ℝ`.

## Main results

* `CollatzPosDens.greenClosed_of_one_le`, `CollatzPosDens.greenClosed_zero_zero`,
  `CollatzPosDens.greenClosed_of_nonpos`: the three cases of the definition.
* `CollatzPosDens.greenClosed_succ`: the value at `j = k + 1` for `k ∈ ℕ`.
* `CollatzPosDens.greenClosed_zero`: `𝒢ᶜˡ(0, s) = [s = 0]`.
* `CollatzPosDens.greenClosed_of_neg`: `𝒢ᶜˡ(j, s) = 0` for `j < 0`.
* `CollatzPosDens.greenClosed_nonneg`: the closed form is nonnegative.

## Implementation notes

The raw-prefix mass `𝖱(k, t)` is indexed by a natural length `k`; in the case `j ≥ 1` the
length `j - 1` is nonnegative, and is passed as `(j - 1).toNat`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The closed form `𝒢ᶜˡ(j, s)` of the Green's function:
`ϖ(4) 𝖱(j - 1, s - 4) + ϖ(5) 𝖱(j - 1, s - 5)` if `j ≥ 1`, `1` at `(0, 0)`, and `0` otherwise. -/
@[collatz_pos_dens "def_rn_green_closed"]
noncomputable def greenClosed (j s : ℤ) : ℝ :=
  if 1 ≤ j then varpi 4 * rawMass (j - 1).toNat (s - 4) + varpi 5 * rawMass (j - 1).toNat (s - 5)
  else if j = 0 ∧ s = 0 then 1
  else 0

/-- For `j ≥ 1`, `𝒢ᶜˡ(j, s) = ϖ(4) 𝖱(j - 1, s - 4) + ϖ(5) 𝖱(j - 1, s - 5)`. -/
theorem greenClosed_of_one_le {j : ℤ} (hj : 1 ≤ j) (s : ℤ) :
    greenClosed j s =
      varpi 4 * rawMass (j - 1).toNat (s - 4) + varpi 5 * rawMass (j - 1).toNat (s - 5) := by
  simp [greenClosed, hj]

/-- `𝒢ᶜˡ(k + 1, s) = ϖ(4) 𝖱(k, s - 4) + ϖ(5) 𝖱(k, s - 5)` for `k ∈ ℕ`. -/
theorem greenClosed_succ (k : ℕ) (s : ℤ) :
    greenClosed ((k : ℤ) + 1) s = varpi 4 * rawMass k (s - 4) + varpi 5 * rawMass k (s - 5) := by
  rw [greenClosed_of_one_le (by omega)]
  simp

/-- `𝒢ᶜˡ(0, 0) = 1`. -/
theorem greenClosed_zero_zero : greenClosed 0 0 = 1 := by
  simp [greenClosed]

/-- For `j ≤ 0`, `𝒢ᶜˡ(j, s)` is `1` at `(0, 0)` and `0` otherwise. -/
theorem greenClosed_of_nonpos {j : ℤ} (hj : j ≤ 0) (s : ℤ) :
    greenClosed j s = if j = 0 ∧ s = 0 then 1 else 0 := by
  simp [greenClosed, show ¬ 1 ≤ j by omega]

/-- `𝒢ᶜˡ(0, s) = [s = 0]`. -/
@[simp] theorem greenClosed_zero (s : ℤ) : greenClosed 0 s = if s = 0 then 1 else 0 := by
  simp [greenClosed_of_nonpos le_rfl]

/-- `𝒢ᶜˡ(j, s) = 0` for `j < 0`. -/
theorem greenClosed_of_neg {j : ℤ} (hj : j < 0) (s : ℤ) : greenClosed j s = 0 := by
  simp [greenClosed_of_nonpos hj.le, hj.ne]

/-- The closed-form Green's function is nonnegative. -/
theorem greenClosed_nonneg (j s : ℤ) : 0 ≤ greenClosed j s := by
  unfold greenClosed
  split_ifs
  · exact add_nonneg (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _))
      (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _))
  · exact zero_le_one
  · exact le_rfl

end CollatzPosDens
