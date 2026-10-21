/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Mixing.MxShWidth
public import CollatzPosDens.Mixing.MxShKhi

/-!
# The lower end of the shell window

For an integer `n ≥ 1` the lower end of the shell window is the integer
$$k^{\mathrm{sh},-}_n = \lfloor H^{\mathrm{sh}}_n / 2 - h^{\mathrm{sh}}_n \rfloor,$$
where `H^{sh}_n = shHeight n` is the crossing height and `h^{sh}_n = shWidth n` the half-width of
the window. Since both are natural numbers, the floor only rounds the half `H^{sh}_n / 2`, and
`k^{sh,-}_n = ⌊H^{sh}_n / 2⌋ - h^{sh}_n = H^{sh}_n / 2 - h^{sh}_n` (natural division, integer
subtraction).

## Main definitions

* `CollatzPosDens.shKLo`: the lower end `k^{sh,-}_n`.

## Main results

* `CollatzPosDens.shKLo_def`: the defining formula.
* `CollatzPosDens.shKLo_le`, `CollatzPosDens.lt_shKLo`:
  `H^{sh}_n / 2 - h^{sh}_n - 1 < k^{sh,-}_n ≤ H^{sh}_n / 2 - h^{sh}_n`.
* `CollatzPosDens.le_shKLo_iff`: `m ≤ k^{sh,-}_n ↔ m ≤ H^{sh}_n / 2 - h^{sh}_n`.
* `CollatzPosDens.shKLo_eq`: the closed form `k^{sh,-}_n = H^{sh}_n / 2 - h^{sh}_n`.
* `CollatzPosDens.shKLo_le_shKHi`: `k^{sh,-}_n ≤ k^{sh,+}_n`, where `k^{sh,+}_n = shKHi n` is the
  upper end of the window.

## Implementation notes

The definition is stated for every natural number `n`; the hypothesis `n ≥ 1` is carried by the
lemmas that use it. The value is an integer, so that it can be compared directly with integer
offsets and may be negative.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

/-- The lower end `k^{sh,-}_n = ⌊H^{sh}_n / 2 - h^{sh}_n⌋ ∈ ℤ` of the shell window, meaningful for
`n ≥ 1`. -/
@[collatz_pos_dens "def_mx_sh_klo"]
noncomputable def shKLo (n : ℕ) : ℤ :=
  ⌊(shHeight n : ℝ) / 2 - shWidth n⌋

/-- The defining formula of `shKLo`. -/
theorem shKLo_def (n : ℕ) : shKLo n = ⌊(shHeight n : ℝ) / 2 - shWidth n⌋ := rfl

/-- `k^{sh,-}_n ≤ H^{sh}_n / 2 - h^{sh}_n`. -/
theorem shKLo_le (n : ℕ) : (shKLo n : ℝ) ≤ (shHeight n : ℝ) / 2 - shWidth n :=
  Int.floor_le _

/-- `H^{sh}_n / 2 - h^{sh}_n - 1 < k^{sh,-}_n`. -/
theorem lt_shKLo (n : ℕ) : (shHeight n : ℝ) / 2 - shWidth n - 1 < shKLo n :=
  Int.sub_one_lt_floor _

/-- `m ≤ k^{sh,-}_n` exactly when `m ≤ H^{sh}_n / 2 - h^{sh}_n`. -/
theorem le_shKLo_iff (n : ℕ) (m : ℤ) :
    m ≤ shKLo n ↔ (m : ℝ) ≤ (shHeight n : ℝ) / 2 - shWidth n :=
  Int.le_floor

/-- The closed form `k^{sh,-}_n = ⌊H^{sh}_n / 2⌋ - h^{sh}_n = H^{sh}_n / 2 - h^{sh}_n`, with
natural division and integer subtraction. -/
theorem shKLo_eq (n : ℕ) : shKLo n = ((shHeight n / 2 : ℕ) : ℤ) - shWidth n := by
  rw [shKLo_def, Int.floor_sub_natCast, sub_left_inj, Int.floor_eq_iff]
  set H := shHeight n
  obtain ⟨q, hq | hq⟩ : ∃ q, H = 2 * q ∨ H = 2 * q + 1 := ⟨H / 2, by omega⟩
  · have hd : H / 2 = q := by omega
    rw [hd, hq]
    push_cast
    constructor <;> linarith
  · have hd : H / 2 = q := by omega
    rw [hd, hq]
    push_cast
    constructor <;> linarith

/-- `k^{sh,-}_n ≤ k^{sh,+}_n`. -/
theorem shKLo_le_shKHi (n : ℕ) : shKLo n ≤ shKHi n := by
  rw [shKLo_eq, shKHi_eq]
  push_cast
  omega

end CollatzPosDens
