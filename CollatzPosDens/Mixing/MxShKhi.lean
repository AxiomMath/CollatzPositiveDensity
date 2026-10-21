/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Mixing.MxShWidth

/-!
# The upper end of the shell window

For an integer `n ≥ 1` the upper end of the shell window of the degree cut with colliding heads is
the integer
$$k^{\mathrm{sh},+}_n = \lceil H^{\mathrm{sh}}_n / 2 + h^{\mathrm{sh}}_n \rceil,$$
where `H^{sh}_n = shHeight n` is the crossing height and `h^{sh}_n = shWidth n` the half-width of
the window. Since both are natural numbers, the ceiling only rounds the half `H^{sh}_n / 2`, and
`k^{sh,+}_n = ⌈H^{sh}_n / 2⌉ + h^{sh}_n = (H^{sh}_n + 1) / 2 + h^{sh}_n` (natural division).

## Main definitions

* `CollatzPosDens.shKHi`: the upper end `k^{sh,+}_n`.

## Main results

* `CollatzPosDens.shKHi_def`: the defining formula.
* `CollatzPosDens.le_shKHi`, `CollatzPosDens.shKHi_lt`:
  `H^{sh}_n / 2 + h^{sh}_n ≤ k^{sh,+}_n < H^{sh}_n / 2 + h^{sh}_n + 1`.
* `CollatzPosDens.shKHi_le_iff`: `k^{sh,+}_n ≤ m ↔ H^{sh}_n / 2 + h^{sh}_n ≤ m`.
* `CollatzPosDens.shKHi_eq`: the closed form `k^{sh,+}_n = (H^{sh}_n + 1) / 2 + h^{sh}_n`.
* `CollatzPosDens.shKHi_nonneg`: `0 ≤ k^{sh,+}_n`.

## Implementation notes

The definition is stated for every natural number `n`, although it is only meaningful for
`n ≥ 1`; that hypothesis belongs to the lemmas that use it. The value is an integer so that it
can be compared directly with integer offsets.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

/-- The upper end `k^{sh,+}_n = ⌈H^{sh}_n / 2 + h^{sh}_n⌉ ∈ ℤ` of the shell window, meaningful for
`n ≥ 1`. -/
@[collatz_pos_dens "def_mx_sh_khi"]
noncomputable def shKHi (n : ℕ) : ℤ :=
  ⌈(shHeight n : ℝ) / 2 + shWidth n⌉

/-- The defining formula of `shKHi`. -/
theorem shKHi_def (n : ℕ) : shKHi n = ⌈(shHeight n : ℝ) / 2 + shWidth n⌉ := rfl

/-- `H^{sh}_n / 2 + h^{sh}_n ≤ k^{sh,+}_n`. -/
theorem le_shKHi (n : ℕ) : (shHeight n : ℝ) / 2 + shWidth n ≤ shKHi n :=
  Int.le_ceil _

/-- `k^{sh,+}_n < H^{sh}_n / 2 + h^{sh}_n + 1`. -/
theorem shKHi_lt (n : ℕ) : (shKHi n : ℝ) < (shHeight n : ℝ) / 2 + shWidth n + 1 :=
  Int.ceil_lt_add_one _

/-- `k^{sh,+}_n ≤ m` exactly when `H^{sh}_n / 2 + h^{sh}_n ≤ m`. -/
theorem shKHi_le_iff (n : ℕ) (m : ℤ) :
    shKHi n ≤ m ↔ (shHeight n : ℝ) / 2 + shWidth n ≤ m :=
  Int.ceil_le

/-- The closed form `k^{sh,+}_n = ⌈H^{sh}_n / 2⌉ + h^{sh}_n = (H^{sh}_n + 1) / 2 + h^{sh}_n`. -/
theorem shKHi_eq (n : ℕ) : shKHi n = (((shHeight n + 1) / 2 + shWidth n : ℕ) : ℤ) := by
  rw [shKHi_def, Int.ceil_add_natCast, Nat.cast_add, add_left_inj, Int.ceil_eq_iff]
  set H := shHeight n
  obtain ⟨q, hq | hq⟩ : ∃ q, H = 2 * q ∨ H = 2 * q + 1 := ⟨H / 2, by omega⟩
  · have hd : (H + 1) / 2 = q := by omega
    rw [hd, hq]
    push_cast
    constructor <;> linarith
  · have hd : (H + 1) / 2 = q + 1 := by omega
    rw [hd, hq]
    push_cast
    constructor <;> linarith

/-- `0 ≤ k^{sh,+}_n`. -/
theorem shKHi_nonneg (n : ℕ) : 0 ≤ shKHi n := by
  rw [shKHi_eq]
  exact Int.natCast_nonneg _

end CollatzPosDens
