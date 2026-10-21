/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# The crossing height of the shell cut

For an integer `n ≥ 1` the crossing height of the shell cut is the natural number
$$H^{\mathrm{sh}}_n = \lceil n \log_2 3 \rceil,$$
the least exponent `k` with `3 ^ n ≤ 2 ^ k`.

## Main definitions

* `CollatzPosDens.shHeight`: the crossing height `H^{sh}_n`.

## Main results

* `CollatzPosDens.shHeight_def`: the defining formula.
* `CollatzPosDens.le_shHeight`, `CollatzPosDens.shHeight_lt`:
  `n log₂ 3 ≤ H^{sh}_n < n log₂ 3 + 1`.
* `CollatzPosDens.shHeight_le_iff`: `H^{sh}_n ≤ k` if and only if `3 ^ n ≤ 2 ^ k`.
* `CollatzPosDens.pow_three_le_two_pow_shHeight`: `3 ^ n ≤ 2 ^ H^{sh}_n`.
* `CollatzPosDens.two_pow_shHeight_sub_one_lt`: `2 ^ (H^{sh}_n - 1) < 3 ^ n` for `n ≥ 1`.
* `CollatzPosDens.shHeight_eq_iff`: `H^{sh}_n` is characterised, for `n ≥ 1`, as the unique
  `k ≥ 1` with `2 ^ (k - 1) < 3 ^ n ≤ 2 ^ k`.

## Implementation notes

The definition is stated for every natural number `n`; at `n = 0` it takes the value `0`. The
hypothesis `n ≥ 1` is carried by the lemmas that need it.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The crossing height `H^{sh}_n = ⌈n log₂ 3⌉` of the shell cut, meaningful for `n ≥ 1`. -/
@[collatz_pos_dens "def_mx_sh_H"]
noncomputable def shHeight (n : ℕ) : ℕ :=
  ⌈(n : ℝ) * Real.logb 2 3⌉₊

/-- The defining formula of `shHeight`. -/
theorem shHeight_def (n : ℕ) : shHeight n = ⌈(n : ℝ) * Real.logb 2 3⌉₊ := rfl

/-- The crossing height at `n = 0` is `0`. -/
@[simp]
theorem shHeight_zero : shHeight 0 = 0 := by
  simp [shHeight_def]

/-- `n log₂ 3 ≤ H^{sh}_n`. -/
theorem le_shHeight (n : ℕ) : (n : ℝ) * Real.logb 2 3 ≤ shHeight n :=
  Nat.le_ceil _

/-- `H^{sh}_n < n log₂ 3 + 1`. -/
theorem shHeight_lt (n : ℕ) : (shHeight n : ℝ) < n * Real.logb 2 3 + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _)
    (Real.logb_nonneg (by norm_num) (by norm_num)))

/-- For real `k`, `3 ^ n ≤ 2 ^ k` iff `n log₂ 3 ≤ k`. -/
private theorem pow_three_le_rpow_iff (n : ℕ) (k : ℝ) :
    (3 : ℝ) ^ n ≤ (2 : ℝ) ^ k ↔ (n : ℝ) * Real.logb 2 3 ≤ k := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  rw [← Real.logb_le_logb (b := 2) (by norm_num) h3 (by positivity), Real.logb_rpow (by norm_num)
    (by norm_num), Real.logb_pow]

/-- `3 ^ n ≤ 2 ^ k` iff `H^{sh}_n ≤ k`: the crossing height is the least such exponent. -/
theorem shHeight_le_iff (n k : ℕ) : shHeight n ≤ k ↔ 3 ^ n ≤ 2 ^ k := by
  rw [shHeight_def, Nat.ceil_le, ← pow_three_le_rpow_iff, Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- `3 ^ n ≤ 2 ^ H^{sh}_n`. -/
theorem pow_three_le_two_pow_shHeight (n : ℕ) : 3 ^ n ≤ 2 ^ shHeight n :=
  (shHeight_le_iff n _).1 le_rfl

/-- `H^{sh}_n ≥ 1` for `n ≥ 1`. -/
theorem one_le_shHeight {n : ℕ} (hn : 1 ≤ n) : 1 ≤ shHeight n := by
  by_contra h
  have h0 : shHeight n = 0 := by omega
  have := pow_three_le_two_pow_shHeight n
  rw [h0, pow_zero] at this
  have : 3 ≤ 3 ^ n := Nat.le_self_pow (by omega) 3
  omega

/-- `2 ^ (H^{sh}_n - 1) < 3 ^ n` for `n ≥ 1`. -/
theorem two_pow_shHeight_sub_one_lt {n : ℕ} (hn : 1 ≤ n) : 2 ^ (shHeight n - 1) < 3 ^ n := by
  have h1 := one_le_shHeight hn
  by_contra h
  have := (shHeight_le_iff n (shHeight n - 1)).2 (not_lt.1 h)
  omega

/-- For `n ≥ 1`, `H^{sh}_n` is the unique `k ≥ 1` with `2 ^ (k - 1) < 3 ^ n ≤ 2 ^ k`. -/
theorem shHeight_eq_iff {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    shHeight n = k ↔ 1 ≤ k ∧ 2 ^ (k - 1) < 3 ^ n ∧ 3 ^ n ≤ 2 ^ k := by
  constructor
  · rintro rfl
    exact ⟨one_le_shHeight hn, two_pow_shHeight_sub_one_lt hn,
      pow_three_le_two_pow_shHeight n⟩
  · rintro ⟨hk, hlt, hle⟩
    have h1 := (shHeight_le_iff n k).2 hle
    have h2 : ¬ shHeight n ≤ k - 1 := fun h => (not_le.2 hlt) ((shHeight_le_iff n _).1 h)
    omega

end CollatzPosDens
