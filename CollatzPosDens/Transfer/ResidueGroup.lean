/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.ZMod.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr

/-!
# The ternary residue space

For `q : ℕ` the ternary residue space is `G_q = ℤ/3^qℤ`, viewed as a finite probability space
with the uniform measure. The average of a real-valued function `f : G_q → ℝ` is
`⟨f⟩_q = 3^{-q} ∑_{y ∈ G_q} f y`. A residue `y` is a *unit* when `3 ∤ ỹ`, where `ỹ` is its least
nonnegative representative in `{0, …, 3^q - 1}`, and a *nonunit* otherwise.

## Main definitions

* `CollatzPosDens.ResidueGroup q`: the ring `ZMod (3 ^ q)`.
* `CollatzPosDens.residueAvg q f`: the uniform average `3^{-q} ∑ y, f y`.
* `CollatzPosDens.IsResidueUnit y`: the residue `y` is not divisible by `3`.

## Main results

* `CollatzPosDens.isResidueUnit_iff_isUnit`: for `q ≥ 1`, `y` is a residue unit exactly when it
  is a unit of the ring `ZMod (3 ^ q)`.
* `CollatzPosDens.residueAvg_const`: the average of a constant is that constant.
* `CollatzPosDens.residueAvg_add`, `residueAvg_sub`, `residueAvg_sum`, `residueAvg_mono`:
  the average is linear and monotone.
* `CollatzPosDens.three_pow_self_residueGroup`: `3^k = 0` in `G_k`.

## Implementation notes

The least nonnegative representative `ỹ` is Mathlib's `ZMod.val`;
`CollatzPosDens.val_lt_three_pow` records that it lies in `{0, …, 3^q - 1}`. The unit
predicate is stated through `ZMod.val`, as in [mazur2026]; for `q = 0` it makes every residue a
nonunit, while [mazur2026] only uses it for `q ≥ 1`, where it agrees with `IsUnit`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The ternary residue space `G_q = ℤ/3^qℤ`. -/
@[collatz_pos_dens "def_residue_group"]
abbrev ResidueGroup (q : ℕ) : Type := ZMod (3 ^ q)

/-- The uniform average `⟨f⟩_q = 3^{-q} ∑_{y ∈ G_q} f y` of a real function on `G_q`. -/
@[collatz_pos_dens "def_residue_group"]
noncomputable def residueAvg (q : ℕ) (f : ResidueGroup q → ℝ) : ℝ :=
  (3 : ℝ) ^ (-(q : ℤ)) * ∑ y, f y

/-- A residue `y ∈ G_q` is a *unit* if `3` does not divide its least nonnegative
representative `y.val`, and a *nonunit* otherwise. -/
@[collatz_pos_dens "def_residue_group"]
def IsResidueUnit {q : ℕ} (y : ResidueGroup q) : Prop :=
  ¬ 3 ∣ y.val

/-- Being a residue unit is decidable, by deciding whether `3` divides `y.val`. -/
instance {q : ℕ} (y : ResidueGroup q) : Decidable (IsResidueUnit y) :=
  inferInstanceAs (Decidable (¬ 3 ∣ y.val))

/-- A residue is a unit exactly when `3` does not divide its least nonnegative representative. -/
theorem isResidueUnit_iff {q : ℕ} {y : ResidueGroup q} : IsResidueUnit y ↔ ¬ 3 ∣ y.val :=
  Iff.rfl

/-- The least nonnegative representative of a residue lies in `{0, …, 3^q - 1}`. -/
theorem val_lt_three_pow {q : ℕ} (y : ResidueGroup q) : y.val < 3 ^ q :=
  ZMod.val_lt y

/-- The average written with `(3 ^ q)⁻¹` in place of `3 ^ (-q)`. -/
theorem residueAvg_def (q : ℕ) (f : ResidueGroup q → ℝ) :
    residueAvg q f = ((3 : ℝ) ^ q)⁻¹ * ∑ y, f y := by
  rw [residueAvg, zpow_neg, zpow_natCast]

/-- The average of a constant function is that constant. -/
@[simp]
theorem residueAvg_const (q : ℕ) (c : ℝ) : residueAvg q (fun _ => c) = c := by
  rw [residueAvg_def, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  push_cast
  field_simp

/-- The average is additive. -/
theorem residueAvg_add {q : ℕ} (f g : ResidueGroup q → ℝ) :
    residueAvg q (fun y => f y + g y) = residueAvg q f + residueAvg q g := by
  simp only [residueAvg_def, Finset.sum_add_distrib, mul_add]

/-- The average commutes with subtraction. -/
theorem residueAvg_sub {q : ℕ} (f g : ResidueGroup q → ℝ) :
    residueAvg q (fun y => f y - g y) = residueAvg q f - residueAvg q g := by
  simp only [residueAvg_def, Finset.sum_sub_distrib, mul_sub]

/-- The average commutes with finite sums. -/
theorem residueAvg_sum {q : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ResidueGroup q → ℝ) :
    residueAvg q (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, residueAvg q (f i) := by
  simp only [residueAvg_def, Finset.mul_sum]
  exact Finset.sum_comm

/-- The average is monotone. -/
theorem residueAvg_mono {q : ℕ} {f g : ResidueGroup q → ℝ} (h : ∀ y, f y ≤ g y) :
    residueAvg q f ≤ residueAvg q g := by
  rw [residueAvg_def, residueAvg_def]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => h y) (by positivity)

/-- For `q ≥ 1`, a residue is a unit in the sense of `IsResidueUnit` exactly when it is a unit of
the ring `ZMod (3 ^ q)`. -/
theorem isResidueUnit_iff_isUnit {q : ℕ} (hq : 1 ≤ q) (y : ResidueGroup q) :
    IsResidueUnit y ↔ IsUnit y := by
  conv_rhs => rw [← ZMod.natCast_zmod_val y]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hq, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd Nat.prime_three, isResidueUnit_iff]

/-- In `G_k`, `3^k = 0`. -/
theorem three_pow_self_residueGroup (k : ℕ) : (3 : ResidueGroup k) ^ k = 0 := by
  exact_mod_cast ZMod.natCast_self (3 ^ k)

end CollatzPosDens
