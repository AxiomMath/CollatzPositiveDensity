/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import CollatzPosDens.Attr

/-!
# The signed fractional part on `ZMod N`

For `N ≥ 1` and `z : ZMod N`, let `v ∈ ℤ` be the unique representative of `z` with
`-N < 2v ≤ N`. The *signed fractional part* of `z` is `sfr z := v / N`, a real number in
`(-1/2, 1/2]`.

## Main definitions

* `CollatzPosDens.sfr`: the signed fractional part `z.valMinAbs / N` of `z : ZMod N`.

## Main results

* `CollatzPosDens.sfr_eq_of_spec`: `sfr z = v / N` for the unique `v` with `(v : ZMod N) = z`
  and `-N < 2v ≤ N`.
* `CollatzPosDens.sfr_mem_Ioc`: `sfr z ∈ (-1/2, 1/2]`.

## Implementation notes

The representative `v` is Mathlib's `ZMod.valMinAbs`, characterised by `ZMod.valMinAbs_spec`.
The source assumes `N` odd; oddness is not needed for the definition or for the range
statement, only `N ≠ 0`, so it is dropped here.

## References

* [Mazur, *Collatz positive density*], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The signed fractional part of `z : ZMod N`: `v / N`, where `v = z.valMinAbs` is the unique
integer representative of `z` with `-N < 2v ≤ N`. -/
@[collatz_pos_dens "def_bk_signed_frac"]
noncomputable def sfr {N : ℕ} (z : ZMod N) : ℝ := (z.valMinAbs : ℝ) / N

/-- Unfolding lemma for `sfr`. -/
lemma sfr_def {N : ℕ} (z : ZMod N) : sfr z = (z.valMinAbs : ℝ) / N := rfl

/-- `sfr z = v / N` for any integer `v` representing `z` with `-N < 2v ≤ N`. -/
lemma sfr_eq_of_spec {N : ℕ} [NeZero N] {z : ZMod N} {v : ℤ} (hv : (v : ZMod N) = z)
    (h₁ : -(N : ℤ) < 2 * v) (h₂ : 2 * v ≤ N) : sfr z = (v : ℝ) / N := by
  rw [sfr_def, (ZMod.valMinAbs_spec z v).2 ⟨hv.symm, mul_comm v 2 ▸ h₁, mul_comm v 2 ▸ h₂⟩]

/-- The signed fractional part lies in `(-1/2, 1/2]`. -/
@[collatz_pos_dens "def_bk_signed_frac"]
theorem sfr_mem_Ioc {N : ℕ} [NeZero N] (z : ZMod N) :
    sfr z ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
  obtain ⟨-, h₁, h₂⟩ := (ZMod.valMinAbs_spec z z.valMinAbs).1 rfl
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h₁' : -(N : ℝ) < z.valMinAbs * 2 := by exact_mod_cast h₁
  have h₂' : (z.valMinAbs : ℝ) * 2 ≤ N := by exact_mod_cast h₂
  rw [sfr_def]
  constructor
  · rw [lt_div_iff₀ hN]; linarith
  · rw [div_le_iff₀ hN]; linarith

end CollatzPosDens
