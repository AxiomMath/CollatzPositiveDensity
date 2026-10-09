/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLevel

/-!
# The lower window end `q^-_n`

For an integer `n ≥ 1` this file defines the integer
$$q^-_n = \left\lfloor \tfrac12 \mathrm{Lv}_n - \tfrac14 n^{2049/4096} \right\rfloor,$$
where `Lv_n` is the crossing level `CollatzPosDens.mxLevel`.

## Main definitions

* `CollatzPosDens.mxWindowLow`: the lower window end `q^-_n`.

## Main results

* `CollatzPosDens.mxWindowLow_def`: the defining formula.
* `CollatzPosDens.mxWindowLow_le`: `q^-_n ≤ Lv_n / 2 - n^{2049/4096} / 4`.
* `CollatzPosDens.lt_mxWindowLow`: `Lv_n / 2 - n^{2049/4096} / 4 - 1 < q^-_n`.
* `CollatzPosDens.le_mxWindowLow_iff`: `z ≤ q^-_n ↔ z ≤ Lv_n / 2 - n^{2049/4096} / 4`.
* `CollatzPosDens.mxWindowLow_lt_iff`: `q^-_n < z ↔ Lv_n / 2 - n^{2049/4096} / 4 < z`.

## Implementation notes

The definition is stated for every natural number `n`, with the power `n^{2049/4096}` taken as
`Real.rpow`; at `n = 0` it takes a junk value. The hypothesis `n ≥ 1` is carried by the lemmas
that need it.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The lower window end `q^-_n = ⌊Lv_n / 2 - n^{2049/4096} / 4⌋`, meaningful for `n ≥ 1`. -/
@[collatz_pos_dens "def_mx_window_low"]
noncomputable def mxWindowLow (n : ℕ) : ℤ :=
  ⌊(1 / 2 : ℝ) * mxLevel n - (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096)⌋

/-- The defining formula of `mxWindowLow`. -/
theorem mxWindowLow_def (n : ℕ) :
    mxWindowLow n =
      ⌊(1 / 2 : ℝ) * mxLevel n - (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096)⌋ := rfl

/-- The lower window end is dominated by the real quantity it rounds down. -/
theorem mxWindowLow_le (n : ℕ) :
    (mxWindowLow n : ℝ) ≤ (1 / 2 : ℝ) * mxLevel n - (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) :=
  Int.floor_le _

/-- The lower window end falls short of the real quantity it rounds down by less than one. -/
theorem lt_mxWindowLow (n : ℕ) :
    (1 / 2 : ℝ) * mxLevel n - (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) - 1 < mxWindowLow n :=
  Int.sub_one_lt_floor _

/-- Characterisation of `z ≤ q^-_n` for an integer `z`. -/
theorem le_mxWindowLow_iff (n : ℕ) (z : ℤ) :
    z ≤ mxWindowLow n ↔
      (z : ℝ) ≤ (1 / 2 : ℝ) * mxLevel n - (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) :=
  Int.le_floor

/-- Characterisation of `q^-_n < z` for an integer `z`. -/
theorem mxWindowLow_lt_iff (n : ℕ) (z : ℤ) :
    mxWindowLow n < z ↔
      (1 / 2 : ℝ) * mxLevel n - (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) < z :=
  Int.floor_lt

end CollatzPosDens
