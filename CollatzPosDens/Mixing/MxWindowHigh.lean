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
# The upper window end `q^+_n`

For an integer `n ≥ 1` this file defines the integer
$$q^+_n = \left\lceil \tfrac12 \mathrm{Lv}_n + \tfrac14 n^{2049/4096} \right\rceil,$$
where `Lv_n` is the crossing level `CollatzPosDens.mxLevel`. It is the upper end of a window
of levels around `Lv_n / 2`.

## Main definitions

* `CollatzPosDens.mxWindowHigh`: the upper window end `q^+_n`.

## Main results

* `CollatzPosDens.mxWindowHigh_def`: the defining formula.
* `CollatzPosDens.le_mxWindowHigh`: `Lv_n / 2 + n^{2049/4096} / 4 ≤ q^+_n`.
* `CollatzPosDens.mxWindowHigh_lt`: `q^+_n < Lv_n / 2 + n^{2049/4096} / 4 + 1`.
* `CollatzPosDens.mxWindowHigh_le_iff`: `q^+_n ≤ z ↔ Lv_n / 2 + n^{2049/4096} / 4 ≤ z`.
* `CollatzPosDens.lt_mxWindowHigh_iff`: `z < q^+_n ↔ z < Lv_n / 2 + n^{2049/4096} / 4`.

## Implementation notes

The definition is stated for every natural number `n`, with the power `n^{2049/4096}` taken as
`Real.rpow`; at `n = 0` it takes a junk value. The hypothesis `n ≥ 1` is carried by the lemmas
that use it.
-/

@[expose] public section

namespace CollatzPosDens

/-- The upper window end `q^+_n = ⌈Lv_n / 2 + n^{2049/4096} / 4⌉`, meaningful for `n ≥ 1`. -/
@[collatz_pos_dens "def_mx_window_high"]
noncomputable def mxWindowHigh (n : ℕ) : ℤ :=
  ⌈(1 / 2 : ℝ) * mxLevel n + (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096)⌉

/-- The defining formula of `mxWindowHigh`. -/
theorem mxWindowHigh_def (n : ℕ) :
    mxWindowHigh n =
      ⌈(1 / 2 : ℝ) * mxLevel n + (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096)⌉ := rfl

/-- The upper window end dominates the real quantity it rounds up. -/
theorem le_mxWindowHigh (n : ℕ) :
    (1 / 2 : ℝ) * mxLevel n + (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) ≤ mxWindowHigh n :=
  Int.le_ceil _

/-- The upper window end exceeds the real quantity it rounds up by less than one. -/
theorem mxWindowHigh_lt (n : ℕ) :
    (mxWindowHigh n : ℝ) <
      (1 / 2 : ℝ) * mxLevel n + (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) + 1 :=
  Int.ceil_lt_add_one _

/-- Characterisation of `q^+_n ≤ z` for an integer `z`. -/
theorem mxWindowHigh_le_iff (n : ℕ) (z : ℤ) :
    mxWindowHigh n ≤ z ↔
      (1 / 2 : ℝ) * mxLevel n + (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) ≤ z :=
  Int.ceil_le

/-- Characterisation of `z < q^+_n` for an integer `z`. -/
theorem lt_mxWindowHigh_iff (n : ℕ) (z : ℤ) :
    z < mxWindowHigh n ↔
      (z : ℝ) < (1 / 2 : ℝ) * mxLevel n + (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) :=
  Int.lt_ceil

end CollatzPosDens
