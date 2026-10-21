/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Ycl
public import CollatzPosDens.Transfer.S02Vcl
public import CollatzPosDens.Transfer.S02HDef
public import CollatzPosDens.Transfer.S02S
public import CollatzPosDens.Transfer.S02Schedule
public import Mathlib.Data.Rat.Cast.Order

/-!
# The clearing exponents `t^cl_i`

For a Fourier index `ι ∈ {o, b}` and `0 ≤ i ≤ r_*(ι)`, the `i`-th clearing exponent is the
rational number
$$t^{\mathrm{cl}}_i(ι) := \bigl(1 - y_{\mathrm{cl}}(ι)\bigr)
  \Bigl(v_{\mathrm{cl}}(ι)\,h_*(ι, p_i(ι)) - \frac{13}{9}\,\mathsf S_i(ι)\Bigr),$$
where `y_cl(ι)` is the clearing point, `v_cl(ι)` the clearing exponent of the clearing estimate,
`h_*(ι, ·)` the window length, `p_i(ι)` the `i`-th schedule position and `S_i(ι)` the `i`-th
interval size of the trace schedule. Since `1 - y_cl(o) = 1/8192`, `v_cl(o) = 1279/100`,
`1 - y_cl(b) = 1/256` and `v_cl(b) = 25/2`,
$$t^{\mathrm{cl}}_i(\mathrm o) = \frac{1}{8192}\Bigl(\frac{1279}{100}h_*(\mathrm o, p_i)
  - \frac{13}{9}\mathsf S_i\Bigr), \qquad
  t^{\mathrm{cl}}_i(\mathrm b) = \frac{1}{256}\Bigl(\frac{25}{2}h_*(\mathrm b, p_i)
  - \frac{13}{9}\mathsf S_i\Bigr).$$

## Main definitions

* `CollatzPosDens.clearingExponent`: the clearing exponent `t^cl_i(ι)`, indexed by
  `ι : FIndex` and `i : ℕ`.

## Main results

* `CollatzPosDens.clearingExponent_def`: the defining formula of `t^cl_i(ι)`.
* `CollatzPosDens.clearingExponent_o`, `CollatzPosDens.clearingExponent_b`: the formula at each
  index with the constants evaluated.
* `CollatzPosDens.clearingExponent_cast`: the defining formula after casting to a field of
  characteristic zero, e.g. `ℝ`.

## Implementation notes

The clearing exponents are only meaningful for `0 ≤ i ≤ r_*(ι)`. The definition is total on
`ℕ`, since `h_*`, `p_i` and `S_i` are. Because `h_*` is defined through a real ceiling, the
definition is `noncomputable`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clearing exponents
`t^cl_i(ι) := (1 - y_cl(ι)) (v_cl(ι) h_*(ι, p_i(ι)) - 13/9 · S_i(ι)) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_clear_exp"]
noncomputable def clearingExponent (ι : FIndex) (i : ℕ) : ℚ :=
  (1 - clearingPoint ι) *
    (clearingPower ι * (windowLength ι (schedule ι i) : ℚ) - 13 / 9 * (sStar ι i : ℚ))

/-- The defining formula
`t^cl_i(ι) = (1 - y_cl(ι)) (v_cl(ι) h_*(ι, p_i(ι)) - 13/9 · S_i(ι))`. -/
theorem clearingExponent_def (ι : FIndex) (i : ℕ) :
    clearingExponent ι i =
      (1 - clearingPoint ι) *
        (clearingPower ι * (windowLength ι (schedule ι i) : ℚ) - 13 / 9 * (sStar ι i : ℚ)) :=
  rfl

/-- At the original index,
`t^cl_i(o) = (1279/100 · h_*(o, p_i(o)) - 13/9 · S_i(o)) / 8192`. -/
theorem clearingExponent_o (i : ℕ) :
    clearingExponent .o i =
      (1279 / 100 * (windowLength .o (schedule .o i) : ℚ) - 13 / 9 * (sStar .o i : ℚ)) /
        8192 := by
  rw [clearingExponent_def, one_sub_clearingPoint_o, clearingPower_o]
  ring

/-- At the bootstrap index,
`t^cl_i(b) = (25/2 · h_*(b, p_i(b)) - 13/9 · S_i(b)) / 256`. -/
theorem clearingExponent_b (i : ℕ) :
    clearingExponent .b i =
      (25 / 2 * (windowLength .b (schedule .b i) : ℚ) - 13 / 9 * (sStar .b i : ℚ)) / 256 := by
  rw [clearingExponent_def, one_sub_clearingPoint_b, clearingPower_b]
  ring

/-- The defining formula of `t^cl_i(ι)`, cast to a field of characteristic zero (typically
`ℝ`). -/
theorem clearingExponent_cast {K : Type*} [Field K] [CharZero K] (ι : FIndex) (i : ℕ) :
    ((clearingExponent ι i : ℚ) : K) =
      (1 - (clearingPoint ι : K)) *
        ((clearingPower ι : K) * (windowLength ι (schedule ι i) : K) -
          13 / 9 * (sStar ι i : K)) := by
  rw [clearingExponent_def]
  push_cast
  ring

end CollatzPosDens
