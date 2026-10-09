/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Mixing.MxLevel
public import CollatzPosDens.Mixing.MxWindowLow
public import CollatzPosDens.Mixing.MxWindowHigh

/-!
# The good words `Gd_n`

For an integer `n ≥ 1`, the set `Gd_n` of *good words* consists of the words
`w ∈ ℤ_{≥1}^n` such that `off(w) ≤ n^{4609/4096}` and for some integer `i` with `1 ≤ i ≤ n`
and `q^-_n < i ≤ q^+_n` the prefix sums cross the level `Lv_n` at the `i`-th letter without
overshooting by much:
$$A(w_{\le i-1}) \le \mathrm{Lv}_n < A(w_{\le i})
  \le \lfloor \mathrm{Lv}_n \rfloor + 1 + \lceil \tfrac98 \log_2 n \rceil.$$
Here `Lv_n` is `mxLevel n`, `q^-_n` is `mxWindowLow n`, `q^+_n` is `mxWindowHigh n`, and `A`
is `Word.valSum`.

## Main definitions

* `CollatzPosDens.mxGood`: the set `Gd_n` of good words.

## Main results

* `CollatzPosDens.mem_mxGood`: the defining condition.
* `CollatzPosDens.length_of_mem_mxGood`: good words have length `n`.
* `CollatzPosDens.off_le_of_mem_mxGood`: good words have offset at most `n^{4609/4096}`.

## Implementation notes

Words are lists of positive integers, so membership in `ℤ_{≥1}^n` is the condition
`w.length = n`, and the prefix `w_{≤ i}` is `w.take i`. The index `i ≥ 1` is taken in `ℕ`;
the window condition compares it with the integers `q^±_n` in `ℤ`, the level conditions
compare valuation sums cast to `ℝ` with the real level `Lv_n`, and the overshoot bound is an
inequality in `ℤ`. The offset, a rational number, is cast to `ℝ` and compared with the real
power `n^{4609/4096}`. The definition is stated for every natural number `n`, without the
hypothesis `n ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §13.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The good words `Gd_n`: the words `w` of length `n` with `off(w) ≤ n^{4609/4096}` for
which some `i` with `1 ≤ i ≤ n` and `q^-_n < i ≤ q^+_n` satisfies
`A(w_{≤ i-1}) ≤ Lv_n < A(w_{≤ i}) ≤ ⌊Lv_n⌋ + 1 + ⌈(9/8) log₂ n⌉`. -/
@[collatz_pos_dens "def_mx_good"]
noncomputable def mxGood (n : ℕ) : Set Word :=
  {w | w.length = n ∧ ((off w : ℚ) : ℝ) ≤ (n : ℝ) ^ ((4609 : ℝ) / 4096) ∧
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ (mxWindowLow n < (i : ℤ) ∧ (i : ℤ) ≤ mxWindowHigh n) ∧
      (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
      mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
      (Word.valSum (w.take i) : ℤ) ≤ ⌊mxLevel n⌋ + 1 + ⌈(9 / 8 : ℝ) * Real.logb 2 n⌉}

/-- The defining condition of the good words `Gd_n`. -/
theorem mem_mxGood {n : ℕ} {w : Word} :
    w ∈ mxGood n ↔ w.length = n ∧ ((off w : ℚ) : ℝ) ≤ (n : ℝ) ^ ((4609 : ℝ) / 4096) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ (mxWindowLow n < (i : ℤ) ∧ (i : ℤ) ≤ mxWindowHigh n) ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
        mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
        (Word.valSum (w.take i) : ℤ) ≤ ⌊mxLevel n⌋ + 1 + ⌈(9 / 8 : ℝ) * Real.logb 2 n⌉ :=
  Iff.rfl

/-- Every good word has length `n`. -/
theorem length_of_mem_mxGood {n : ℕ} {w : Word} (hw : w ∈ mxGood n) : w.length = n :=
  hw.1

/-- Every good word has offset at most `n^{4609/4096}`. -/
theorem off_le_of_mem_mxGood {n : ℕ} {w : Word} (hw : w ∈ mxGood n) :
    ((off w : ℚ) : ℝ) ≤ (n : ℝ) ^ ((4609 : ℝ) / 4096) :=
  hw.2.1

end CollatzPosDens
