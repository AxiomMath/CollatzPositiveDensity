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
`w ∈ ℤ_{≥1}^n` for which some integer `i` with `1 ≤ i ≤ n` and `q^-_n < i ≤ q^+_n` has the
prefix sums cross the level `Lv_n` at the `i`-th letter with the product crossing condition:
$$A(w_{\le i-1}) \le \mathrm{Lv}_n < A(w_{\le i}) \quad\text{and}\quad
  2^{A(w_{\le i})} \operatorname{off}(w_{\le i}) < 3^n.$$
Every good word lies in the union of the slice gates, so the mass outside the gates is
bounded by the mass of the complement of `Gd_n`.

## Main definitions

* `CollatzPosDens.mxGood`: the set `Gd_n` of good words.

## Main results

* `CollatzPosDens.mem_mxGood`: the defining condition.
* `CollatzPosDens.length_of_mem_mxGood`: good words have length `n`.

## Implementation notes

Words are lists of positive integers, so membership in `ℤ_{≥1}^n` is the condition
`w.length = n`, and the prefix `w_{≤ i}` is `w.take i`. The index `i ≥ 1` is taken in `ℕ`;
the window condition compares it with the integers `q^±_n` in `ℤ`, the level conditions
compare valuation sums cast to `ℝ` with the real level `Lv_n`, and the product condition is
an inequality in `ℚ`, where the offset lives. The definition is stated for every natural
number `n`; the hypothesis `n ≥ 1` of the source belongs to the lemmas that use it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The good words `Gd_n`: the words `w` of length `n` for which some `i` with `1 ≤ i ≤ n` and
`q^-_n < i ≤ q^+_n` satisfies `A(w_{≤ i-1}) ≤ Lv_n < A(w_{≤ i})` and
`2^{A(w_{≤ i})} off(w_{≤ i}) < 3^n`. -/
@[collatz_pos_dens "def_mx_good"]
noncomputable def mxGood (n : ℕ) : Set Word :=
  {w | w.length = n ∧
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ (mxWindowLow n < (i : ℤ) ∧ (i : ℤ) ≤ mxWindowHigh n) ∧
      (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
      mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
      (2 : ℚ) ^ Word.valSum (w.take i) * off (w.take i) < 3 ^ n}

/-- The defining condition of the good words `Gd_n`. -/
theorem mem_mxGood {n : ℕ} {w : Word} :
    w ∈ mxGood n ↔ w.length = n ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ (mxWindowLow n < (i : ℤ) ∧ (i : ℤ) ≤ mxWindowHigh n) ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
        mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
        (2 : ℚ) ^ Word.valSum (w.take i) * off (w.take i) < 3 ^ n :=
  Iff.rfl

/-- Every good word has length `n`. -/
theorem length_of_mem_mxGood {n : ℕ} {w : Word} (hw : w ∈ mxGood n) : w.length = n :=
  hw.1

end CollatzPosDens
