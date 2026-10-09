/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Set.Finite.List
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Mixing.MxLevel
public import CollatzPosDens.Mixing.MxWindowLow
public import CollatzPosDens.Mixing.MxWindowHigh

/-!
# The head gate `Hd(n, k, l)`

For an integer `n ≥ 1` and `k, l ∈ ℕ`, the *head gate* `Hd(n, k, l)` is the set of words
`h = (a₁, …, a_{k+1})` of length `k + 1` such that

1. the length lies in the window, `q^-_n < k + 1 ≤ q^+_n`;
2. `h` crosses the level `Lv_n` at its last letter with valuation sum `l`:
   $$A(h_{\le k}) \le \mathrm{Lv}_n < A(h) = l;$$
3. the crossing does not overshoot by much:
   `l ≤ ⌊Lv_n⌋ + 1 + ⌈(9/8) log₂ n⌉`;
4. the offset is small, `off(h) ≤ n^{4609/4096}`.

## Main definitions

* `CollatzPosDens.mxHeadGate`: the head gate `Hd(n, k, l)`, a set of words.

## Main results

* `CollatzPosDens.mem_mxHeadGate`: the defining condition.
* `CollatzPosDens.mxHeadGate_finite`: every head gate is a finite set of words.
* `CollatzPosDens.length_of_mem_mxHeadGate`, `CollatzPosDens.valSum_of_mem_mxHeadGate`:
  members have length `k + 1` and valuation sum `l`.

## Implementation notes

Words are lists of positive integers, so membership in `ℤ_{≥1}^{k+1}` is the condition
`h.length = k + 1`, and the prefix `h_{≤ k}` is `h.take k`. The window condition compares
`k + 1` with the integers `q^±_n` in `ℤ`; the level conditions compare valuation sums cast to
`ℝ` with the real level `Lv_n`; condition 3 is an inequality in `ℤ`; the offset, a rational
number, is cast to `ℝ` and compared with the real power `n^{4609/4096}`. The definition is
stated for every natural number `n`; the hypothesis `n ≥ 1` belongs to the lemmas that use it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The head gate `Hd(n, k, l)`: the words `h` of length `k + 1` with
`q^-_n < k + 1 ≤ q^+_n`, `A(h_{≤ k}) ≤ Lv_n < A(h) = l`,
`l ≤ ⌊Lv_n⌋ + 1 + ⌈(9/8) log₂ n⌉` and `off(h) ≤ n^{4609/4096}`. -/
@[collatz_pos_dens "def_mx_head_gate"]
noncomputable def mxHeadGate (n k l : ℕ) : Set Word :=
  {h | h.length = k + 1 ∧
    (mxWindowLow n < (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ mxWindowHigh n) ∧
    ((Word.valSum (h.take k) : ℝ) ≤ mxLevel n ∧ mxLevel n < (Word.valSum h : ℝ) ∧
      Word.valSum h = l) ∧
    (l : ℤ) ≤ ⌊mxLevel n⌋ + 1 + ⌈(9 / 8 : ℝ) * Real.logb 2 n⌉ ∧
    ((off h : ℚ) : ℝ) ≤ (n : ℝ) ^ ((4609 : ℝ) / 4096)}

/-- The defining condition of the head gate `Hd(n, k, l)`. -/
theorem mem_mxHeadGate {n k l : ℕ} {h : Word} :
    h ∈ mxHeadGate n k l ↔ h.length = k + 1 ∧
      (mxWindowLow n < (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ mxWindowHigh n) ∧
      ((Word.valSum (h.take k) : ℝ) ≤ mxLevel n ∧ mxLevel n < (Word.valSum h : ℝ) ∧
        Word.valSum h = l) ∧
      (l : ℤ) ≤ ⌊mxLevel n⌋ + 1 + ⌈(9 / 8 : ℝ) * Real.logb 2 n⌉ ∧
      ((off h : ℚ) : ℝ) ≤ (n : ℝ) ^ ((4609 : ℝ) / 4096) :=
  Iff.rfl

/-- A member of `Hd(n, k, l)` has length `k + 1`. -/
theorem length_of_mem_mxHeadGate {n k l : ℕ} {h : Word} (hh : h ∈ mxHeadGate n k l) :
    h.length = k + 1 :=
  hh.1

/-- A member of `Hd(n, k, l)` has valuation sum `l`. -/
theorem valSum_of_mem_mxHeadGate {n k l : ℕ} {h : Word} (hh : h ∈ mxHeadGate n k l) :
    Word.valSum h = l :=
  hh.2.2.1.2.2

/-- A member of `Hd(n, k, l)` has offset at most `n^{4609/4096}`. -/
theorem off_le_of_mem_mxHeadGate {n k l : ℕ} {h : Word} (hh : h ∈ mxHeadGate n k l) :
    ((off h : ℚ) : ℝ) ≤ (n : ℝ) ^ ((4609 : ℝ) / 4096) :=
  hh.2.2.2.2

/-- Every head gate `Hd(n, k, l)` is a finite set of words. -/
theorem mxHeadGate_finite (n k l : ℕ) : (mxHeadGate n k l).Finite :=
  (Word.finite_setOf_valSum_le l).subset fun _ hh => (valSum_of_mem_mxHeadGate hh).le

end CollatzPosDens
