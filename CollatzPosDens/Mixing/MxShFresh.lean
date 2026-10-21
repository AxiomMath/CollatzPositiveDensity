/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShPattern

/-!
# The fresh word of the binary clock

Let `N ∈ ℕ` and `w = (a₁, …, a_n)` a word with `d = |Ex_N(w)| < n`. The *fresh word* of `w`
is the sequence of `n - d` integers
$$\mathrm{Fr}_N(w) = \bigl(A(w_{\le d+1}) - N,\ a_{d+2}, \dots, a_n\bigr),$$
whose first entry is the overshoot of the first partial sum beyond `N` and whose remaining
entries are the letters of `w` after position `d + 1`. It is again a word: the first entry is
positive.

## Main definitions

* `CollatzPosDens.Word.freshSeq`: the integer sequence `Fr_N(w)`.
* `CollatzPosDens.Word.fresh`: the same sequence as a word, its first letter read in `ℕ+`.

## Main results

* `CollatzPosDens.Word.fresh_append_cons`: `Fr_N(u a r) = (A(u) + a - N) r` when
  `A(u) ≤ N < A(u) + a`.
* `CollatzPosDens.Word.freshSeq_append_cons`: the same identity for the integer sequence.

## Implementation notes

`Fr_N(w)` is defined for every word: when `|Ex_N(w)| ≥ |w|` its value is irrelevant. The
integer sequence `freshSeq` is the definition as stated; the word `fresh` truncates the first
entry to a positive integer, and agrees with `freshSeq` whenever `|Ex_N(w)| < |w|`. Statements
about offsets and valuation sums of the fresh word use `fresh`, which is a `Word`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset

/-- The fresh word `Fr_N(w) = (A(w_{≤ d+1}) - N, a_{d+2}, …, a_n) ∈ ℤ^{n-d}` of a word
`w = (a₁, …, a_n)`, with `d = |Ex_N(w)|`, as a list of integers. -/
@[collatz_pos_dens "def_mx_sh_fresh"]
def freshSeq (N : ℕ) (w : Word) : List ℤ :=
  ((valSum (w.take (#(exposedPattern N w) + 1)) : ℤ) - N) ::
    (w.drop (#(exposedPattern N w) + 1)).map fun a : ℕ+ => ((a : ℕ) : ℤ)

/-- The fresh word `Fr_N(w)` as a word: the first letter `A(w_{≤ d+1}) - N` (with `d =
|Ex_N(w)|`) is read in `ℕ+`, followed by the letters of `w` after position `d + 1`. It agrees
with `freshSeq N w` whenever `|Ex_N(w)| < |w|`. -/
def fresh (N : ℕ) (w : Word) : Word :=
  Nat.toPNat' (valSum (w.take (#(exposedPattern N w) + 1)) - N) ::
    w.drop (#(exposedPattern N w) + 1)

/-- If `A(u) ≤ N < A(u) + a`, then `Fr_N(u a r) = (A(u) + a - N) r` as integer sequences. -/
theorem freshSeq_append_cons {N : ℕ} {u : Word} {a : ℕ+} (r : Word)
    (hu : valSum u ≤ N) (ha : N < valSum u + a) :
    freshSeq N (u ++ a :: r) =
      ((valSum u + a : ℕ) - N : ℤ) :: r.map fun b : ℕ+ => ((b : ℕ) : ℤ) := by
  simp [freshSeq, card_exposedPattern_append_cons r hu ha, List.take_append, List.drop_append,
    List.take_of_length_le, List.drop_eq_nil_of_le]

/-- If `A(u) ≤ N < A(u) + a`, then `Fr_N(u a r) = (A(u) + a - N) r`, the first letter being the
positive integer `A(u) + a - N`. -/
theorem fresh_append_cons {N : ℕ} {u : Word} {a : ℕ+} (r : Word)
    (hu : valSum u ≤ N) (ha : N < valSum u + a) :
    fresh N (u ++ a :: r) = Nat.toPNat' (valSum u + a - N) :: r := by
  simp [fresh, card_exposedPattern_append_cons r hu ha, List.take_append, List.drop_append,
    List.take_of_length_le, List.drop_eq_nil_of_le]

/-- If `A(u) ≤ N < A(u) + a`, the first letter of `Fr_N(u a r)` is `A(u) + a - N`. -/
theorem coe_toPNat'_valSum_add_sub {N : ℕ} {u : Word} {a : ℕ+} (ha : N < valSum u + a) :
    ((Nat.toPNat' (valSum u + a - N) : ℕ+) : ℕ) = valSum u + a - N :=
by
  rw [Nat.toPNat'_coe]
  split_ifs <;> omega

/-- If `A(u) ≤ N < A(u) + a`, then `A(Fr_N(u a r)) + N = A(u a r)`. -/
theorem valSum_fresh_append_cons {N : ℕ} {u : Word} {a : ℕ+} (r : Word)
    (hu : valSum u ≤ N) (ha : N < valSum u + a) :
    valSum (fresh N (u ++ a :: r)) + N = valSum (u ++ a :: r) := by
  rw [fresh_append_cons r hu ha, valSum_cons, coe_toPNat'_valSum_add_sub ha, valSum_append,
    valSum_cons]
  omega

/-- If `A(u) ≤ N < A(u) + a`, the fresh word of `u a r` has length `|r| + 1`. -/
theorem length_fresh_append_cons {N : ℕ} {u : Word} {a : ℕ+} (r : Word)
    (hu : valSum u ≤ N) (ha : N < valSum u + a) :
    (fresh N (u ++ a :: r)).length = r.length + 1 := by
  rw [fresh_append_cons r hu ha, List.length_cons]

end Word

end CollatzPosDens
