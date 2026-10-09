/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.PNat.Basic
public import CollatzPosDens.Attr

/-!
# Words

A *word* is a finite sequence `w = (a₁, …, a_d)` of positive integers, `d ≥ 0`; its length is
`|w| = d` and `∅` is the empty word. Words are concatenated by juxtaposition, `u` is a prefix
of `w` if `w = u v` for some word `v`, and `w_{≤ i}` is the prefix of `w` of length `i`.
The letters of `w` are the exponents of successive inverse Syracuse steps, applied to a
starting value in the order `a₁, a₂, …`, as in `CollatzPosDens.src`.

## Main definitions

* `CollatzPosDens.Word`: the set `𝕎` of words, as lists of positive integers.

## Implementation notes

`Word` is an abbreviation for `List ℕ+`, so the whole list API applies directly: the length
`|w|` is `List.length`, the empty word is `[]`, concatenation `u v` is `u ++ v`, "`u` is a
prefix of `w`" is `u <+: w` (`List.IsPrefix`, which unfolds to `∃ v, u ++ v = w`), and the
prefix `w_{≤ i}` is `w.take i`. The list head is the letter `a₁`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝕎` of words: finite sequences `(a₁, …, a_d)` of positive integers, with `a₁` the
list head. Length, concatenation, prefixes and the prefix `w_{≤ i}` are `List.length`, `++`,
`List.IsPrefix` and `List.take i`. -/
@[collatz_pos_dens "def_word"]
abbrev Word : Type := List ℕ+

end CollatzPosDens
