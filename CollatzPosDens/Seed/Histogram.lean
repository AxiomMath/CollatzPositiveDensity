/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The residue histogram

For an odd positive integer `t`, `n, q ≥ 0` and a residue `y ∈ G_q = ℤ/3^qℤ`, the residue
histogram is the total weight of the central histories of generation `n` from `t` whose endpoint
lies in the class `y`:
`Hg_{n,q}(y) = ∑_{h ∈ 𝓗_n(t), R_h ≡ y (mod 3^q)} ω(h)`.

## Main definitions

* `CollatzPosDens.residueHistogram t n q y`: the histogram value `Hg_{n,q}(y)`.

## Main results

* `CollatzPosDens.residueHistogram_eq_sum`: `Hg_{n,q}(y)` as a `Finset` sum over the
  finite set `𝓗_n(t)`.
* `CollatzPosDens.residueHistogram_nonneg`: the histogram is nonnegative.

## Implementation notes

The endpoint `R_h` is a rational number (`CollatzPosDens.historyEndpoint`); the congruence
`R_h ≡ y (mod 3^q)` is read as "`R_h` is an integer `r` with `r ≡ y (mod 3^q)`". This is no
restriction, since the endpoint of a central history from `t` is an integer (its concatenated word
is admissible from `t`). The sum is a `finsum` over the set `𝓗_n(t)`; this set is finite, so the
`finsum` is a finite sum, and the definition needs no finiteness hypothesis to be stated. As in
`CollatzPosDens.centralHistories`, `t` is taken in `ℚ` and its oddness and positivity are left to
the results that use them.

## References

* [Mazur, *Collatz positive density*], §16.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The residue histogram `Hg_{n,q}(y) = ∑_{h ∈ 𝓗_n(t), R_h ≡ y (mod 3^q)} ω(h)`: the total
weight of the central histories of generation `n` from `t` whose endpoint `R_h` is an integer
congruent to `y` modulo `3^q`. -/
@[collatz_pos_dens "def_histogram"]
noncomputable def residueHistogram (t : ℚ) (n q : ℕ) (y : ResidueGroup q) : ℝ :=
  ∑ᶠ (h : Fin n → Word) (_ : h ∈ centralHistories t n ∧
      ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y),
    ((concatWord h).weight : ℝ)

open Classical in
/-- The residue histogram as a `Finset` sum over the finite set `𝓗_n(t)`. -/
theorem residueHistogram_eq_sum (t : ℚ) (n q : ℕ) (y : ResidueGroup q) :
    residueHistogram t n q y =
      ∑ h ∈ (centralHistories_finite t n).toFinset with
        ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y,
        ((concatWord h).weight : ℝ) := by
  rw [Finset.sum_filter, ← finsum_mem_eq_finite_toFinset_sum, residueHistogram]
  refine finsum_congr fun h => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hC : h ∈ centralHistories t n
  · by_cases hP : ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y
    · rw [ite_eq_left ⟨hC, hP⟩, ite_eq_left hC, ite_eq_left hP]
    · rw [ite_eq_right fun H => hP H.2, ite_eq_left hC, ite_eq_right hP]
  · rw [ite_eq_right fun H => hC H.1, ite_eq_right hC]

/-- The residue histogram is nonnegative. -/
theorem residueHistogram_nonneg (t : ℚ) (n q : ℕ) (y : ResidueGroup q) :
    0 ≤ residueHistogram t n q y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by exact_mod_cast (Word.weight_pos _).le

end CollatzPosDens
