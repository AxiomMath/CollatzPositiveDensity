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

For an odd positive integer `M`, `n, q ≥ 0` and a residue `y ∈ G_q = ℤ/3^qℤ`, the residue
histogram is the total weight of the central histories of generation `n` from `M` whose endpoint
lies in the class `y`:
`Hg_{n,q}(y) = ∑_{h ∈ 𝓗_n(M), R_h ≡ y (mod 3^q)} ω(h)`.

## Main definitions

* `CollatzPosDens.residueHistogram M n q y`: the histogram value `Hg_{n,q}(y)`.

## Main results

* `CollatzPosDens.residueHistogram_eq_sum`: `Hg_{n,q}(y)` as a `Finset` sum over the
  finite set `𝓗_n(M)`.
* `CollatzPosDens.residueHistogram_nonneg`: the histogram is nonnegative.

## Implementation notes

The endpoint `R_h` is a rational number (`CollatzPosDens.historyEndpoint`); the congruence
`R_h ≡ y (mod 3^q)` is read as "`R_h` is an integer `r` with `r ≡ y (mod 3^q)`"; this loses
nothing, since the endpoint of a central history from `M` is an integer (its concatenated word is
admissible from `M`). The sum is a `finsum` over the set `𝓗_n(M)`; this set is finite, so the
`finsum` is an ordinary finite sum, and the definition needs no finiteness hypothesis to be
stated. As in `CollatzPosDens.centralHistories`, `M` is taken in `ℚ` and its oddness and
positivity are left to the results that use them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The residue histogram `Hg_{n,q}(y) = ∑_{h ∈ 𝓗_n(M), R_h ≡ y (mod 3^q)} ω(h)`: the total
weight of the central histories of generation `n` from `M` whose endpoint `R_h` is an integer
congruent to `y` modulo `3^q`. -/
@[collatz_pos_dens "def_histogram"]
noncomputable def residueHistogram (M : ℚ) (n q : ℕ) (y : ResidueGroup q) : ℝ :=
  ∑ᶠ (h : Fin n → Word) (_ : h ∈ centralHistories M n ∧
      ∃ r : ℤ, (r : ℚ) = historyEndpoint M h ∧ (r : ResidueGroup q) = y),
    ((concatWord h).weight : ℝ)

open Classical in
/-- The residue histogram as a `Finset` sum over the finite set `𝓗_n(M)`. -/
theorem residueHistogram_eq_sum (M : ℚ) (n q : ℕ) (y : ResidueGroup q) :
    residueHistogram M n q y =
      ∑ h ∈ (centralHistories_finite M n).toFinset with
        ∃ r : ℤ, (r : ℚ) = historyEndpoint M h ∧ (r : ResidueGroup q) = y,
        ((concatWord h).weight : ℝ) := by
  rw [Finset.sum_filter, ← finsum_mem_eq_finite_toFinset_sum, residueHistogram]
  refine finsum_congr fun h => ?_
  simp only [finsum_eq_if]
  split_ifs <;> simp_all

/-- The residue histogram is nonnegative. -/
theorem residueHistogram_nonneg (M : ℚ) (n q : ℕ) (y : ResidueGroup q) :
    0 ≤ residueHistogram M n q y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by exact_mod_cast (Word.weight_pos _).le

end CollatzPosDens
