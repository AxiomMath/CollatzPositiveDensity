/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The weighted central sum `Z_n`

For an odd positive integer `t` and `n ≥ 0`, the weighted central sum is
`Z_n(t) = ∑_{h ∈ 𝓗_n(t)} ω(h) ρ_{k_n}(R_h mod 3^{k_n})`, a sum over the central histories of
generation `n` from `t`, weighting each history by `ω(h) = ω(ŵ(h))` and by the reference
density at level `k_n = ⌊b_n / 4⌋` evaluated at the residue of its endpoint `R_h`. The sum is
finite: every word of a central family `𝒞(b_j, K_j)` lies in a first-crossing family, whose
words have bounded valuation sum, and there are finitely many words of bounded valuation sum.

## Main definitions

* `CollatzPosDens.weightedCentralSum n t`: the sum `Z_n(t)`.

## Main results

* `CollatzPosDens.weightedCentralSum_eq_sum`: `Z_n(t)` as a `Finset` sum over `𝓗_n(t)`.
* `CollatzPosDens.weightedCentralSum_nonneg`: `0 ≤ Z_n(t)`.

## Implementation notes

The sum is a `finsum` over the set `𝓗_n(t)`; since that set is finite it is a genuine finite
sum, and `weightedCentralSum_eq_sum` rewrites it as a `Finset` sum. The endpoint `R_h` is a
rational number, an integer for `h ∈ 𝓗_n(t)` because `ŵ(h)` is admissible from `t`; its residue
modulo `3^{k_n}` is taken to be that of its numerator. The starting point `t` is taken in `ℚ`,
as for `CollatzPosDens.centralHistories`; the oddness and positivity of `t` are not needed
to state the definition.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §16.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted central sum `Z_n(t) = ∑_{h ∈ 𝓗_n(t)} ω(h) ρ_{k_n}(R_h mod 3^{k_n})`. -/
@[collatz_pos_dens "def_Zn"]
noncomputable def weightedCentralSum (n : ℕ) (t : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories t n,
    ((concatWord h).weight : ℝ) *
      refDensity (level n) ((historyEndpoint t h).num : ResidueGroup (level n))

/-- `Z_n(t)` as a `Finset` sum over the finite set `𝓗_n(t)`. -/
theorem weightedCentralSum_eq_sum (n : ℕ) (t : ℚ) :
    weightedCentralSum n t =
      ∑ h ∈ (centralHistories_finite t n).toFinset,
        ((concatWord h).weight : ℝ) *
          refDensity (level n) ((historyEndpoint t h).num : ResidueGroup (level n)) :=
  finsum_mem_eq_finite_toFinset_sum _ _

/-- The weighted central sum is nonnegative. -/
theorem weightedCentralSum_nonneg (n : ℕ) (t : ℚ) : 0 ≤ weightedCentralSum n t := by
  rw [weightedCentralSum_eq_sum]
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

end CollatzPosDens
