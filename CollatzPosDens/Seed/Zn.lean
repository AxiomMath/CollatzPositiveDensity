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

For an odd positive integer `M` and `n ≥ 0`, the weighted central sum is
`Z_n(M) = ∑_{h ∈ 𝓗_n(M)} ω(h) ρ_{k_n}(R_h mod 3^{k_n})`, a sum over the central histories of
generation `n` from `M`, weighting each history by `ω(h) = ω(ŵ(h))` and by the reference
density at level `k_n = ⌊b_n / 4⌋` evaluated at the residue of its endpoint `R_h`. The sum is
finite: every word of a central family `𝒞(b_j, K_j)` lies in a first-crossing family, whose
words have bounded valuation sum, and there are finitely many words of bounded valuation sum.

## Main definitions

* `CollatzPosDens.weightedCentralSum n M`: the sum `Z_n(M)`.

## Main results

* `CollatzPosDens.weightedCentralSum_eq_sum`: `Z_n(M)` as a `Finset` sum over `𝓗_n(M)`.
* `CollatzPosDens.weightedCentralSum_nonneg`: `0 ≤ Z_n(M)`.

## Implementation notes

The sum is a `finsum` over the set `𝓗_n(M)`; since that set is finite it is a genuine finite
sum, and `weightedCentralSum_eq_sum` rewrites it as a `Finset` sum. The endpoint `R_h` is a
rational number, an integer for `h ∈ 𝓗_n(M)` because `ŵ(h)` is admissible from `M`; its residue
modulo `3^{k_n}` is taken to be that of its numerator. The starting point `M` is taken in `ℚ`,
as for `CollatzPosDens.centralHistories`; the oddness and positivity of `M` are not needed
to state the definition.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted central sum `Z_n(M) = ∑_{h ∈ 𝓗_n(M)} ω(h) ρ_{k_n}(R_h mod 3^{k_n})`. -/
@[collatz_pos_dens "def_Zn"]
noncomputable def weightedCentralSum (n : ℕ) (M : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories M n,
    ((concatWord h).weight : ℝ) *
      refDensity (level n) ((historyEndpoint M h).num : ResidueGroup (level n))

/-- `Z_n(M)` as a `Finset` sum over the finite set `𝓗_n(M)`. -/
theorem weightedCentralSum_eq_sum (n : ℕ) (M : ℚ) :
    weightedCentralSum n M =
      ∑ h ∈ (centralHistories_finite M n).toFinset,
        ((concatWord h).weight : ℝ) *
          refDensity (level n) ((historyEndpoint M h).num : ResidueGroup (level n)) :=
  finsum_mem_eq_finite_toFinset_sum _ _

/-- The weighted central sum is nonnegative. -/
theorem weightedCentralSum_nonneg (n : ℕ) (M : ℚ) : 0 ≤ weightedCentralSum n M := by
  rw [weightedCentralSum_eq_sum]
  refine Finset.sum_nonneg fun h _ => mul_nonneg ?_ (refDensity_nonneg _ _)
  exact_mod_cast (Word.weight_pos _).le

end CollatzPosDens
