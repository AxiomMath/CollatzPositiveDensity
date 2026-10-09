/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldList
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Green's function of the holding-time law

For `(j, s) ∈ ℤ × ℤ` the Green's function of the renewal process is
`𝒢(j, s) = ∑_{N ≥ 0} ∑_{h ∈ 𝒫^N, h_1 + ⋯ + h_N = (j, s)} η^{⊗N}(h)`,
the total weight of hold lists of any length whose steps add up to `(j, s)`. The term `N = 0`
is the empty hold list, which contributes `η^{⊗0} = 1` exactly when `(j, s) = (0, 0)`.

## Main definitions

* `CollatzPosDens.green j s`: the Green's function `𝒢(j, s)`.

## Main results

* `CollatzPosDens.green_def`: the defining double sum.
* `CollatzPosDens.green_nonneg`: `0 ≤ 𝒢(j, s)`.

## Implementation notes

A point of `𝒫 = ℤ_{≥1} × ℤ` is a pair `p : ℕ × ℤ` with `1 ≤ p.1`, matching the signature of
`holdListLaw`, and `h ∈ 𝒫^N` is a tuple `h : Fin N → ℕ × ℤ` all of whose entries satisfy this.
The constraint `h_1 + ⋯ + h_N = (j, s)` is stated coordinatewise, the first coordinates being
summed in `ℤ`. The outer sum over `N` and the inner sum over `h` are `tsum`s; every term is
nonnegative and only finitely many are nonzero (`CollatzPosDens.green_finite`), so these are
finite sums. The restriction to `𝒫` is essential: `η(0, 0) = 1`, so admitting steps with first
coordinate `0` would make the inner sums infinite.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The Green's function
`𝒢(j, s) = ∑_{N ≥ 0} ∑_{h ∈ 𝒫^N, h_1 + ⋯ + h_N = (j, s)} η^{⊗N}(h)`, where `h ∈ 𝒫^N` is a
tuple `h : Fin N → ℕ × ℤ` with every first coordinate at least `1`. -/
@[collatz_pos_dens "def_rn_green"]
noncomputable def green (j s : ℤ) : ℝ :=
  ∑' N : ℕ, ∑' h : {h : Fin N → ℕ × ℤ //
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s},
    holdListLaw h.1

/-- Unfolding lemma for `green`. -/
theorem green_def (j s : ℤ) :
    green j s =
      ∑' N : ℕ, ∑' h : {h : Fin N → ℕ × ℤ //
          (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s},
        holdListLaw h.1 :=
  rfl

/-- The Green's function is nonnegative. -/
theorem green_nonneg (j s : ℤ) : 0 ≤ green j s :=
  tsum_nonneg fun _ ↦ tsum_nonneg fun h ↦ holdListLaw_nonneg h.1

end CollatzPosDens
