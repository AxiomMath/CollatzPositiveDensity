/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Characters.FxOffsetLaw
public import CollatzPosDens.Transfer.FxRefLawBounded

/-!
# The submass is bounded by the reference law

For `n ∈ ℕ`, a set `𝒱 ⊆ ℤ_{≥1}^n` of words of length `n` and `y ∈ G_n`,
$$\mathrm{Sub}^n_{\mathcal V}(y) \le \mu_n(y) \quad\text{in } [0, \infty].$$
The reference law `μ_n(y)` is the submass at `y` of the set of all words of length `n`, and the
submass is monotone in the set of words.

## Main results

* `CollatzPosDens.subMass_length_eq_refLaw`: `Sub^n_{ℤ_{≥1}^n}(y) = μ_n(y)`.
* `CollatzPosDens.subMass_le_refLaw`: `Sub^n_𝒱(y) ≤ μ_n(y)` for `𝒱 ⊆ ℤ_{≥1}^n`.
* `CollatzPosDens.subMass_ne_top_of_subset_length`: `Sub^n_𝒱(y) < ∞` for `𝒱 ⊆ ℤ_{≥1}^n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The submass of the set of all words of length `n` is the reference law:
`Sub^n_{ℤ_{≥1}^n}(y) = μ_n(y)`. -/
theorem subMass_length_eq_refLaw (n : ℕ) (y : ResidueGroup n) :
    subMass n {w : Word | w.length = n} y = refLaw n y := by
  rw [subMass_eq_tsum, refLaw_eq_tsum_off]
  exact tsum_congr fun w => by simp [ENNReal.inv_pow]

/-- **Submass bound.** For `𝒱 ⊆ ℤ_{≥1}^n` and `y ∈ G_n`, `Sub^n_𝒱(y) ≤ μ_n(y)` in `[0, ∞]`. -/
@[collatz_pos_dens "lem_mx_submass_le"]
theorem subMass_le_refLaw (n : ℕ) {V : Set Word} (hV : V ⊆ {w : Word | w.length = n})
    (y : ResidueGroup n) : subMass n V y ≤ refLaw n y :=
  subMass_length_eq_refLaw n y ▸ subMass_mono n hV y

/-- A submass of a set of words of length `n` is finite. -/
theorem subMass_ne_top_of_subset_length (n : ℕ) {V : Set Word}
    (hV : V ⊆ {w : Word | w.length = n}) (y : ResidueGroup n) : subMass n V y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((subMass_le_refLaw n hV y).trans (refLaw_le_one n y))

end CollatzPosDens
