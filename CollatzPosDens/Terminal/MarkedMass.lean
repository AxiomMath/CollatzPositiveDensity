/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.LengthOk
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Terminal.TerminalShift
public import CollatzPosDens.Transfer.RefDensity

/-!
# The marked terminal mass `Θ_{j,X}(t)`

For `j : ℕ`, an external scale `X` and a starting point `t`, the marked terminal mass is
$$\Theta_{j,X}(t) = \sum_{h \in \mathcal H_j(t)} \omega(h)
  \sum_{w} \omega(w)\, \rho_{k_j}\bigl(\mathrm{src}(w, R_h) \bmod 3^{k_j}\bigr),$$
where the inner sum runs over the words `w ∈ 𝒲(b_j, u_h, K_j)` satisfying the length condition
`Λ_{b_j,u_h}(w)` and admissible from the endpoint `R_h` of `h`. Here `b_j` is the scale, `K_j`
the cap, `k_j = ⌊b_j / 4⌋` the level, `u_h = u_{j,X}(R_h)` the terminal shift of `h`, and
`ω(h) = ω(ŵ(h))` the weight of the concatenated word of `h`. Both sums are finite, since
`𝓗_j(t)` and every first-crossing family `𝒲(b, u, K)` are finite.

## Main definitions

* `CollatzPosDens.markedMassWords j X t h`: the words `w` of the inner sum attached to `h`.
* `CollatzPosDens.markedMass j X t`: the marked terminal mass `Θ_{j,X}(t)`.

## Main results

* `CollatzPosDens.mem_markedMassWords`: membership in the inner index set.
* `CollatzPosDens.markedMassWords_finite`: the inner index set is finite.
* `CollatzPosDens.markedMass_eq_sum`: `Θ_{j,X}(t)` as an iterated `Finset` sum.
* `CollatzPosDens.markedMass_nonneg`: `0 ≤ Θ_{j,X}(t)`.

## Implementation notes

Both sums are `finsum`s over sets; these sets are finite
(`CollatzPosDens.centralHistories_finite`,
`CollatzPosDens.markedMassWords_finite`), so the `finsum`s are finite sums and
the definition needs no hypothesis. The inner index set is the set of `w ∈ 𝒲(b_j, u_h, K_j)`
admissible from `R_h` cut down by the length filter `Λ_{b_j,u_h}`, so the version without the
length filter differs only in dropping that conjunct.

The endpoint `R_h` and the source `src(w, R_h)` are rational numbers, integers when `w` is
admissible from `R_h` and `R_h` is an integer; the residue of `src(w, R_h)` modulo `3^{k_j}` is
taken to be that of its numerator, as in `CollatzPosDens.weightedCentralSum`. The shift
`u_h ∈ ℕ` is cast to `ℤ` to index the first-crossing family. The positivity of `X` and the
oddness and positivity of `t` are not needed to state the definition.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {j : ℕ}

/-- The words of the inner sum of `Θ_{j,X}(t)` attached to a history `h`: the words
`w ∈ 𝒲(b_j, u_h, K_j)` with `Λ_{b_j,u_h}(w)` that are admissible from the endpoint `R_h`. -/
def markedMassWords (j : ℕ) (X : ℝ) (t : ℚ) (h : Fin j → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale j) (historyShift j X t h) (cap j) ∧
    LengthOk (scale j) (historyShift j X t h) w ∧ Admissible (historyEndpoint t h) w}

/-- The marked terminal mass
`Θ_{j,X}(t) = ∑_{h ∈ 𝓗_j(t)} ω(h) ∑_w ω(w) ρ_{k_j}(src(w, R_h) mod 3^{k_j})`, the inner sum over
`w ∈ 𝒲(b_j, u_h, K_j)` with `Λ_{b_j,u_h}(w)` and `w` admissible from `R_h`. -/
@[collatz_pos_dens "def_marked_mass"]
noncomputable def markedMass (j : ℕ) (X : ℝ) (t : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories t j, ((concatWord h).weight : ℝ) *
    ∑ᶠ w ∈ markedMassWords j X t h, (w.weight : ℝ) *
      refDensity (level j) ((src w (historyEndpoint t h)).num : ResidueGroup (level j))

/-- Membership in the inner index set of `Θ_{j,X}(t)`. -/
theorem mem_markedMassWords {X : ℝ} {t : ℚ} {h : Fin j → Word} {w : Word} :
    w ∈ markedMassWords j X t h ↔
      w ∈ firstCrossing (scale j) (historyShift j X t h) (cap j) ∧
        LengthOk (scale j) (historyShift j X t h) w ∧ Admissible (historyEndpoint t h) w :=
  Iff.rfl

/-- The inner index set of `Θ_{j,X}(t)` is finite. -/
theorem markedMassWords_finite (j : ℕ) (X : ℝ) (t : ℚ) (h : Fin j → Word) :
    (markedMassWords j X t h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- `Θ_{j,X}(t)` as an iterated `Finset` sum over the finite index sets. -/
theorem markedMass_eq_sum (j : ℕ) (X : ℝ) (t : ℚ) :
    markedMass j X t = ∑ h ∈ (centralHistories_finite t j).toFinset,
      ((concatWord h).weight : ℝ) * ∑ w ∈ (markedMassWords_finite j X t h).toFinset,
        (w.weight : ℝ) *
          refDensity (level j) ((src w (historyEndpoint t h)).num : ResidueGroup (level j)) := by
  rw [markedMass,
    finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite t j)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (markedMassWords_finite j X t h)]

/-- The marked terminal mass is nonnegative. -/
theorem markedMass_nonneg (j : ℕ) (X : ℝ) (t : ℚ) : 0 ≤ markedMass j X t := by
  rw [markedMass_eq_sum]
  refine Finset.sum_nonneg fun h _ => mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) ?_
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

end CollatzPosDens
