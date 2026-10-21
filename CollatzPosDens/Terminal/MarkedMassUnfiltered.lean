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
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Terminal.TerminalShift
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The unfiltered marked terminal mass `Θ°_{j,X}(t)`

For an odd positive integer `t`, `j ≥ 0` and a real `X > 0`, the marked terminal mass without
the length filter is
\[
  Θ°_{j,X}(t) = ∑_{h ∈ 𝓗_j(t)} ω(h)
    ∑_{w ∈ 𝓦(b_j, u_h, K_j),\ w \text{ admissible from } R_h} ω(w)\,
      ρ_{k_j}(\mathrm{src}(w, R_h) \bmod 3^{k_j}).
\]
Each central history `h` of generation `j` from `t` is extended by every first-crossing word
at scale `b_j`, terminal shift `u_h` and cap `K_j` that is admissible from the endpoint `R_h`
of `h`, and the reference density at level `k_j` is evaluated at the residue of the resulting
source. Both sums are finite.

## Main definitions

* `CollatzPosDens.markedMassUnfilteredWords j X t h`: the set of words
  `w ∈ 𝓦(b_j, u_h, K_j)` admissible from `R_h`.
* `CollatzPosDens.markedMassUnfiltered j X t`: the sum `Θ°_{j,X}(t)`.

## Main results

* `CollatzPosDens.markedMassUnfilteredWords_finite`: the inner index set is finite.
* `CollatzPosDens.markedMassUnfiltered_eq_sum`: `Θ°_{j,X}(t)` as a double `Finset` sum.
* `CollatzPosDens.markedMassUnfiltered_nonneg`: `0 ≤ Θ°_{j,X}(t)`.

## Implementation notes

Both sums are `finsum`s over sets, finite by
`CollatzPosDens.centralHistories_finite` and
`CollatzPosDens.firstCrossing_finite`. The weight of a history is that of its concatenated
word, `ω(h) = ω(ŵ(h))`. The source `src(w, R_h)` is a rational number, an integer when `w` is
admissible from `R_h`; its residue modulo `3^{k_j}` is taken to be that of its numerator, as in
`CollatzPosDens.weightedCentralSum`. The seed `t` is taken in `ℚ` and `X` in `ℝ`; the
oddness and positivity of `t` and the positivity of `X` are not needed to state the definition,
so the definition is stated without them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The words `w ∈ 𝓦(b_j, u_h, K_j)` that are admissible from the endpoint `R_h` of the
history `h`: the inner index set of `Θ°_{j,X}(t)`. -/
@[collatz_pos_dens "def_marked_mass_unfiltered"]
def markedMassUnfilteredWords (j : ℕ) (X : ℝ) (t : ℚ) (h : Fin j → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale j) (historyShift j X t h) (cap j) ∧
    Admissible (historyEndpoint t h) w}

/-- Membership in the inner index set of `Θ°_{j,X}(t)`. -/
theorem mem_markedMassUnfilteredWords {j : ℕ} {X : ℝ} {t : ℚ} {h : Fin j → Word} {w : Word} :
    w ∈ markedMassUnfilteredWords j X t h ↔
      w ∈ firstCrossing (scale j) (historyShift j X t h) (cap j) ∧
        Admissible (historyEndpoint t h) w :=
  Iff.rfl

/-- The inner index set of `Θ°_{j,X}(t)` is finite. -/
theorem markedMassUnfilteredWords_finite (j : ℕ) (X : ℝ) (t : ℚ) (h : Fin j → Word) :
    (markedMassUnfilteredWords j X t h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- The marked terminal mass without the length filter,
`Θ°_{j,X}(t) = ∑_{h ∈ 𝓗_j(t)} ω(h) ∑_{w ∈ 𝓦(b_j,u_h,K_j), w admissible from R_h}
ω(w) ρ_{k_j}(src(w, R_h) mod 3^{k_j})`. -/
@[collatz_pos_dens "def_marked_mass_unfiltered"]
noncomputable def markedMassUnfiltered (j : ℕ) (X : ℝ) (t : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories t j, ((concatWord h).weight : ℝ) *
    ∑ᶠ w ∈ markedMassUnfilteredWords j X t h, (w.weight : ℝ) *
      refDensity (level j) ((src w (historyEndpoint t h)).num : ResidueGroup (level j))

/-- `Θ°_{j,X}(t)` as a double `Finset` sum over the finite index sets. -/
theorem markedMassUnfiltered_eq_sum (j : ℕ) (X : ℝ) (t : ℚ) :
    markedMassUnfiltered j X t =
      ∑ h ∈ (centralHistories_finite t j).toFinset,
        ((concatWord h).weight : ℝ) *
          ∑ w ∈ (markedMassUnfilteredWords_finite j X t h).toFinset, (w.weight : ℝ) *
            refDensity (level j) ((src w (historyEndpoint t h)).num : ResidueGroup (level j)) := by
  rw [markedMassUnfiltered,
    finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite t j)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (markedMassUnfilteredWords_finite j X t h)]

/-- The unfiltered marked mass is nonnegative. -/
theorem markedMassUnfiltered_nonneg (j : ℕ) (X : ℝ) (t : ℚ) :
    0 ≤ markedMassUnfiltered j X t := by
  rw [markedMassUnfiltered_eq_sum]
  refine Finset.sum_nonneg fun h _ => mul_nonneg ?_ (Finset.sum_nonneg fun w _ => ?_)
  · exact_mod_cast (Word.weight_pos _).le
  · exact mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

end CollatzPosDens
