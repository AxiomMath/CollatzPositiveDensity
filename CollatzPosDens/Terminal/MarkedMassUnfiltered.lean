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
# The unfiltered marked terminal mass `Θ°_{n,X}(M)`

For `n ≥ 0`, a real `X > 0` and an odd positive integer `M`, the marked terminal mass without
the length filter is
\[
  Θ°_{n,X}(M) = ∑_{h ∈ 𝓗_n(M)} ω(h)
    ∑_{w ∈ 𝓦(b_n, u_h, K_n),\ w \text{ admissible from } R_h} ω(w)\,
      ρ_{k_n}(\mathrm{src}(w, R_h) \bmod 3^{k_n}).
\]
Each central history `h` of generation `n` from `M` is extended by every first-crossing word
at scale `b_n`, terminal shift `u_h` and cap `K_n` that is admissible from the endpoint `R_h`
of `h`, and the reference density at level `k_n` is evaluated at the residue of the resulting
source. Both sums are finite.

## Main definitions

* `CollatzPosDens.markedMassUnfilteredWords n X M h`: the set of words
  `w ∈ 𝓦(b_n, u_h, K_n)` admissible from `R_h`.
* `CollatzPosDens.markedMassUnfiltered n X M`: the sum `Θ°_{n,X}(M)`.

## Main results

* `CollatzPosDens.markedMassUnfilteredWords_finite`: the inner index set is finite.
* `CollatzPosDens.markedMassUnfiltered_eq_sum`: `Θ°_{n,X}(M)` as a double `Finset` sum.
* `CollatzPosDens.markedMassUnfiltered_nonneg`: `0 ≤ Θ°_{n,X}(M)`.

## Implementation notes

Both sums are `finsum`s over sets, finite by
`CollatzPosDens.centralHistories_finite` and
`CollatzPosDens.firstCrossing_finite`. The weight of a history is that of its concatenated
word, `ω(h) = ω(ŵ(h))`. The source `src(w, R_h)` is a rational number, an integer when `w` is
admissible from `R_h`; its residue modulo `3^{k_n}` is taken to be that of its numerator, as in
`CollatzPosDens.weightedCentralSum`. The seed `M` is taken in `ℚ` and `X` in `ℝ`; the
oddness and positivity of `M` and the positivity of `X` are not needed to state the definition.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The words `w ∈ 𝓦(b_n, u_h, K_n)` that are admissible from the endpoint `R_h` of the
history `h`: the inner index set of `Θ°_{n,X}(M)`. -/
@[collatz_pos_dens "def_marked_mass_unfiltered"]
def markedMassUnfilteredWords (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale n) (historyShift n X M h) (cap n) ∧
    Admissible (historyEndpoint M h) w}

/-- Membership in the inner index set of `Θ°_{n,X}(M)`. -/
theorem mem_markedMassUnfilteredWords {n : ℕ} {X : ℝ} {M : ℚ} {h : Fin n → Word} {w : Word} :
    w ∈ markedMassUnfilteredWords n X M h ↔
      w ∈ firstCrossing (scale n) (historyShift n X M h) (cap n) ∧
        Admissible (historyEndpoint M h) w :=
  Iff.rfl

/-- The inner index set of `Θ°_{n,X}(M)` is finite. -/
theorem markedMassUnfilteredWords_finite (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) :
    (markedMassUnfilteredWords n X M h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- The marked terminal mass without the length filter,
`Θ°_{n,X}(M) = ∑_{h ∈ 𝓗_n(M)} ω(h) ∑_{w ∈ 𝓦(b_n,u_h,K_n), w admissible from R_h}
ω(w) ρ_{k_n}(src(w, R_h) mod 3^{k_n})`. -/
@[collatz_pos_dens "def_marked_mass_unfiltered"]
noncomputable def markedMassUnfiltered (n : ℕ) (X : ℝ) (M : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories M n, ((concatWord h).weight : ℝ) *
    ∑ᶠ w ∈ markedMassUnfilteredWords n X M h, (w.weight : ℝ) *
      refDensity (level n) ((src w (historyEndpoint M h)).num : ResidueGroup (level n))

/-- `Θ°_{n,X}(M)` as a double `Finset` sum over the finite index sets. -/
theorem markedMassUnfiltered_eq_sum (n : ℕ) (X : ℝ) (M : ℚ) :
    markedMassUnfiltered n X M =
      ∑ h ∈ (centralHistories_finite M n).toFinset,
        ((concatWord h).weight : ℝ) *
          ∑ w ∈ (markedMassUnfilteredWords_finite n X M h).toFinset, (w.weight : ℝ) *
            refDensity (level n) ((src w (historyEndpoint M h)).num : ResidueGroup (level n)) := by
  rw [markedMassUnfiltered,
    finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite M n)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (markedMassUnfilteredWords_finite n X M h)]

/-- The unfiltered marked mass is nonnegative. -/
theorem markedMassUnfiltered_nonneg (n : ℕ) (X : ℝ) (M : ℚ) :
    0 ≤ markedMassUnfiltered n X M := by
  rw [markedMassUnfiltered_eq_sum]
  refine Finset.sum_nonneg fun h _ => mul_nonneg ?_ (Finset.sum_nonneg fun w _ => ?_)
  · exact_mod_cast (Word.weight_pos _).le
  · exact mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

end CollatzPosDens
