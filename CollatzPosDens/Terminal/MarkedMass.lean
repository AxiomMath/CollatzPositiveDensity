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
# The marked terminal mass `Θ_{n,X}(M)`

For `n : ℕ`, an external scale `X` and a starting point `M`, the marked terminal mass is
$$\Theta_{n,X}(M) = \sum_{h \in \mathcal H_n(M)} \omega(h)
  \sum_{w} \omega(w)\, \rho_{k_n}\bigl(\mathrm{src}(w, R_h) \bmod 3^{k_n}\bigr),$$
where the inner sum runs over the words `w ∈ 𝒲(b_n, u_h, K_n)` satisfying the length condition
`Λ_{b_n,u_h}(w)` and admissible from the endpoint `R_h` of `h`. Here `b_n` is the scale, `K_n`
the cap, `k_n = ⌊b_n / 4⌋` the level, `u_h = u_{n,X}(R_h)` the terminal shift of `h`, and
`ω(h) = ω(ŵ(h))` the weight of the concatenated word of `h`. Both sums are finite, since
`𝓗_n(M)` and every first-crossing family `𝒲(b, u, K)` are finite.

## Main definitions

* `CollatzPosDens.markedMassWords n X M h`: the words `w` of the inner sum attached to `h`.
* `CollatzPosDens.markedMass n X M`: the marked terminal mass `Θ_{n,X}(M)`.

## Main results

* `CollatzPosDens.mem_markedMassWords`: membership in the inner index set.
* `CollatzPosDens.markedMassWords_finite`: the inner index set is finite.
* `CollatzPosDens.markedMass_eq_sum`: `Θ_{n,X}(M)` as an iterated `Finset` sum.
* `CollatzPosDens.markedMass_nonneg`: `0 ≤ Θ_{n,X}(M)`.

## Implementation notes

Both sums are `finsum`s over sets; these sets are finite (`CollatzPosDens.centralHistories_finite`,
`CollatzPosDens.markedMassWords_finite`), so the `finsum`s are finite sums and the definition
needs no hypothesis. The inner index set is the set of `w ∈ 𝒲(b_n, u_h, K_n)` admissible from
`R_h` and satisfying the length condition `Λ_{b_n,u_h}(w)`.

The endpoint `R_h` and the source `src(w, R_h)` are rational numbers, integers when `w` is
admissible from `R_h` and `R_h` is an integer; the residue of `src(w, R_h)` modulo `3^{k_n}` is
taken to be that of its numerator, as in `CollatzPosDens.weightedCentralSum`. The shift
`u_h ∈ ℕ` is cast to `ℤ` to index the first-crossing family. The positivity of `X` and the
oddness and positivity of `M` are not needed to state the definition.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The words of the inner sum of `Θ_{n,X}(M)` attached to a history `h`: the words
`w ∈ 𝒲(b_n, u_h, K_n)` with `Λ_{b_n,u_h}(w)` that are admissible from the endpoint `R_h`. -/
def markedMassWords (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale n) (historyShift n X M h) (cap n) ∧
    LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w}

/-- The marked terminal mass
`Θ_{n,X}(M) = ∑_{h ∈ 𝓗_n(M)} ω(h) ∑_w ω(w) ρ_{k_n}(src(w, R_h) mod 3^{k_n})`, the inner sum over
`w ∈ 𝒲(b_n, u_h, K_n)` with `Λ_{b_n,u_h}(w)` and `w` admissible from `R_h`. -/
@[collatz_pos_dens "def_marked_mass"]
noncomputable def markedMass (n : ℕ) (X : ℝ) (M : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories M n, ((concatWord h).weight : ℝ) *
    ∑ᶠ w ∈ markedMassWords n X M h, (w.weight : ℝ) *
      refDensity (level n) ((src w (historyEndpoint M h)).num : ResidueGroup (level n))

/-- Membership in the inner index set of `Θ_{n,X}(M)`. -/
theorem mem_markedMassWords {X : ℝ} {M : ℚ} {h : Fin n → Word} {w : Word} :
    w ∈ markedMassWords n X M h ↔
      w ∈ firstCrossing (scale n) (historyShift n X M h) (cap n) ∧
        LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w :=
  Iff.rfl

/-- The inner index set of `Θ_{n,X}(M)` is finite. -/
theorem markedMassWords_finite (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) :
    (markedMassWords n X M h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- `Θ_{n,X}(M)` as an iterated `Finset` sum over the finite index sets. -/
theorem markedMass_eq_sum (n : ℕ) (X : ℝ) (M : ℚ) :
    markedMass n X M = ∑ h ∈ (centralHistories_finite M n).toFinset,
      ((concatWord h).weight : ℝ) * ∑ w ∈ (markedMassWords_finite n X M h).toFinset,
        (w.weight : ℝ) *
          refDensity (level n) ((src w (historyEndpoint M h)).num : ResidueGroup (level n)) := by
  rw [markedMass,
    finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite M n)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (markedMassWords_finite n X M h)]

/-- The marked terminal mass is nonnegative. -/
theorem markedMass_nonneg (n : ℕ) (X : ℝ) (M : ℚ) : 0 ≤ markedMass n X M := by
  rw [markedMass_eq_sum]
  refine Finset.sum_nonneg fun h _ => mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) ?_
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

end CollatzPosDens
