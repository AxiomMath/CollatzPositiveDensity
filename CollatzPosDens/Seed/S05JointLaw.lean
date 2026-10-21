/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawCdf
public import CollatzPosDens.Seed.S05PrefixResidue

/-!
# The joint offset law

For integers `D ≥ q ≥ 0`, a residue `r ∈ G_q` and a real `x`, the *joint offset law*
$$\mathsf F^{\mathrm{jt}}_{D,q}(r, x) = \mathbf p\bigl(\{u \in \mathbb Z_{\ge 1}^D :
  \mathrm{off}(u) \le x,\ \mathrm{pr}_q(u) = r\}\bigr) \in [0, \infty]$$
is the geometric mass of the words of length `D` with offset at most `x` whose prefix of length
`q` has offset congruent to `r` modulo `3^q`. Summing over `r ∈ G_q` recovers the offset
distribution function `𝖥_D(x)`.

## Main definitions

* `CollatzPosDens.jointLaw D q r x`: the joint offset law `𝖥^{jt}_{D,q}(r, x)`.

## Main results

* `CollatzPosDens.jointLaw_mono`: `𝖥^{jt}_{D,q}(r, ·)` is nondecreasing.
* `CollatzPosDens.jointLaw_le_offlawCdf`: `𝖥^{jt}_{D,q}(r, x) ≤ 𝖥_D(x)`.
* `CollatzPosDens.sum_jointLaw`: `∑_{r ∈ G_q} 𝖥^{jt}_{D,q}(r, x) = 𝖥_D(x)`.

## Implementation notes

The definition is stated for all `D, q ∈ ℕ`; [mazur2026] restricts to `D ≥ q`, where the prefix
`u_{≤ q}` has length exactly `q`. Words of length `D` are lists of positive integers of length
`D`, as in `CollatzPosDens.offlawCdf`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The **joint offset law** `𝖥^{jt}_{D,q}(r, x) = 𝐩({u ∈ ℤ_{≥1}^D : off(u) ≤ x, pr_q(u) = r})`,
the geometric mass of the words of length `D` with offset at most `x` and prefix residue `r`. -/
@[collatz_pos_dens "def_s05_joint_law"]
noncomputable def jointLaw (D q : ℕ) (r : ResidueGroup q) (x : ℝ) : ℝ≥0∞ :=
  geomMass {u : Word | u.length = D ∧ (off u : ℝ) ≤ x ∧ prefixResidue q u = r}

/-- Unfolding lemma for `jointLaw`. -/
theorem jointLaw_def (D q : ℕ) (r : ResidueGroup q) (x : ℝ) :
    jointLaw D q r x =
      geomMass {u : Word | u.length = D ∧ (off u : ℝ) ≤ x ∧ prefixResidue q u = r} :=
  rfl

/-- The joint offset law is nondecreasing in `x`. -/
theorem jointLaw_mono (D q : ℕ) (r : ResidueGroup q) : Monotone (jointLaw D q r) :=
  fun _ _ hxy => geomMass_mono fun _ hu => ⟨hu.1, hu.2.1.trans hxy, hu.2.2⟩

/-- The joint offset law is at most the offset distribution function. -/
theorem jointLaw_le_offlawCdf (D q : ℕ) (r : ResidueGroup q) (x : ℝ) :
    jointLaw D q r x ≤ offlawCdf D x :=
  geomMass_mono fun _ hu => ⟨hu.1, hu.2.1⟩

/-- Summing the joint offset law over all residues `r ∈ G_q` gives the offset distribution
function: `∑_{r ∈ G_q} 𝖥^{jt}_{D,q}(r, x) = 𝖥_D(x)`. -/
theorem sum_jointLaw (D q : ℕ) (x : ℝ) :
    ∑ r : ResidueGroup q, jointLaw D q r x = offlawCdf D x := by
  simp only [jointLaw_def, offlawCdf_def, geomMass_eq_tsum_indicator]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun u => ?_
  rw [Finset.sum_eq_single (prefixResidue q u)]
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, and_true]
  · intro r _ hr
    exact Set.indicator_of_notMem (fun h => hr h.2.2.symm) _
  · exact fun h => absurd (Finset.mem_univ _) h

end CollatzPosDens
