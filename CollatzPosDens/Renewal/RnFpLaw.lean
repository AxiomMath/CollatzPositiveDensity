/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpWord
public import CollatzPosDens.Renewal.RnHoldList

/-!
# The first-passage law

For a level `s` and a point `x ∈ ℤ × ℤ`, the first-passage law is
`F_s(x) = ∑_{K ≥ 1} ∑_h η^{⊗K}(h)`, the inner sum over the first-passage words
`h = (h_1, …, h_K) ∈ 𝒫^K` for level `s` with `h_1 + ⋯ + h_K = x`: the probability that the
random walk with steps drawn from the holding-time law `η` first exceeds level `s` (in its second
coordinate) at the point `x`.

## Main definitions

* `CollatzPosDens.firstPassageLawWeight`: the weight `η^{⊗K}(h)` of a word `h`.
* `CollatzPosDens.firstPassageLaw`: the first-passage law `F_s(x)`.

## Main results

* `CollatzPosDens.firstPassageLaw_def`: `F_s(x)` as a sum over the first-passage words with
  sum `x`.
* `CollatzPosDens.firstPassageLawWeight_cons`: the weight splits off the first letter.
* `CollatzPosDens.firstPassageLaw_nonneg`: `F_s(x) ≥ 0`.
* `CollatzPosDens.firstPassageLaw_of_neg`: `F_s(x) = 0` for a negative level `s`.

## Implementation notes

Words are lists of points of `ℤ × ℤ`, as in `IsFirstPassageWord`; a list carries its length `K`,
and the condition `K ≥ 1` and the membership `h ∈ 𝒫^K` are part of `IsFirstPassageWord`, so the
double sum over `K ≥ 1` and `h ∈ 𝒫^K` is a single sum over lists. The weight of a word `h` is the
hold-list weight `η^{⊗K}` of the tuple `i ↦ (j(h_i), l(h_i))`, where the first coordinate is
read in `ℕ` through `Int.toNat`; on `𝒫 = ℤ_{≥1} × ℤ` this is the identity, so the weight is the
source's `∏_i η(h_i)` (`firstPassageLawWeight_cons`).

The sum is an unconditional sum `tsum` of reals over the subtype of first-passage words for `s`
with sum `x`; only finitely many of its terms are nonzero (`firstPassageLaw_finite`), so it
agrees with the finite sum of the source. The level `s` is taken in `ℤ` rather than in `ℕ`,
which generalizes the source: for a negative level there is no first-passage word and the law
vanishes (`firstPassageLaw_of_neg`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §6.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The hold-list weight `η^{⊗K}(h) = ∏_i η(h_i)` of a word `h = [h_1, …, h_K]` of points of
`ℤ × ℤ`, the first coordinate of each point read in `ℕ`. -/
noncomputable def firstPassageLawWeight (h : List (ℤ × ℤ)) : ℝ :=
  holdListLaw fun i : Fin h.length => ((h.get i).1.toNat, (h.get i).2)

/-- The first-passage law `F_s(x) = ∑_{K ≥ 1} ∑_h η^{⊗K}(h)`, the sum over the first-passage
words `h = (h_1, …, h_K)` for level `s` with `h_1 + ⋯ + h_K = x`. -/
@[collatz_pos_dens "def_rn_fp_law"]
noncomputable def firstPassageLaw (s : ℤ) (x : ℤ × ℤ) : ℝ :=
  ∑' h : {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = x}, firstPassageLawWeight h.1

/-- Unfolding lemma for `firstPassageLaw`. -/
theorem firstPassageLaw_def (s : ℤ) (x : ℤ × ℤ) :
    firstPassageLaw s x =
      ∑' h : {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = x}, firstPassageLawWeight h.1 :=
  rfl

/-- Unfolding lemma for `firstPassageLawWeight`. -/
theorem firstPassageLawWeight_def (h : List (ℤ × ℤ)) :
    firstPassageLawWeight h =
      holdListLaw fun i : Fin h.length => ((h.get i).1.toNat, (h.get i).2) :=
  rfl

/-- The weight of the empty word is `1`. -/
@[simp]
theorem firstPassageLawWeight_nil : firstPassageLawWeight [] = 1 :=
  holdListLaw_zero _

/-- The weight of a word splits off its first letter. -/
@[simp]
theorem firstPassageLawWeight_cons (p : ℤ × ℤ) (t : List (ℤ × ℤ)) :
    firstPassageLawWeight (p :: t) = holdLaw p.1.toNat p.2 * firstPassageLawWeight t := by
  rw [firstPassageLawWeight, holdListLaw_succ]
  rfl

/-- The weight of a word is nonnegative. -/
theorem firstPassageLawWeight_nonneg (h : List (ℤ × ℤ)) : 0 ≤ firstPassageLawWeight h :=
  holdListLaw_nonneg _

/-- The first-passage law is nonnegative. -/
theorem firstPassageLaw_nonneg (s : ℤ) (x : ℤ × ℤ) : 0 ≤ firstPassageLaw s x :=
  tsum_nonneg fun h => firstPassageLawWeight_nonneg h.1

/-- The first-passage law vanishes at a negative level. -/
theorem firstPassageLaw_of_neg {s : ℤ} (hs : s < 0) (x : ℤ × ℤ) : firstPassageLaw s x = 0 := by
  have : IsEmpty {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = x} :=
    ⟨fun h => absurd h.2.1.nonneg (not_le.2 hs)⟩
  simp [firstPassageLaw]

end CollatzPosDens
