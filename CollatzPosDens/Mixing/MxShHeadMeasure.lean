/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02DyadicReduction
public import CollatzPosDens.Mixing.MxShGate

/-!
# Head measure of a gate

For natural numbers `n`, `d`, `j` and a residue `y ∈ G_n = ℤ/3^nℤ`, the *head measure* of the gate
`(d, j)` at `y` is the normalized number of exposed patterns whose offset reduces to `y`:
$$\Gamma^{\mathrm{sh}}_{n,d,j}(y) = 2^{-(H^{\mathrm{sh}}_n - 1)}\,
  \#\{\beta \in \mathrm{Hd}^{\mathrm{sh}}_n(d,j) : [\mathrm{Of}(\beta)]_n = y\}
  \in \mathbb{Q}_{\ge 0}.$$
Here `Of(β) ∈ ℤ[1/2]` is the subset offset and `[·]_n : ℤ[1/2] → G_n` the dyadic reduction. Each
exposed pattern is counted at exactly one residue, so the head measures over `y ∈ G_n` add up to
`2^{-(H^{sh}_n - 1)} #Hd^{sh}_n(d, j)`.

## Main definitions

* `CollatzPosDens.shHeadMeasure`: the head measure `Γ^sh_{n,d,j}(y)`.

## Main results

* `CollatzPosDens.setOffset_mem_dyadicRationals`: the subset offset is a dyadic rational.
* `CollatzPosDens.shHeadMeasure_nonneg`: `0 ≤ Γ^sh_{n,d,j}(y)`.
* `CollatzPosDens.sum_shHeadMeasure`:
  `∑_{y ∈ G_n} Γ^sh_{n,d,j}(y) = 2^{-(H^{sh}_n - 1)} #Hd^{sh}_n(d, j)`.

## Implementation notes

The head measure is defined for all natural numbers `n`, not only for `n ≥ 1`. The value lies in
`ℚ`, and `2^{-(H^{sh}_n - 1)}` is written `(2 ^ (H^{sh}_n - 1))⁻¹` with natural subtraction, which
is the intended value for `n ≥ 1`, where `H^{sh}_n ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The subset offset `Of(S)` is a dyadic rational. -/
theorem setOffset_mem_dyadicRationals (S : Finset ℕ) : setOffset S ∈ dyadicRationals := by
  unfold setOffset
  refine Subalgebra.sum_mem _ fun s _ => ?_
  have h := intCast_div_two_pow_mem ((3 : ℤ) ^ #(S.filter (· < s))) s
  push_cast at h
  rwa [div_eq_mul_inv] at h

/-- The head measure `Γ^sh_{n,d,j}(y) = 2^{-(H^sh_n - 1)} #{β ∈ Hd^sh_n(d, j) : [Of(β)]_n = y}`
of the gate `(d, j)` at the residue `y ∈ G_n`. -/
@[collatz_pos_dens "def_mx_sh_head_measure"]
noncomputable def shHeadMeasure (n d j : ℕ) (y : ResidueGroup n) : ℚ :=
  ((2 : ℚ) ^ (shHeight n - 1))⁻¹ *
    #{β ∈ shRetainedHeads n d j |
      dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩ = y}

/-- Unfolding lemma for `shHeadMeasure`. -/
theorem shHeadMeasure_def (n d j : ℕ) (y : ResidueGroup n) :
    shHeadMeasure n d j y = ((2 : ℚ) ^ (shHeight n - 1))⁻¹ *
      #{β ∈ shRetainedHeads n d j |
        dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩ = y} :=
  rfl

/-- The head measure is nonnegative. -/
theorem shHeadMeasure_nonneg (n d j : ℕ) (y : ResidueGroup n) : 0 ≤ shHeadMeasure n d j y := by
  rw [shHeadMeasure_def]
  positivity

/-- The head measures over all residues add up to the normalized number of exposed patterns:
`∑_{y ∈ G_n} Γ^sh_{n,d,j}(y) = 2^{-(H^sh_n - 1)} #Hd^sh_n(d, j)`. -/
theorem sum_shHeadMeasure (n d j : ℕ) :
    ∑ y : ResidueGroup n, shHeadMeasure n d j y =
      ((2 : ℚ) ^ (shHeight n - 1))⁻¹ * #(shRetainedHeads n d j) := by
  simp_rw [shHeadMeasure_def]
  rw [← Finset.mul_sum]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := fun β : Finset ℕ =>
      dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩)
    (t := (univ : Finset (ResidueGroup n))) (fun _ _ => mem_univ _)]
  push_cast
  rfl

end CollatzPosDens
