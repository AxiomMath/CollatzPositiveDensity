/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Characters.FxOffsetLaw
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxSubmassLe
public import CollatzPosDens.Mixing.MxSubmassTotal
public import CollatzPosDens.Mixing.MxSubmassUnion
public import CollatzPosDens.Mixing.MxGateUnion
public import CollatzPosDens.Mixing.MxGateCover
public import CollatzPosDens.Mixing.MxGoodComplement

/-!
# The covering deficit of the gate union

For every integer `n ≥ 2^{131072}`, the submass of the gate union `𝒰_n` approximates the
reference law `μ_n` in `ℓ¹(G_n)`:
$$\sum_{y \in G_n} \bigl|\mu_n(y) - \mathrm{Sub}^n_{\mathcal U_n}(y)\bigr| \le n^{-9/8}.$$

By the offset law, `μ_n = Sub^n_{ℤ_{≥1}^n}`. Since `𝒰_n ⊆ ℤ_{≥1}^n`, additivity of the submass
on the two disjoint sets `𝒰_n` and `ℤ_{≥1}^n \ 𝒰_n` gives
`μ_n - Sub^n_{𝒰_n} = Sub^n_{ℤ_{≥1}^n \ 𝒰_n} ≥ 0`, all values being finite. Summing over `y`, the
left side is `𝐩(ℤ_{≥1}^n \ 𝒰_n)`. As `Gd_n ⊆ 𝒰_n`, this is at most `𝐩(ℤ_{≥1}^n \ Gd_n)`,
which is at most `n^{-9/8}`.

## Main results

* `CollatzPosDens.sum_abs_refLaw_sub_subMass_mxGateUnion_le`: the bound above.
* `CollatzPosDens.refLaw_sub_subMass_mxGateUnion_eq`: the pointwise identity
  `μ_n(y) - Sub^n_{𝒰_n}(y) = Sub^n_{ℤ_{≥1}^n \ 𝒰_n}(y)`.

## Implementation notes

The `[0, ∞]`-valued weights `μ_n(y)` and `Sub^n_{𝒰_n}(y)` enter the absolute value through
`ENNReal.toReal`; both are at most one, so this loses nothing. The bound `n^{-9/8}` is the real
power `(n : ℝ) ^ (-(9/8 : ℝ))`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Pointwise, `μ_n(y) - Sub^n_{𝒰_n}(y) = Sub^n_{ℤ_{≥1}^n \ 𝒰_n}(y)` (as real numbers). -/
theorem refLaw_sub_subMass_mxGateUnion_eq (n : ℕ) (y : ResidueGroup n) :
    (refLaw n y).toReal - (subMass n (mxGateUnion n) y).toReal =
      (subMass n ({w : Word | w.length = n} \ mxGateUnion n) y).toReal := by
  have hUS := mxGateUnion_subset_setOf_length n
  rw [← subMass_length_eq_refLaw, ← Set.union_sdiff_cancel hUS,
    subMass_union n Set.disjoint_sdiff_right, Set.union_sdiff_cancel hUS,
    ENNReal.toReal_add (subMass_ne_top_of_subset_length n hUS y)
      (subMass_ne_top_of_subset_length n Set.sdiff_subset y)]
  ring

/-- **Covering deficit.** For every integer `n ≥ 2^{131072}`,
`∑_{y ∈ G_n} |μ_n(y) - Sub^n_{𝒰_n}(y)| ≤ n^{-9/8}`. -/
@[collatz_pos_dens "lem_mx_cover_deficit"]
theorem sum_abs_refLaw_sub_subMass_mxGateUnion_le (n : ℕ) (hn : 2 ^ 131072 ≤ n) :
    ∑ y : ResidueGroup n, |(refLaw n y).toReal - (subMass n (mxGateUnion n) y).toReal| ≤
      (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
  simp_rw [refLaw_sub_subMass_mxGateUnion_eq, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [← ENNReal.toReal_sum fun y _ => subMass_ne_top_of_subset_length n Set.sdiff_subset y,
    sum_subMass]
  have hmono : geomMass ({w : Word | w.length = n} \ mxGateUnion n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(9 / 8 : ℝ))) :=
    (geomMass_mono (Set.sdiff_subset_sdiff_right (mxGood_subset_mxGateUnion n))).trans
      (geomMass_compl_mxGood_le n hn)
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono).trans_eq ?_
  exact ENNReal.toReal_ofReal (by positivity)

end CollatzPosDens
