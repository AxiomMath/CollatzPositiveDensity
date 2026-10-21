/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.Case3.C3InitException
public import CollatzPosDens.Case3.C3PaidPassage
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.Transfer.S02Z
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The filtered paid marginal

Fix a level `n` and a residue `ξ ∈ G_n`, and let whiteness and the gap refer to
`(n, ξ, ε_*)`. For a black point `e ∈ 𝒫` with gap `ω = gap(e)` and a lattice point `x`, the
*filtered paid marginal* at a Fourier index `ι ∈ 𝔍` is
```
F^gd_{e,ι}(x) = ∑_{π ∈ Π_ω \ 𝓑_init(ι, ω), Bp_{|π|}(π) = x}
  bw^⊗(π) exp(-z_* N^*(e, π; |π|)) ∈ [0, ∞],
```
the paid passage mass `F̃_e(x)` with the passage lists of the common initial exception
`𝓑_init(ι, ω)` removed. Since `𝓑_init(ι, ω) ⊆ Π_ω`, the paid passage mass splits as the filtered
marginal plus the part carried by `𝓑_init(ι, ω)`; in particular `F^gd_{e,ι}(x) ≤ F̃_e(x)`.

## Main definitions

* `CollatzPosDens.c3GoodMarginal ι n ξ e x`: the filtered paid marginal
  `F^gd_{e,ι}(x) ∈ [0, ∞]`.

## Main results

* `CollatzPosDens.c3GoodMarginal_add_tsum_c3InitException`: `F̃_e(x)` is `F^gd_{e,ι}(x)` plus
  the sum of the same terms over `π ∈ 𝓑_init(ι, ω)`.
* `CollatzPosDens.c3GoodMarginal_le_c3PaidPassage`: `F^gd_{e,ι}(x) ≤ F̃_e(x)`.

## Implementation notes

As for `CollatzPosDens.c3PaidPassage`, the marginal is a sum of nonnegative terms that need
not be summable a priori, so it is an `ℝ≥0∞`-valued `tsum`; the gap is an integer, nonnegative
for black points, and the index sets are taken at its `Int.toNat`. The definition makes sense
for every `e : ℤ × ℤ`; blackness of `e` is a hypothesis of the results that need it only.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §10.5.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The summand `bw^⊗(π) exp(-z_* N^*(e, π; |π|))` of the paid masses at `x`, set to `0`
unless `Bp_{|π|}(π) = x`. -/
noncomputable abbrev c3PaidTerm (n : ℕ) (ξ : ResidueGroup n) (e x : ℤ × ℤ)
    (π : List (List ℤ × ℤ)) : ℝ≥0∞ :=
  if chBlockPath π π.length = x then
    ENNReal.ofReal (trListWeight π * Real.exp (-(zStar : ℝ) * trCount n ξ e π π.length))
  else 0

/-- The filtered paid marginal of a point `e` at `x`, at the Fourier index `ι`:
`F^gd_{e,ι}(x) = ∑_{π ∈ Π_ω \ 𝓑_init(ι, ω), Bp_{|π|}(π) = x} bw^⊗(π) exp(-z_* N^*(e, π; |π|))`,
where `ω = gap(e)` is the gap for `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_c3_good_marginal"]
noncomputable def c3GoodMarginal (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (e x : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' π : (trPassage (trGap n ξ (epsStar : ℝ) e).toNat \
      c3InitException ι (trGap n ξ (epsStar : ℝ) e).toNat :),
    if chBlockPath π.1 π.1.length = x then
      ENNReal.ofReal (trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length))
    else 0

/-- `F^gd_{e,ι}(x)` is the sum of `c3PaidTerm` over `Π_ω \ 𝓑_init(ι, ω)`. -/
lemma c3GoodMarginal_eq_tsum (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (e x : ℤ × ℤ) :
    c3GoodMarginal ι n ξ e x =
      ∑' π : (trPassage (trGap n ξ (epsStar : ℝ) e).toNat \
        c3InitException ι (trGap n ξ (epsStar : ℝ) e).toNat :), c3PaidTerm n ξ e x π :=
  rfl

/-- `F̃_e(x)` is the sum of `c3PaidTerm` over `Π_ω`. -/
lemma c3PaidPassage_eq_tsum_c3PaidTerm (n : ℕ) (ξ : ResidueGroup n) (e x : ℤ × ℤ) :
    c3PaidPassage n ξ e x =
      ∑' π : trPassage (trGap n ξ (epsStar : ℝ) e).toNat, c3PaidTerm n ξ e x π :=
  rfl

/-- **Splitting off the initial exception.** The paid passage mass `F̃_e(x)` is the filtered
marginal `F^gd_{e,ι}(x)` plus the sum of the same terms over `π ∈ 𝓑_init(ι, ω)`. -/
theorem c3GoodMarginal_add_tsum_c3InitException (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n)
    (e x : ℤ × ℤ) :
    c3GoodMarginal ι n ξ e x +
        ∑' π : c3InitException ι (trGap n ξ (epsStar : ℝ) e).toNat, c3PaidTerm n ξ e x π =
      c3PaidPassage n ξ e x := by
  set ω := (trGap n ξ (epsStar : ℝ) e).toNat
  rw [c3GoodMarginal_eq_tsum, c3PaidPassage_eq_tsum_c3PaidTerm,
    ← Summable.tsum_union_disjoint Set.disjoint_sdiff_left ENNReal.summable ENNReal.summable,
    Set.sdiff_union_of_subset (c3InitException_subset_trPassage ι ω)]

/-- The filtered marginal is at most the paid passage mass: `F^gd_{e,ι}(x) ≤ F̃_e(x)`. -/
theorem c3GoodMarginal_le_c3PaidPassage (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n)
    (e x : ℤ × ℤ) :
    c3GoodMarginal ι n ξ e x ≤ c3PaidPassage n ξ e x :=
  ENNReal.tsum_mono_subtype (c3PaidTerm n ξ e x) Set.sdiff_subset

end CollatzPosDens
