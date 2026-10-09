/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.RoundedOffset
public import CollatzPosDens.Maps.Weight

/-!
# The five-block selector

For five words `v₀, …, v₄`, the *five-block selector* `Sel(v₀, …, v₄)` is the proposition
$$\tfrac38 \le \mathrm{rd}_9(v_0) + \omega(v_0)\,\mathrm{rd}_6(v_1) \le \tfrac{19}8,\quad
  \mathrm{rd}_6(v_1) \le 16,\quad \mathrm{rd}_3(v_2) \le 16,\quad
  \mathrm{rd}_0(v_3) \le 64,\quad \mathrm{rd}_{-3}(v_4) \le 256,$$
where `rd_p` is the rounded offset and `ω` the weight of a word. It restricts the first five
central words of a history; every quantity involved is an exact rational, so the selector is
decidable.

## Main definitions

* `CollatzPosDens.fiveBlockSelector v₀ v₁ v₂ v₃ v₄`: the proposition `Sel(v₀, …, v₄)`.

## Main results

* `CollatzPosDens.fiveBlockSelector_iff`: the selector unfolded into its six inequalities.
* A `Decidable` instance for `fiveBlockSelector v₀ v₁ v₂ v₃ v₄`.

## Implementation notes

The double inequality is kept as two conjuncts, so the selector is a conjunction of six
rational inequalities, each of which can be extracted by projection.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The five-block selector `Sel(v₀, …, v₄)`:
`3/8 ≤ rd₉(v₀) + ω(v₀) rd₆(v₁) ≤ 19/8`, `rd₆(v₁) ≤ 16`, `rd₃(v₂) ≤ 16`, `rd₀(v₃) ≤ 64` and
`rd₋₃(v₄) ≤ 256`. -/
@[collatz_pos_dens "def_s05_selector"]
def fiveBlockSelector (v₀ v₁ v₂ v₃ v₄ : Word) : Prop :=
  3 / 8 ≤ roundedOffset 9 v₀ + v₀.weight * roundedOffset 6 v₁ ∧
    roundedOffset 9 v₀ + v₀.weight * roundedOffset 6 v₁ ≤ 19 / 8 ∧
    roundedOffset 6 v₁ ≤ 16 ∧ roundedOffset 3 v₂ ≤ 16 ∧ roundedOffset 0 v₃ ≤ 64 ∧
    roundedOffset (-3) v₄ ≤ 256

/-- The five-block selector as its six rational inequalities. -/
theorem fiveBlockSelector_iff (v₀ v₁ v₂ v₃ v₄ : Word) :
    fiveBlockSelector v₀ v₁ v₂ v₃ v₄ ↔
      3 / 8 ≤ roundedOffset 9 v₀ + v₀.weight * roundedOffset 6 v₁ ∧
      roundedOffset 9 v₀ + v₀.weight * roundedOffset 6 v₁ ≤ 19 / 8 ∧
      roundedOffset 6 v₁ ≤ 16 ∧ roundedOffset 3 v₂ ≤ 16 ∧ roundedOffset 0 v₃ ≤ 64 ∧
      roundedOffset (-3) v₄ ≤ 256 :=
  Iff.rfl

/-- The selector is decidable: it is a conjunction of inequalities between rationals. -/
instance fiveBlockSelector.instDecidable (v₀ v₁ v₂ v₃ v₄ : Word) :
    Decidable (fiveBlockSelector v₀ v₁ v₂ v₃ v₄) :=
  decidable_of_iff' _ (fiveBlockSelector_iff v₀ v₁ v₂ v₃ v₄)

end CollatzPosDens
