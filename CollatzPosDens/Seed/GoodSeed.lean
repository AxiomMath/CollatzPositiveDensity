/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.FirstCrossing.Scales

/-!
# Good seeds

An integer `M` is a *good seed* if `M` is odd, `3 ∤ M`, `16^{b₀} < M < 𝓜`, `3M + 1` is a power
of `4`, and the weighted central sum at generation `N_*` satisfies `Z_{N_*}(M) > 2^{-23}`.

## Main definitions

* `CollatzPosDens.GoodSeed M`: `M` is a good seed.

## Main results

* `CollatzPosDens.GoodSeed.pos`: a good seed is positive.
* `CollatzPosDens.GoodSeed.weightedCentralSum_pos`: a good seed has `0 < Z_{N_*}(M)`.

## Implementation notes

The seed is taken in `ℕ`: the lower bound `16^{b₀} < M` forces a good integer seed to be
positive, so this loses nothing against the integer formulation. The weighted central sum is
evaluated at the cast of `M` to `ℚ`, which is how `Z_n` is defined. The condition is a
structure with one named field per clause, since consumers use different clauses.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `M` is a *good seed*: `M` is odd, `3 ∤ M`, `16^{b₀} < M < 𝓜`, `3M + 1` is a power of `4`,
and `Z_{N_*}(M) > 2^{-23}`. -/
@[collatz_pos_dens "def_good_seed"]
structure GoodSeed (M : ℕ) : Prop where
  /-- A good seed is odd. -/
  odd : Odd M
  /-- A good seed is not divisible by `3`. -/
  not_three_dvd : ¬ 3 ∣ M
  /-- The lower bound `16^{b₀} < M`. -/
  lower : 16 ^ scale 0 < M
  /-- The upper bound `M < 𝓜`. -/
  upper : M < seedBound
  /-- `3M + 1` is a power of `4`. -/
  pow_four : ∃ k : ℕ, 3 * M + 1 = 4 ^ k
  /-- The weighted central sum bound `2^{-23} < Z_{N_*}(M)`. -/
  lt_weightedCentralSum : (2 : ℝ)⁻¹ ^ 23 < weightedCentralSum generationThreshold (M : ℚ)

/-- A good seed is positive. -/
theorem GoodSeed.pos {M : ℕ} (h : GoodSeed M) : 0 < M :=
  h.odd.pos

/-- A good seed has positive weighted central sum `Z_{N_*}(M)`. -/
theorem GoodSeed.weightedCentralSum_pos {M : ℕ} (h : GoodSeed M) :
    0 < weightedCentralSum generationThreshold (M : ℚ) :=
  lt_trans (by positivity) h.lt_weightedCentralSum

end CollatzPosDens
