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
public import CollatzPosDens.Maps.SyrPeriodic

/-!
# `s`-good seeds

Let `s ≥ 1` be an integer. An integer `M` is an *`s`-good seed* if `M` is odd, `3 ∤ M`,
`16^{b₀} s < M < 𝓜(s)`, `3M + 1 = 2^k s` for some `k ∈ ℕ`, `M` is not Syracuse-periodic, and the
weighted central sum at generation `N_*` satisfies `Z_{N_*}(M) > 2^{-23}`.

## Main definitions

* `CollatzPosDens.GoodSeed s M`: `M` is an `s`-good seed.

## Main results

* `CollatzPosDens.GoodSeed.pos`: an `s`-good seed is positive.
* `CollatzPosDens.GoodSeed.weightedCentralSum_pos`: an `s`-good seed has `0 < Z_{N_*}(M)`.
* `CollatzPosDens.GoodSeed.sixteen_pow_lt`: an `s`-good seed with `s ≥ 1` has `16^{b₀} < M`.

## Implementation notes

The seed is taken in `ℕ`: the lower bound forces a good integer seed to be positive, so this loses
nothing against the integer formulation. The weighted central sum is evaluated at the cast of `M`
to `ℚ`, which is how `Z_n` is defined. The condition is a structure with one named field per
clause, since consumers use different clauses.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `M` is an *`s`-good seed*: `M` is odd, `3 ∤ M`, `16^{b₀} s < M < 𝓜(s)`, `3M + 1 = 2^k s` for
some `k`, `M` is not Syracuse-periodic, and `Z_{N_*}(M) > 2^{-23}`. -/
@[collatz_pos_dens "def_good_seed"]
structure GoodSeed (s M : ℕ) : Prop where
  /-- A good seed is odd. -/
  odd : Odd M
  /-- A good seed is not divisible by `3`. -/
  not_three_dvd : ¬ 3 ∣ M
  /-- The lower bound `16^{b₀} s < M`. -/
  lower : 16 ^ scale 0 * s < M
  /-- The upper bound `M < 𝓜(s)`. -/
  upper : M < seedBound s
  /-- `3M + 1 = 2^k s` for some `k`. -/
  two_pow_mul : ∃ k : ℕ, 3 * M + 1 = 2 ^ k * s
  /-- A good seed is not Syracuse-periodic. -/
  not_syrPeriodic : ¬ SyrPeriodic M
  /-- The weighted central sum bound `2^{-23} < Z_{N_*}(M)`. -/
  lt_weightedCentralSum : (2 : ℝ)⁻¹ ^ 23 < weightedCentralSum generationThreshold (M : ℚ)

/-- A good seed is positive. -/
theorem GoodSeed.pos {s M : ℕ} (h : GoodSeed s M) : 0 < M :=
  h.odd.pos

/-- A good seed has positive weighted central sum `Z_{N_*}(M)`. -/
theorem GoodSeed.weightedCentralSum_pos {s M : ℕ} (h : GoodSeed s M) :
    0 < weightedCentralSum generationThreshold (M : ℚ) :=
  lt_trans (by positivity) h.lt_weightedCentralSum

/-- An `s`-good seed with `s ≥ 1` satisfies `16^{b₀} < M`. -/
theorem GoodSeed.sixteen_pow_lt {s M : ℕ} (h : GoodSeed s M) (hs : 0 < s) :
    16 ^ scale 0 < M :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hs) h.lower

end CollatzPosDens
