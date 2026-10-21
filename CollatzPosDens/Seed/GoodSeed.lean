/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Recipe.SeedShift
public import CollatzPosDens.Recipe.TailMargin
public import CollatzPosDens.Recipe.ZMargin
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Maps.SyrPeriodic

/-!
# `t`-good seeds

Let `t` be a positive integer with `3 ∤ t`, let `q_*` be the conductor, `σ_sd` the seed shift,
`θ_tl` the tail margin and `ε_Z` the central-sum margin. An integer `t₁` is a *`t`-good seed* if
there is `a ∈ ℕ` with `a < σ_sd + 4 + 4 · 3^{q_*}` and `3 t₁ + 1 = 2^a t`, `t₁` is odd, `t₁` is not
Syracuse-periodic, `2^{σ_sd} t < t₁ < 𝓜(t)`, and the weighted central sum at generation `N_*`
satisfies `Z_{N_*}(t₁) > θ_tl + ε_Z`. With the values of the parameters, the conditions read
`a < 66180 + 4 · 3^{q_*}`, `2^{66176} t < t₁ < 2^{5 · 3^{q_*}} t` and
`Z_{N_*}(t₁) > 6/7 + 2^{-28}`; here `σ_sd = 4 b₀ = 66176` with first scale `b₀ = 16544`, and
`N_* = 9853`.

## Main definitions

* `CollatzPosDens.GoodSeed t M`: `M` is a `t`-good seed.

## Main results

* `CollatzPosDens.GoodSeed.exists_two_pow_mul`, `CollatzPosDens.GoodSeed.two_pow_66176_mul_lt`,
  `CollatzPosDens.GoodSeed.add_two_inv_pow_lt_weightedCentralSum`: the clauses of a good seed
  with the values of the parameters.
* `CollatzPosDens.GoodSeed.pos`: a `t`-good seed is positive.
* `CollatzPosDens.GoodSeed.weightedCentralSum_pos`: a `t`-good seed has `0 < Z_{N_*}(M)`.
* `CollatzPosDens.GoodSeed.two_pow_66176_lt`: a `t`-good seed with `t ≥ 1` has `2^{66176} < M`.
* `CollatzPosDens.GoodSeed.two_pow_thirtySix_lt`: a `t`-good seed with `t ≥ 1` has
  `2^{36} < M`.

## Implementation notes

The seed is taken in `ℕ`: the lower bound `2^{σ_sd} t < t₁` forces a good integer seed to be
positive, so this loses nothing against the integer formulation. The standing hypotheses `t ≥ 1`
and `3 ∤ t` are not needed to state the definition and are left to the results that use them. The
weighted central sum is evaluated at the cast of `M` to `ℚ`, which is how `Z_n` is defined, and is
compared in `ℝ` with the rational margins cast to `ℝ`. The condition is a structure with one named
field per clause.

## References

* [Mazur, *Collatz positive density*], §16.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- `M` is a *`t`-good seed*: `3M + 1 = 2^a t` for some `a < σ_sd + 4 + 4 · 3^{q_*}`, `M` is odd
and not Syracuse-periodic, `2^{σ_sd} t < M < 𝓜(t)`, and `Z_{N_*}(M) > θ_tl + ε_Z`. -/
@[collatz_pos_dens "def_good_seed"]
structure GoodSeed (t M : ℕ) : Prop where
  /-- `3M + 1 = 2^a t` for some `a < σ_sd + 4 + 4 · 3^{q_*}`. -/
  two_pow_mul : ∃ a < seedShift + 4 + 4 * 3 ^ conductor, 3 * M + 1 = 2 ^ a * t
  /-- A good seed is odd. -/
  odd : Odd M
  /-- A good seed is not Syracuse-periodic. -/
  not_syrPeriodic : ¬ SyrPeriodic M
  /-- The lower bound `2^{σ_sd} t < M`. -/
  lower : 2 ^ seedShift * t < M
  /-- The upper bound `M < 𝓜(t)`. -/
  upper : M < seedBound t
  /-- The weighted central sum bound `θ_tl + ε_Z < Z_{N_*}(M)`. -/
  lt_weightedCentralSum :
    (tailMargin : ℝ) + (centralSumMargin : ℝ) < weightedCentralSum generationThreshold (M : ℚ)

/-- Arithmetic for the exponent clause, with the large summand `Q` left opaque so that it is
never evaluated. -/
private theorem lt_66180_add_of_lt {a Q : ℕ} (h : a < 66176 + 4 + Q) : a < 66180 + Q := by
  omega

/-- The exponent clause with the value `σ_sd = 66176`: `3M + 1 = 2^a t` for some
`a < 66180 + 4 · 3^{q_*}`. -/
theorem GoodSeed.exists_two_pow_mul {t M : ℕ} (h : GoodSeed t M) :
    ∃ a < 66180 + 4 * 3 ^ conductor, 3 * M + 1 = 2 ^ a * t := by
  obtain ⟨a, ha, he⟩ := h.two_pow_mul
  rw [seedShift_eq] at ha
  exact ⟨a, lt_66180_add_of_lt ha, he⟩

/-- The lower bound with the value `σ_sd = 66176`: `2^{66176} t < M`. -/
theorem GoodSeed.two_pow_66176_mul_lt {t M : ℕ} (h : GoodSeed t M) : 2 ^ 66176 * t < M := by
  have := h.lower
  rwa [seedShift_eq] at this

/-- The weighted central sum bound with the values of the margins:
`6/7 + 2^{-28} < Z_{N_*}(M)`. -/
theorem GoodSeed.add_two_inv_pow_lt_weightedCentralSum {t M : ℕ} (h : GoodSeed t M) :
    (6 / 7 : ℝ) + (2 : ℝ)⁻¹ ^ 28 < weightedCentralSum generationThreshold (M : ℚ) := by
  have := h.lt_weightedCentralSum
  rwa [tailMargin_cast, centralSumMargin_cast] at this

/-- A good seed is positive. -/
theorem GoodSeed.pos {t M : ℕ} (h : GoodSeed t M) : 0 < M :=
  h.odd.pos

/-- A good seed has positive weighted central sum `Z_{N_*}(M)`. -/
theorem GoodSeed.weightedCentralSum_pos {t M : ℕ} (h : GoodSeed t M) :
    0 < weightedCentralSum generationThreshold (M : ℚ) :=
  lt_trans (by positivity) h.add_two_inv_pow_lt_weightedCentralSum

/-- A `t`-good seed with `t ≥ 1` satisfies `2^{66176} < M`. -/
theorem GoodSeed.two_pow_66176_lt {t M : ℕ} (h : GoodSeed t M) (ht : 0 < t) :
    2 ^ 66176 < M :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_right _ ht) h.two_pow_66176_mul_lt

/-- A `t`-good seed with `t ≥ 1` satisfies the weaker fixed bound `2^{36} < M`, which follows
from `2^{66176} < M`. -/
theorem GoodSeed.two_pow_thirtySix_lt {t M : ℕ} (h : GoodSeed t M) (ht : 0 < t) :
    2 ^ 36 < M := by
  have h₁ := h.two_pow_66176_lt ht
  generalize hk : 66176 = k at h₁
  exact (Nat.pow_le_pow_right Nat.two_pos (by omega)).trans_lt h₁

end CollatzPosDens
