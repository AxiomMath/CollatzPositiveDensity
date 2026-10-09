/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkCanonEdge

/-!
# Exit points lie in the strip

Let `ξ` be a unit of `ResidueGroup n`, `ε > 0`, `Δ ∈ bkFamily n ξ ε` and `u ∈ Δ`. If `s ∈ ℕ`
is the vertical distance `Δ.l - bkL u` from `u` to the top edge of `Δ`, and `r ∈ ℕ` satisfies
`3 ε 9^r < 2^s`, then the point `r` steps to the right of `u` still lies in the strip:
`bkJ u + r ≤ ⌊n/2⌋`.

Write `Δ = bkCanonTriangle n ξ ε p` with `p` black. Membership `u ∈ Δ` gives
`(bkJ u - Δ.j) log 9 + s log 2 ≤ Δ.s`, and the edge of a canonical triangle bounds
`Δ.j + Δ.s / log 9 ≤ n/2 + 1 - log (1/ε) / log 9`. Taking logarithms in `3 ε 9^r < 2^s` gives
`r log 9 < s log 2 - log ε - log 3`. Adding, and using `log 3 = (1/2) log 9`, gives
`bkJ u + r < n/2 + 1/2`, so `2 (bkJ u + r) ≤ n` by integrality.

## Main results

* `CollatzPosDens.bkJ_add_le_of_mem_bkFamily`: `bkJ u + r ≤ ⌊n/2⌋`.

## Implementation notes

The statement assumes only `0 < ε`, which is all the argument uses, rather than
`0 < ε < 1/4`. Since `bkJ u` is an integer, `⌊n/2⌋` is written as the natural number division
`n / 2`, cast to `ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.7.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {Δ : BkTriangle} {u : ℤ × ℤ}

/-- **Exit points lie in the strip.** Let `ξ` be a unit, `ε > 0`, `Δ ∈ bkFamily n ξ ε`, `u ∈ Δ`,
`s ∈ ℕ` with `bkL u + s = Δ.l`, and `r ∈ ℕ` with `3 ε 9^r < 2^s`. Then
`bkJ u + r ≤ ⌊n/2⌋`. -/
@[collatz_pos_dens "lem_bk_exit_strip"]
theorem bkJ_add_le_of_mem_bkFamily (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hΔ : Δ ∈ bkFamily n ξ ε) (hu : u ∈ Δ) {s r : ℕ} (hs : bkL u + s = Δ.l)
    (hr : 3 * ε * 9 ^ r < 2 ^ s) :
    bkJ u + r ≤ ((n / 2 : ℕ) : ℤ) := by
  obtain ⟨p, hp, hb, rfl⟩ := hΔ
  set T := bkCanonTriangle n ξ ε p hp
  have hedge := bkCanonTriangle_j_add_s_div_log_nine_le hξ hε hp hb
  have hw := BkTriangle.weight_le_of_mem hu
  have hls : ((T.l - bkL u : ℤ) : ℝ) = s := by
    rw [← hs]; push_cast; ring
  rw [hls] at hw
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 := log_nine_eq_two_mul_log_three
  have h9pos : 0 < Real.log 9 := by rw [h9]; positivity
  have hedge' : (T.j : ℝ) * Real.log 9 + T.s ≤
      ((n : ℝ) / 2 + 1) * Real.log 9 + Real.log ε := by
    rw [one_div, Real.log_inv, neg_div] at hedge
    have := mul_le_mul_of_nonneg_right hedge h9pos.le
    rw [add_mul, div_mul_cancel₀ _ h9pos.ne', sub_mul, neg_mul, div_mul_cancel₀ _ h9pos.ne']
      at this
    linarith
  have hlog := Real.log_lt_log (by positivity) hr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hε.ne',
    Real.log_pow, Real.log_pow] at hlog
  push_cast at hw
  have key : ((bkJ u : ℝ) + r) * Real.log 9 < ((n : ℝ) / 2 + 1 / 2) * Real.log 9 := by
    rw [h9] at hlog hedge' hw ⊢
    nlinarith
  have hlt : (bkJ u : ℝ) + r < (n : ℝ) / 2 + 1 / 2 := lt_of_mul_lt_mul_right key h9pos.le
  have hlt' : 2 * (bkJ u + r) < (n : ℤ) + 1 := by
    have : (2 * (bkJ u + r) : ℝ) < (n : ℝ) + 1 := by linarith
    exact_mod_cast this
  omega

end CollatzPosDens
