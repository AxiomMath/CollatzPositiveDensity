/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkSeWeight
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkNwClosure
public import CollatzPosDens.BlackSet.BkSeBound
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkClaimI
public import CollatzPosDens.BlackSet.BkCornerValue
public import CollatzPosDens.BlackSet.BkExitLeft
public import CollatzPosDens.BlackSet.BkExitStrip
public import CollatzPosDens.BlackSet.BkWhiteNear

/-!
# Exit points are white

Let `ξ` be a unit, `0 < ε < 1/27`, `Δ ∈ 𝔗_{n,ξ,ε}` and `u ∈ Δ`. Let `s ∈ ℕ` be the vertical
distance `l_Δ - l(u)` from `u` to the top edge of `Δ`, and let `r ∈ ℕ` satisfy `3 ε 9^r < 2^s`.
Then for every `O ∈ {1, 2, 3, 4}` the point `e = (j(u) + r, l_Δ + O)` is white.

Write `Δ = Δ(p) = (a, L, U)` with `p` black and `j_e = j(u) + r`. The point `e` lies in the strip
`j_e ≤ ⌊n/2⌋`, so if it is not white it is black, `|ϑ(e)| ≤ ε`, and moving down to
`b₀ = (j_e, L + 1)` gives `|ϑ(b₀)| ≤ 2^{O-1} ε ≤ 8 ε`. North-west closure puts `(j(u), L)` in `Δ`,
and this point is black. One then shows `2 ϑ(j(u), L + 1) = ϑ(j(u), L)`: for `r = 0` by
`CollatzPosDens.two_mul_bkTheta_eq_of_self_of_south` at `b₀`, and for `r ≥ 1` by leftward
recovery along row `L + 1`, the row below being controlled by the corner value
`|ϑ(a, L)| = ε e^{-U}` and `U ≥ (j(u) - a) log 9 + s log 2`. Hence `|ϑ(j(u), L + 1)| ≤ ε/2`,
while `(j(u), L + 1) ∉ Δ` is at distance `1` from `(j(u), L) ∈ Δ`, so it is white: a
contradiction.

## Main results

* `CollatzPosDens.isBkWhite_exit_of_mem_bkFamily`: the exit point `(j(u) + r, l_Δ + O)` is
  white.

## Implementation notes

Mazur's proof argues with the largest `k₀ ∈ [j(u), j_e]` such that `(k₀, L) ∈ Δ`, splitting on
whether `(j_e, L) ∈ Δ`. Maximality of `k₀` is never used: the bound on row `L` holds at every
`x` with `a ≤ j(x) ≤ j_e - 1`, inside `Δ` or not. We therefore take `k₀ = j(u)` and split instead
on `r = 0` (where `(j_e, L) = (j(u), L) ∈ Δ`, the first case of that proof) and `r ≥ 1`.
The offset `O` is an integer with `1 ≤ O ≤ 4`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.7.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {Δ : BkTriangle} {u : ℤ × ℤ}

/-- **Exit points are white.** Let `ξ` be a unit, `0 < ε < 1/27`, `Δ ∈ 𝔗_{n,ξ,ε}`, `u ∈ Δ`,
`s ∈ ℕ` with `l(u) + s = l_Δ`, `r ∈ ℕ` with `3 ε 9^r < 2^s`, and `O ∈ {1, 2, 3, 4}`. Then the
point `(j(u) + r, l_Δ + O)` is white. -/
@[collatz_pos_dens "lem_bk_exit_white"]
theorem isBkWhite_exit_of_mem_bkFamily (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hε' : ε < 1 / 27) (hΔ : Δ ∈ bkFamily n ξ ε) (hu : u ∈ Δ) {s r : ℕ}
    (hs : bkL u + s = Δ.l) (hr : 3 * ε * 9 ^ r < 2 ^ s) {O : ℤ} (hO₁ : 1 ≤ O) (hO₄ : O ≤ 4) :
    IsBkWhite n ξ ε (bkJ u + r, Δ.l + O) := by
  have hstrip := bkJ_add_le_of_mem_bkFamily hξ hε hΔ hu hs hr
  obtain ⟨p, hp, hb, rfl⟩ := hΔ
  obtain ⟨x, y⟩ := u
  simp only [bkJ, bkL] at hstrip hs ⊢
  set T := bkCanonTriangle n ξ ε p hp with hT
  have hΔmem : T ∈ bkFamily n ξ ε := ⟨p, hp, hb, rfl⟩
  have haj : T.j ≤ x := hu.1
  have hlu : y ≤ T.l := hu.2.1
  have ha1 : 1 ≤ T.j := T.one_le_j
  refine ⟨hstrip, lt_of_not_ge fun he => ?_⟩
  have hb₀ : |bkTheta n ξ (x + r, T.l + 1)| ≤ 8 * ε := by
    have h := abs_bkTheta_le_exp_bkSe_mul n ξ (a := (x + r, T.l + O))
      (q := (x + r, T.l + 1)) (by simp only [mem_bkPoints, bkJ]; omega)
      (by simp only [mem_bkPoints, bkJ]; omega) le_rfl (by simp only [bkL]; omega)
    rw [exp_bkSe] at h
    simp only [bkJ, bkL, sub_self, zpow_zero, one_mul] at h
    have h2 : (2 : ℝ) ^ (T.l + O - (T.l + 1)) ≤ 8 := by
      calc (2 : ℝ) ^ (T.l + O - (T.l + 1)) ≤ (2 : ℝ) ^ (3 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 8 := by norm_num
    calc _ ≤ _ := h
      _ ≤ 8 * ε := mul_le_mul h2 he (abs_nonneg _) (by norm_num)
  have hw : (x, T.l) ∈ T :=
    BkTriangle.mem_of_mem_of_nw hu haj le_rfl hlu le_rfl
  have hwb : |bkTheta n ξ (x, T.l)| ≤ ε :=
    (bkBlack_of_mem_bkCanonTriangle hξ hε hε' hp hb hw).2
  have hkey : 2 * bkTheta n ξ (x, T.l + 1) = bkTheta n ξ (x, T.l) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      simp only [Nat.cast_zero, add_zero] at hb₀
      have h := two_mul_bkTheta_eq_of_self_of_south n ξ (j := x) (l := T.l + 1)
        (by simp only [mem_bkPoints_mk]; omega) (A₀ := 8 * ε) (B₀ := ε) (by linarith) hb₀
        (by simpa using hwb)
      simpa using h
    · have hcorner := abs_bkTheta_bkCanonTriangle_corner hξ hε hp hb
      rw [← hT] at hcorner
      have hlog : Real.log 3 + Real.log ε + r * Real.log 9 < s * Real.log 2 := by
        have h := Real.log_lt_log (by positivity) hr
        rwa [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) hε.ne', Real.log_pow, Real.log_pow] at h
      have hU : ((x - T.j : ℤ) : ℝ) * Real.log 9 + (s : ℝ) * Real.log 2 ≤ T.s := by
        have h := hu.2.2
        have : T.l - y = (s : ℤ) := by omega
        rwa [this, Int.cast_natCast] at h
      have h27 : Real.log 27 = Real.log 3 + Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have hl9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
      have h := two_mul_bkTheta_eq_of_exit_left n ξ (k₀ := x) (l := T.l + 1)
        (by simp only [mem_bkPoints_mk]; omega) (m := r) hr0 hε'.le hb₀ (by simpa using hwb)
        (fun k hk1 hk2 => ?_)
      · simpa using h
      · rw [add_sub_cancel_right]
        have hk : (k : ℝ) ≤ (r : ℝ) - 1 := by
          have : k + 1 ≤ r := by omega
          have : ((k + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
          push_cast at this; linarith
        have h := abs_bkTheta_le_exp_bkSe_mul n ξ (a := T.corner) (q := (x + k, T.l))
          T.one_le_j (by simp only [mem_bkPoints_mk]; omega)
          (by simp only [bkJ, BkTriangle.corner_fst]; omega) (by simp)
        rw [hcorner] at h
        refine h.trans (le_of_lt ?_)
        rw [bkSe, mul_left_comm, ← Real.exp_add]
        simp only [bkJ, bkL, BkTriangle.corner_fst, BkTriangle.corner_snd, sub_self,
          Int.cast_zero, zero_mul, add_zero]
        have hexp : ((x + k - T.j : ℤ) : ℝ) * Real.log 9 + -T.s ≤
            ((r : ℝ) - 1) * Real.log 9 - s * Real.log 2 := by
          push_cast at hU ⊢
          nlinarith
        calc ε * Real.exp (((x + k - T.j : ℤ) : ℝ) * Real.log 9 + -T.s)
            ≤ ε * Real.exp (((r : ℝ) - 1) * Real.log 9 - s * Real.log 2) := by
              gcongr
          _ = Real.exp (Real.log ε + (((r : ℝ) - 1) * Real.log 9 - s * Real.log 2)) := by
              rw [Real.exp_add, Real.exp_log hε]
          _ < Real.exp (-Real.log 27) := by
              apply Real.exp_lt_exp.2
              linarith
          _ = 1 / 27 := by
              rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have hsmall : |bkTheta n ξ (x, T.l + 1)| ≤ ε / 2 := by
    have : |2 * bkTheta n ξ (x, T.l + 1)| ≤ ε := by rw [hkey]; exact hwb
    rw [abs_mul] at this
    norm_num at this
    linarith
  have hnot : (x, T.l + 1) ∉ T := fun h => by
    have := h.2.1
    simp only [bkL] at this
    omega
  have hwhite := isBkWhite_of_bkDist_le_one hξ hε hε' hΔmem hw
    (by simp only [mem_bkPoints_mk]; omega) hnot
    (by simp only [bkJ]; omega) (by simp [bkDist, bkDistSq, bkJ, bkL])
  have := hwhite.2
  linarith

end CollatzPosDens
