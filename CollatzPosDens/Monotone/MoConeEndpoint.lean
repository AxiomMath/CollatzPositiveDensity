/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.CharSum.ChQmMono
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.D1
public import CollatzPosDens.Transfer.Dpt
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.Transfer.Z
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkExitRoom
public import CollatzPosDens.BlackSet.BkExitWhite
public import CollatzPosDens.Monotone.MoCase1
public import CollatzPosDens.Monotone.MoConeRoom
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A cone exit is a discounted white point

Fix a level `n`, a unit `ξ ∈ G_n`, write `J = ⌊n/2⌋`, and colour points with the colour scale
`ε_*`. Let `m ≥ D_pt`, let `p ∈ 𝒫` with `j(p) + m = J` lie in a canonical triangle
`Δ ∈ 𝔗_{n,ξ,ε_*}` at vertical distance `s = l_Δ - l(p) ≤ m / (log m)^2` below its top edge, and
let `1 ≤ r ≤ ⌊(5s + 16)/16⌋`, `1 ≤ O ≤ 4`. Then the exit point `e = p + (r, s + O)` satisfies
`Q(e) ≤ e^{-z_* + w_*/2} max(m - r, 1)^{-A_*} Q_{m-1}`.

Since `D_pt ≥ 344 > e`, `log m ≥ 1`, and `moConeRoom` gives `r + D₁ < m`. The bound
`3 ε_* 9^r < 2^s` makes `e = (j(p) + r, l_Δ + O)` white (`isBkWhite_exit_of_mem_bkFamily`), and
`chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite` at `e` with `m' = m - r ≥ D₁` in place of `m` gives
`Q(e) ≤ e^{-z_* + w_*/2} m'^{-A_*} Q_{m'-1}`; finally `Q_{m'-1} ≤ Q_{m-1}` by `chQm_mono`.

## Main results

* `CollatzPosDens.chQ_coneEndpoint_le`: the cone-exit bound.

## Implementation notes

The integer `m ≥ D_pt > 0` is taken to be a natural number, so that `Q_{m-1}` is the supremum at
the natural number `m - 1`; likewise the integer `r ≥ 1` is a natural number, and the floor
`⌊(5s + 16)/16⌋` of a nonnegative rational with natural numerator is the natural-number division
`(5 * s + 16) / 16`. The quantities `max(m - r, 1)` and `s ≤ m / (log m)^2` are read in `ℝ`.

## References

* [Mazur, *Collatz positive density*], §8.5.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- Let `ξ` be a unit, `m ≥ D_pt`, `p ∈ 𝒫` with `j(p) + m = ⌊n/2⌋`, `Δ ∈ 𝔗_{n,ξ,ε_*}` with
`p ∈ Δ`, `s ∈ ℕ` with `l(p) + s = l_Δ` and `s ≤ m / (log m)^2`, `1 ≤ r ≤ ⌊(5s + 16)/16⌋` and
`1 ≤ O ≤ 4`. Then `Q(p + (r, s + O)) ≤ e^{-z_* + w_*/2} max(m - r, 1)^{-A_*} Q_{m-1}`. -/
@[collatz_pos_dens "lem_mo_cone_endpoint"]
theorem chQ_coneEndpoint_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {m : ℕ}
    (hm : (Dpt : ℝ) ≤ m) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (hpΔ : p ∈ Δ) {s : ℕ} (hs : bkL p + s = Δ.l)
    (hsm : (s : ℝ) ≤ m / Real.log m ^ 2) {r : ℕ} (hr₁ : 1 ≤ r) (hr : r ≤ (5 * s + 16) / 16)
    {O : ℤ} (hO₁ : 1 ≤ O) (hO₄ : O ≤ 4) :
    chQ n ξ (epsStar : ℝ) (p + ((r : ℤ), (s : ℤ) + O)) ≤
      exp (-(zStar : ℝ) + (wStar : ℝ) / 2) * max ((m : ℝ) - r) 1 ^ (-(Aexp : ℝ)) *
        chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
  have hDpt : (Dpt : ℝ) = 2 * D1 + 344 := by rw [Dpt_def]; push_cast; ring
  have hD1 : (2 : ℝ) < D1 := by exact_mod_cast two_lt_D1
  have hlog : 1 ≤ Real.log ((m : ℤ) : ℝ) := by
    rw [Int.cast_natCast, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hroom := moConeRoom (m := (m : ℤ)) (by rw [Int.cast_natCast]; exact hm) hlog
    (s := s) (by rw [Int.cast_natCast]; exact hsm) (r := (r : ℤ)) (by
      rw [Int.le_floor]
      have : r * 16 ≤ 5 * s + 16 := by omega
      have : ((r * 16 : ℕ) : ℝ) ≤ ((5 * s + 16 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith)
  rw [Int.cast_natCast, Int.cast_natCast] at hroom
  have hrm : r < m := by
    have : (r : ℝ) < m := by linarith
    exact_mod_cast this
  have hm' : ((m - r : ℕ) : ℝ) = (m : ℝ) - r := by rw [Nat.cast_sub hrm.le]
  have hmax : max ((m : ℝ) - r) 1 = ((m - r : ℕ) : ℝ) := by
    rw [hm']; exact max_eq_left (by linarith)
  have he : p + ((r : ℤ), (s : ℤ) + O) = (bkJ p + r, Δ.l + O) := by
    obtain ⟨j, l⟩ := p
    simp only [bkJ, bkL] at hs ⊢
    ext <;> (simp; try omega)
  have hroom' : 3 * (epsStar : ℝ) * 9 ^ r < 2 ^ s := by
    refine lt_of_le_of_lt ?_ (three_mul_epsStar_mul_nine_pow_lt_two_pow (K := ℝ) s)
    have h0 : (0 : ℝ) < epsStar := epsStar_mem_bkRange.1
    gcongr
    norm_num
  have hwhite := isBkWhite_exit_of_mem_bkFamily hξ epsStar_mem_bkRange.1
    epsStar_mem_bkRange.2 hΔ hpΔ hs hroom' hO₁ hO₄
  have hcase := chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite n ξ (epsStar : ℝ) (m := m - r)
    (by rw [hm']; linarith) (p := (bkJ p + r, Δ.l + O))
    (by simp only [mem_bkPoints, bkJ] at hp ⊢; omega) hwhite
    (by simp only [bkJ] at hpm ⊢; push_cast [hrm.le]; omega)
  rw [he, hmax]
  refine hcase.trans ?_
  have hA : (0 : ℝ) ≤ (Aexp : ℝ) := by rw [Aexp_cast]; norm_num
  gcongr
  · exact chQm_mono n ξ _ hA (by omega)

end CollatzPosDens
