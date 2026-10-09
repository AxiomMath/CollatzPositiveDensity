/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkSeWeight
public import CollatzPosDens.BlackSet.BkSeExact
public import CollatzPosDens.BlackSet.BkStrip

/-!
# A black column ends within `2n` steps

Let `ξ ∈ G_n` be a unit, `ε < 1/4`, and let `p = (j, l) ∈ 𝒫` be black. Then some point
`(j, l + t)` with `1 ≤ t ≤ 2n` is white. Otherwise every point `(j, l + u)`, `0 ≤ u ≤ 2n`, is
black. For a vertical step of length one the weight satisfies `e^{se((j, l+u+1), (j, l+u))} = 2`,
and since `2 |ϑ| ≤ 2ε < 1/2` along the column, the exact scaling of the angle gives
`|ϑ(j, l + u)| = 2 |ϑ(j, l + u + 1)|`; by induction `|ϑ(j, l)| = 4^n |ϑ(j, l + 2n)|`. The strip
bound `1/3 ≤ 3^{n+1-2j} |ϑ(j, l + 2n)|` together with `3^{n+1-2j} ≤ 4^n` then forces
`1/3 ≤ ε`, a contradiction.

## Main results

* `CollatzPosDens.exists_isBkWhite_of_bkBlack`: a black column ends within `2n` steps.

## Implementation notes

The hypothesis `0 ≤ ε` of the source is not needed and is omitted.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- One vertical step halves the angle while it stays small: if `1 ≤ j` and
`2 |ϑ(j, l + 1)| < 1/2` then `|ϑ(j, l)| = 2 |ϑ(j, l + 1)|`. -/
private theorem abs_bkTheta_eq_two_mul_of_step (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hj : 1 ≤ j) (hsmall : 2 * |bkTheta n ξ (j, l + 1)| < 1 / 2) :
    |bkTheta n ξ (j, l)| = 2 * |bkTheta n ξ (j, l + 1)| := by
  have hexp : Real.exp (bkSe (j, l + 1) (j, l)) = 2 := by
    rw [exp_bkSe]; simp [bkJ, bkL]
  have h := abs_bkTheta_eq_exp_bkSe_mul n ξ (a := (j, l + 1)) (q := (j, l)) hj hj le_rfl
    (show l ≤ l + 1 by omega) (by rw [hexp]; exact hsmall)
  rwa [hexp] at h

/-- **A black column ends within `2n` steps.** Let `ξ` be a unit, `ε < 1/4` and let
`p = (j, l) ∈ 𝒫` be black. Then there is an integer `t` with `1 ≤ t ≤ 2n` such that
`(j, l + t)` is white. -/
@[collatz_pos_dens "lem_bk_column_ends"]
theorem exists_isBkWhite_of_bkBlack {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {ε : ℝ} (hε : ε < 1 / 4) {p : ℤ × ℤ} (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    ∃ t : ℤ, 1 ≤ t ∧ t ≤ 2 * n ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t) := by
  obtain ⟨j, l⟩ := p
  rw [mem_bkPoints] at hp
  simp only [bkJ, bkL] at hp hb ⊢
  by_contra hcon
  push Not at hcon
  have hblack : ∀ u : ℕ, u ≤ 2 * n → |bkTheta n ξ (j, l + u)| ≤ ε := by
    intro u hu
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · simpa using hb.2
    · have := hcon u (by exact_mod_cast hu0) (by exact_mod_cast hu)
      rw [isBkWhite_iff] at this
      exact not_lt.1 fun h => this ⟨hb.1, h⟩
  have hscale : ∀ u : ℕ, u ≤ 2 * n →
      |bkTheta n ξ (j, l)| = 2 ^ u * |bkTheta n ξ (j, l + u)| := by
    intro u
    induction u with
    | zero => intro _; simp
    | succ u ih =>
      intro hu
      have hstep := abs_bkTheta_eq_two_mul_of_step n ξ (l := l + u) hp
        (by have := hblack (u + 1) hu; push_cast at this; rw [add_assoc]; linarith)
      rw [ih (by omega), hstep]
      push_cast
      rw [add_assoc]
      ring
  have h4 := hscale (2 * n) le_rfl
  have hstrip := one_third_le_three_zpow_mul_abs_bkTheta hξ (p := (j, l + ((2 * n : ℕ) : ℤ)))
    (by simpa using hp) (by simpa using hb.1)
  simp only [bkJ] at hstrip
  have hpow : (3 : ℝ) ^ ((n : ℤ) + 1 - 2 * j) ≤ 2 ^ (2 * n) := by
    calc (3 : ℝ) ^ ((n : ℤ) + 1 - 2 * j) ≤ (3 : ℝ) ^ (n : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 3 ^ n := zpow_natCast _ _
      _ ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      _ = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have habs := abs_nonneg (bkTheta n ξ (j, l + ((2 * n : ℕ) : ℤ)))
  have := mul_le_mul_of_nonneg_right hpow habs
  have hle := hb.2
  linarith

end CollatzPosDens
