/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Transfer.S02Kappa
public import CollatzPosDens.Transfer.S02Z
public import CollatzPosDens.CharSum.ChPacketCoverage

/-!
# Baseline paid reward

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For an integer `c` and a point `p`, with
`[·]` the indicator of a statement, the *baseline paid reward* is
* `R^old_c(p) = κ_* [p white]` for `c = 3`;
* `R^old_c(p) = [p white]` for `c = 4`;
* `R^old_c(p) = [p white] + (18351/25000) [p not white and p - (0,1) white]` for `c = 5`;
* `R^old_c(p) = M_c(p)/(c - 1) · (1 - z_*/2)` for `6 ≤ c ≤ 16`, with `M_c(p)` the packet
  coverage;
* `R^old_c(p) = 0` otherwise.

## Main definitions

* `CollatzPosDens.chOldReward n ξ ε c p`: the baseline paid reward `R^old_c(p)`.

## Main results

* `CollatzPosDens.chOldReward_three`, `chOldReward_four`, `chOldReward_five`,
  `chOldReward_of_six_le_of_le_sixteen`, `chOldReward_of_not_mem`: the five cases.
* `CollatzPosDens.chOldReward_nonneg`: `R^old_c(p) ≥ 0`.
* `CollatzPosDens.chOldReward_eq_zero_of_lt_bkJ`: `R^old_c(p) = 0` when `j(p) > ⌊n/2⌋`.

## Implementation notes

The reward is defined for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, as whiteness and the packet
coverage are. The constants `κ_*` and `z_*` are rational and are cast to `ℝ`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The baseline paid reward `R^old_c(p)`. -/
@[collatz_pos_dens "def_ch_old_reward"]
noncomputable def chOldReward (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) : ℝ :=
  if c = 3 then (kappaStar : ℝ) * (if IsBkWhite n ξ ε p then 1 else 0)
  else if c = 4 then (if IsBkWhite n ξ ε p then 1 else 0)
  else if c = 5 then
    (if IsBkWhite n ξ ε p then 1 else 0) +
      18351 / 25000 * (if ¬ IsBkWhite n ξ ε p ∧ IsBkWhite n ξ ε (p - (0, 1)) then 1 else 0)
  else if 6 ≤ c ∧ c ≤ 16 then
    (chPacketCoverage n ξ ε c p : ℝ) / ((c : ℝ) - 1) * (1 - (zStar : ℝ) / 2)
  else 0

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ} {p : ℤ × ℤ}

/-- `R^old_3(p) = κ_* [p white]`. -/
theorem chOldReward_three :
    chOldReward n ξ ε 3 p = (kappaStar : ℝ) * (if IsBkWhite n ξ ε p then 1 else 0) := by
  simp [chOldReward]

/-- `R^old_4(p) = [p white]`. -/
theorem chOldReward_four :
    chOldReward n ξ ε 4 p = if IsBkWhite n ξ ε p then 1 else 0 := by
  simp [chOldReward]

/-- `R^old_5(p) = [p white] + (18351/25000) [p not white and p - (0,1) white]`. -/
theorem chOldReward_five :
    chOldReward n ξ ε 5 p = (if IsBkWhite n ξ ε p then 1 else 0) +
      18351 / 25000 * (if ¬ IsBkWhite n ξ ε p ∧ IsBkWhite n ξ ε (p - (0, 1)) then 1 else 0) := by
  simp [chOldReward]

/-- `R^old_c(p) = M_c(p)/(c - 1) · (1 - z_*/2)` for `6 ≤ c ≤ 16`. -/
theorem chOldReward_of_six_le_of_le_sixteen (h₁ : 6 ≤ c) (h₂ : c ≤ 16) :
    chOldReward n ξ ε c p =
      (chPacketCoverage n ξ ε c p : ℝ) / ((c : ℝ) - 1) * (1 - (zStar : ℝ) / 2) := by
  have h3 : c ≠ 3 := by omega
  have h4 : c ≠ 4 := by omega
  have h5 : c ≠ 5 := by omega
  simp [chOldReward, h3, h4, h5, h₁, h₂]

/-- `R^old_c(p) = 0` when `c ∉ [3, 16]`. -/
theorem chOldReward_of_not_mem (h : c < 3 ∨ 16 < c) : chOldReward n ξ ε c p = 0 := by
  have h3 : c ≠ 3 := by omega
  have h4 : c ≠ 4 := by omega
  have h5 : c ≠ 5 := by omega
  have h6 : ¬ (6 ≤ c ∧ c ≤ 16) := by omega
  simp only [chOldReward, h3, h4, h5, h6, ite_false]

/-- `R^old_c(p) = [p white]` for `c ∈ {4, 5}` and `p` white. -/
theorem chOldReward_of_isBkWhite (hc : c = 4 ∨ c = 5) (hp : IsBkWhite n ξ ε p) :
    chOldReward n ξ ε c p = 1 := by
  rcases hc with rfl | rfl <;> simp [chOldReward, hp]

/-- The baseline paid reward is nonnegative. -/
theorem chOldReward_nonneg : 0 ≤ chOldReward n ξ ε c p := by
  have hk : (0 : ℝ) ≤ kappaStar := by rw [kappaStar_cast]; norm_num
  have hz : (0 : ℝ) ≤ 1 - (zStar : ℝ) / 2 := by rw [zStar_cast]; norm_num
  unfold chOldReward
  split_ifs <;> try positivity
  rename_i h6
  have : (0 : ℝ) ≤ (c : ℝ) - 1 := by
    have : (6 : ℝ) ≤ c := by exact_mod_cast h6.1
    linarith
  positivity

/-- `R^old_c(p) = 0` when `j(p) > ⌊n/2⌋`: no point with this first coordinate is white. -/
theorem chOldReward_eq_zero_of_lt_bkJ (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) :
    chOldReward n ξ ε c p = 0 := by
  have hw : ¬ IsBkWhite n ξ ε p := fun h => absurd h.bkJ_le (not_le.2 hp)
  have hw' : ¬ IsBkWhite n ξ ε (p - (0, 1)) := fun h =>
    absurd h.bkJ_le (not_le.2 (by simpa using hp))
  simp [chOldReward, hw, hw', chPacketCoverage_eq_zero_of_lt_bkJ hp]

end CollatzPosDens
