/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The geometric holding-time law `ν₄₅`

For `j ∈ ℤ` we set `ν₄₅(j) = (5/16) (11/16)^(j-1)` if `j ≥ 1` and `ν₄₅(j) = 0` if `j ≤ 0`.
This is the law of a geometric random variable on `{1, 2, …}` with success probability `5/16`:
the weights are nonnegative, consecutive positive weights have ratio `11/16`, and they sum to `1`.

## Main definitions

* `CollatzPosDens.nu45`: the weight `ν₄₅ : ℤ → ℝ`.

## Main results

* `CollatzPosDens.nu45_of_pos`, `CollatzPosDens.nu45_of_nonpos`: the two cases of the
  definition.
* `CollatzPosDens.nu45_natCast_add_one`: `ν₄₅(k + 1) = (5/16) (11/16)^k` for `k : ℕ`.
* `CollatzPosDens.nu45_nonneg`, `CollatzPosDens.nu45_pos_iff`: positivity.
* `CollatzPosDens.nu45_add_one`: consecutive positive weights have ratio `11/16`.
* `CollatzPosDens.hasSum_nu45`, `CollatzPosDens.tsum_nu45`: the weights over `ℤ` sum to `1`.
* `CollatzPosDens.hasSum_nu45_natCast_add_one`: the weights over `j ≥ 1` sum to `1`.

## Implementation notes

The exponent `j - 1` is an integer, so the power is the `zpow` `(11/16 : ℝ) ^ (j - 1)`; in the
branch where it is used, `j - 1 ≥ 0`, and `nu45_natCast_add_one` restates the weight with a natural
exponent.
-/

@[expose] public section

namespace CollatzPosDens

/-- The geometric law with parameter `5/16` on `ℤ`: `ν₄₅(j) = (5/16) (11/16)^(j-1)` for `j ≥ 1`
and `ν₄₅(j) = 0` for `j ≤ 0`. -/
@[collatz_pos_dens "def_rn_geom4"]
noncomputable def nu45 (j : ℤ) : ℝ :=
  if 1 ≤ j then 5 / 16 * (11 / 16 : ℝ) ^ (j - 1) else 0

/-- For `j ≥ 1`, `ν₄₅(j) = (5/16) (11/16)^(j-1)`. -/
lemma nu45_of_pos {j : ℤ} (hj : 1 ≤ j) : nu45 j = 5 / 16 * (11 / 16 : ℝ) ^ (j - 1) := by
  simp [nu45, hj]

/-- For `j ≤ 0`, `ν₄₅(j) = 0`. -/
lemma nu45_of_nonpos {j : ℤ} (hj : j ≤ 0) : nu45 j = 0 := by
  simp [nu45, show ¬ 1 ≤ j by omega]

/-- `ν₄₅(k + 1) = (5/16) (11/16)^k` for `k : ℕ`. -/
lemma nu45_natCast_add_one (k : ℕ) : nu45 ((k : ℤ) + 1) = 5 / 16 * (11 / 16 : ℝ) ^ k := by
  rw [nu45_of_pos (by omega), add_sub_cancel_right, zpow_natCast]

/-- The weights `ν₄₅(j)` are nonnegative. -/
lemma nu45_nonneg (j : ℤ) : 0 ≤ nu45 j := by
  unfold nu45
  split_ifs
  · exact mul_nonneg (by norm_num) (zpow_nonneg (by norm_num) _)
  · exact le_rfl

/-- `ν₄₅(j) > 0` if and only if `j ≥ 1`. -/
lemma nu45_pos_iff {j : ℤ} : 0 < nu45 j ↔ 1 ≤ j := by
  refine ⟨fun h ↦ ?_, fun hj ↦ ?_⟩
  · by_contra hj
    rw [nu45_of_nonpos (by omega)] at h
    exact lt_irrefl _ h
  · rw [nu45_of_pos hj]; exact mul_pos (by norm_num) (zpow_pos (by norm_num) _)

/-- For `j ≥ 1`, consecutive weights have ratio `11/16`. -/
lemma nu45_add_one {j : ℤ} (hj : 1 ≤ j) : nu45 (j + 1) = 11 / 16 * nu45 j := by
  rw [nu45_of_pos (by omega), nu45_of_pos hj, add_sub_cancel_right,
    show j = (j - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]
  ring_nf

/-- The weights `ν₄₅(j)`, `j ≥ 1`, form a probability distribution. -/
lemma hasSum_nu45_natCast_add_one : HasSum (fun k : ℕ ↦ nu45 ((k : ℤ) + 1)) 1 := by
  simp_rw [nu45_natCast_add_one]
  convert (hasSum_geometric_of_lt_one (r := (11 / 16 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (5 / 16) using 1
  norm_num

/-- The weights `ν₄₅(j)`, `j ∈ ℤ`, form a probability distribution. -/
lemma hasSum_nu45 : HasSum nu45 1 := by
  have hinj : Function.Injective (fun k : ℕ ↦ (k : ℤ) + 1) := fun a b h ↦ by simpa using h
  refine (hinj.hasSum_iff fun j hj ↦ nu45_of_nonpos ?_).mp hasSum_nu45_natCast_add_one
  by_contra h
  exact hj ⟨(j - 1).toNat, by simp only; omega⟩

/-- The weights `ν₄₅(j)`, `j ∈ ℤ`, are summable. -/
lemma summable_nu45 : Summable nu45 :=
  hasSum_nu45.summable

/-- `∑_{j ∈ ℤ} ν₄₅(j) = 1`. -/
lemma tsum_nu45 : ∑' j, nu45 j = 1 :=
  hasSum_nu45.tsum_eq

end CollatzPosDens
