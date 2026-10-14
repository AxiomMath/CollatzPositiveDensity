/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr

/-!
# A dyadic sum against the offset tail

For every real `R ≥ 2`,
$$\sum_{r\ge0}\frac7{2R+2^{r+2}}\le\frac7{2R}\bigl(\log_2R+2\bigr).$$

## Main results

* `CollatzPosDens.jointSum_le`: the series converges and satisfies the bound.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **A dyadic sum against the offset tail.** For every real `R ≥ 2` the series
`∑_{r ≥ 0} 7 / (2R + 2^{r+2})` converges and is at most `7 / (2R) · (log₂ R + 2)`. -/
@[collatz_pos_dens "lem_mx_joint_sum"]
theorem jointSum_le {R : ℝ} (hR : 2 ≤ R) :
    Summable (fun r : ℕ => 7 / (2 * R + 2 ^ (r + 2))) ∧
      ∑' r : ℕ, 7 / (2 * R + 2 ^ (r + 2)) ≤ 7 / (2 * R) * (Real.logb 2 R + 2) := by
  have hR0 : 0 < R := by linarith
  set f : ℕ → ℝ := fun r => 7 / (2 * R + 2 ^ (r + 2))
  have hfg : ∀ r, f r ≤ 7 * (1 / 2) ^ r / 4 := fun r => by
    have h2 : (0 : ℝ) < 2 ^ (r + 2) := by positivity
    have : (7 : ℝ) * (1 / 2) ^ r / 4 = 7 / 2 ^ (r + 2) := by
      rw [one_div_pow, pow_add]; field_simp; norm_num
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) h2 (by linarith)
  have hg : Summable (fun r : ℕ => 7 * (1 / 2 : ℝ) ^ r / 4) :=
    (summable_geometric_two.mul_left 7).div_const 4
  have hs : Summable f := Summable.of_nonneg_of_le (fun r => by positivity) hfg hg
  refine ⟨hs, ?_⟩
  set N : ℕ := ⌊Real.logb 2 R⌋₊
  have hNle : (N : ℝ) ≤ Real.logb 2 R :=
    Nat.floor_le (Real.logb_nonneg (by norm_num) (by linarith))
  have hNlt : Real.logb 2 R < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hRlt : R < 2 ^ (N + 1) := by
    have := (Real.logb_lt_iff_lt_rpow (by norm_num) hR0).1 hNlt
    rw [← Real.rpow_natCast]; push_cast; exact this
  rw [← hs.sum_add_tsum_nat_add (N + 1)]
  have hhead : ∑ i ∈ Finset.range (N + 1), f i ≤ (N + 1) * (7 / (2 * R)) := by
    calc ∑ i ∈ Finset.range (N + 1), f i ≤ ∑ _i ∈ Finset.range (N + 1), 7 / (2 * R) :=
          Finset.sum_le_sum fun i _ =>
            div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (by linarith [pow_pos (two_pos (α := ℝ)) (i + 2)])
      _ = (N + 1) * (7 / (2 * R)) := by simp
  have htail : ∑' i, f (i + (N + 1)) ≤ 7 / (2 * R) := by
    have hg' : Summable (fun i : ℕ => 7 * (1 / 2 : ℝ) ^ (i + (N + 1)) / 4) :=
      (summable_nat_add_iff (N + 1)).2 hg
    calc ∑' i, f (i + (N + 1)) ≤ ∑' i : ℕ, 7 * (1 / 2 : ℝ) ^ (i + (N + 1)) / 4 :=
          Summable.tsum_le_tsum (fun _ => hfg _) ((summable_nat_add_iff (N + 1)).2 hs) hg'
      _ = 7 * (1 / 2 : ℝ) ^ (N + 1) / 4 * ∑' i : ℕ, (1 / 2 : ℝ) ^ i := by
          rw [← tsum_mul_left]; congr 1; ext i; rw [pow_add]; ring
      _ = 7 / (2 * 2 ^ (N + 1)) := by
          rw [tsum_geometric_two, one_div_pow]; field_simp; ring
      _ ≤ 7 / (2 * R) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  calc ∑ i ∈ Finset.range (N + 1), f i + ∑' i, f (i + (N + 1))
      ≤ (N + 1) * (7 / (2 * R)) + 7 / (2 * R) := add_le_add hhead htail
    _ = 7 / (2 * R) * ((N : ℝ) + 2) := by ring
    _ ≤ 7 / (2 * R) * (Real.logb 2 R + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end CollatzPosDens
