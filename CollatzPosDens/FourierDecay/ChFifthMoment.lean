/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The fifth moment of the geometric law `ν₄₅`

The geometric law `ν₄₅(j) = (5/16) (11/16)^(j-1)` (`j ≥ 1`) has finite fifth moment, and
`∑_{j ≥ 1} ν₄₅(j) j⁵ ≤ 20⁵`.

The proof bounds `j⁵ ≤ j (j+1) (j+2) (j+3) (j+4) = 5! · binom(j+4, 5)` and sums the negative
binomial series `∑_{k ≥ 0} binom(k+5, 5) r^k = (1 - r)^{-6}` at `r = 11/16`, which gives the bound
`120 (16/5)^5 = 25165824/625 < 3200000 = 20⁵`.

## Main results

* `CollatzPosDens.nu45_fifth_moment_le`: the sequence `j ↦ ν₄₅(j) j⁵` on `ℤ` is summable and
  its sum is at most `20⁵`.
* `CollatzPosDens.nu45_fifth_moment_le_natCast_add_one`: the same statement with the sum
  indexed by `j = k + 1`, `k : ℕ`.

## Implementation notes

Since `ν₄₅(j) = 0` for `j ≤ 0`, the sum over all of `ℤ` equals the sum over `j ≥ 1`; the main
statement is phrased over `ℤ`, the domain of `nu45`, and records summability explicitly.
-/

@[expose] public section

namespace CollatzPosDens

/-- `(k+1)^5 ≤ 5! · binom(k+5, 5)`. -/
private lemma pow_five_le_choose (k : ℕ) : ((k : ℝ) + 1) ^ 5 ≤ 120 * ((k + 5).choose 5 : ℝ) := by
  have h : (k + 5).descFactorial 5 = Nat.factorial 5 * (k + 5).choose 5 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h' : (k + 5).descFactorial 5 = (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) := by
    simp [Nat.descFactorial_succ]
    ring
  have hN : (k + 1) ^ 5 ≤ 120 * (k + 5).choose 5 := by
    have : Nat.factorial 5 = 120 := by decide
    rw [← this, ← h, h']
    have h1 : k + 1 ≤ k + 2 := by omega
    have h2 : k + 1 ≤ k + 3 := by omega
    have h3 : k + 1 ≤ k + 4 := by omega
    have h4 : k + 1 ≤ k + 5 := by omega
    calc (k + 1) ^ 5 = (k + 1) * (k + 1) * (k + 1) * (k + 1) * (k + 1) := by ring
      _ ≤ (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) := by gcongr
  exact_mod_cast hN

/-- The fifth moment of `ν₄₅`, indexed by `j = k + 1`: the series `∑_{k ≥ 0} ν₄₅(k+1) (k+1)⁵`
converges and its sum is at most `20⁵`. -/
theorem nu45_fifth_moment_le_natCast_add_one :
    Summable (fun k : ℕ ↦ nu45 ((k : ℤ) + 1) * (((k : ℤ) + 1 : ℤ) : ℝ) ^ 5) ∧
      ∑' k : ℕ, nu45 ((k : ℤ) + 1) * (((k : ℤ) + 1 : ℤ) : ℝ) ^ 5 ≤ 20 ^ 5 := by
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one 5 (r := (11 / 16 : ℝ))
    (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)).mul_left (5 / 16 * 120)
  have hle : ∀ k : ℕ, nu45 ((k : ℤ) + 1) * (((k : ℤ) + 1 : ℤ) : ℝ) ^ 5 ≤
      5 / 16 * 120 * (((k + 5).choose 5 : ℕ) * (11 / 16 : ℝ) ^ k) := by
    intro k
    rw [nu45_natCast_add_one]
    push_cast
    have := pow_five_le_choose k
    have hp : (0 : ℝ) ≤ (11 / 16) ^ k := by positivity
    nlinarith
  have hnn : ∀ k : ℕ, 0 ≤ nu45 ((k : ℤ) + 1) * (((k : ℤ) + 1 : ℤ) : ℝ) ^ 5 := fun k ↦
    mul_nonneg (nu45_nonneg _) (by push_cast; positivity)
  have hs : Summable (fun k : ℕ ↦ nu45 ((k : ℤ) + 1) * (((k : ℤ) + 1 : ℤ) : ℝ) ^ 5) :=
    hg.summable.of_nonneg_of_le hnn hle
  refine ⟨hs, ?_⟩
  refine (hasSum_le hle hs.hasSum hg).trans ?_
  norm_num

/-- **Fifth moment of the horizontal hold law.** The series `∑_j ν₄₅(j) j⁵` over `j ∈ ℤ` (whose
nonzero terms are those with `j ≥ 1`) converges and its sum is at most `20⁵`. -/
@[collatz_pos_dens "lem_ch_fifth_moment"]
theorem nu45_fifth_moment_le :
    Summable (fun j : ℤ ↦ nu45 j * (j : ℝ) ^ 5) ∧ ∑' j : ℤ, nu45 j * (j : ℝ) ^ 5 ≤ 20 ^ 5 := by
  obtain ⟨hs, hle⟩ := nu45_fifth_moment_le_natCast_add_one
  have hinj : Function.Injective (fun k : ℕ ↦ (k : ℤ) + 1) := fun a b h ↦ by simpa using h
  have hzero : ∀ j ∉ Set.range (fun k : ℕ ↦ (k : ℤ) + 1), nu45 j * (j : ℝ) ^ 5 = 0 := by
    intro j hj
    rw [nu45_of_nonpos, zero_mul]
    by_contra h
    exact hj ⟨(j - 1).toNat, by simp only; omega⟩
  have hH := (hinj.hasSum_iff (f := fun j : ℤ ↦ nu45 j * (j : ℝ) ^ 5) hzero).mp hs.hasSum
  exact ⟨hH.summable, hH.tsum_eq ▸ hle⟩

end CollatzPosDens
