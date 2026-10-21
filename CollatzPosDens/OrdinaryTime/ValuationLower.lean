/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.OrdinaryTime.S07FullWord
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.LengthOk
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.OrdinaryTime.S07Wstar
public import CollatzPosDens.Seed.History
public import CollatzPosDens.FirstCrossing.Width
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# A lower bound on the valuation sum of a full word

Let `(h, w)` be a selected pair of level `(t, n, X)` with full word `𝐰 = 𝐰(h, w)` of length
`d = |𝐰|`. Then
$$A(\mathbf w)\log 2 \ge 2d\log 2 - \log(4/3)\,W_*(n) - (2n+1)\log 2 - \frac{b_n}{8}\log 2.$$
Writing `λ = log₂ 3`, each central word `w_j ∈ 𝒞(b_j, K_j)` satisfies
`A(w_j) ≥ 2|w_j| - (2 - λ) wd(b_j) - 1`, because it crosses the barrier
`H_{b_j, r_{b_j}}(s) = 2b_j + B((s - b_j)_+) - B((b_j - s)_+)` and its length is within
`wd(b_j)` of `b_j`; the terminal word satisfies `A(w) ≥ 2|w| - b_n / 8` by the crossing
condition and `Λ_{b_n,u}(w)`. Summing and using `(2 - λ) log 2 = log (4/3)` gives the claim.

## Main results

* `CollatzPosDens.valSum_fullWord_mul_log_two_ge`: the lower bound above.
* `CollatzPosDens.sub_le_valSum_of_mem_centralFamily`: the bound
  `A(w) ≥ 2|w| - (2 - log₂ 3) wd(b) - 1` for a central word `w ∈ 𝒞(b, K)`.
* `CollatzPosDens.sub_le_valSum_of_lengthOk`: the bound
  `A(w) ≥ 2|w| - b / 8` for `w ∈ 𝒲(b, u, K)` with `Λ_{b,u}(w)`.

## Implementation notes

The hypotheses that `t` is a positive odd integer and that `X > 0` are not used, so the
result is stated for every `t : ℚ` and `X : ℝ`, matching `CollatzPosDens.IsSelectedPair`.
A history `h = (w_0, …, w_{n-1})` is a tuple `Fin n → Word`, entry `k` being `w_k`.
The quotient `b_n / 8` is the real quotient; `W_*(n)` and `b_n` are natural numbers cast to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- A central word `w ∈ 𝒞(b, K)` satisfies `A(w) ≥ 2|w| - (2 - log₂ 3) wd(b) - 1`. -/
theorem sub_le_valSum_of_mem_centralFamily {b K : ℕ} {w : Word}
    (hw : w ∈ centralFamily b K) :
    2 * (w.length : ℝ) - (2 - logb 2 3) * wd b - 1 ≤ w.valSum := by
  have hA := barrier_le_valSum_of_mem_firstCrossing hw.1
  have hlo := sub_wd_le_length_of_mem_centralFamily hw
  have hhi := length_le_add_wd_of_mem_centralFamily hw
  have hlam : logb 2 3 < 2 := logb_two_three_bounds.2.trans (by norm_num)
  rcases le_total b w.length with hs | hs
  · rw [barrier_of_le _ hs] at hA
    have hA' : (2 * (b : ℝ) + ceilLog3 (w.length - b)) ≤ w.valSum := by
      have : (2 * (b : ℤ) + ceilLog3 (w.length - b) : ℤ) ≤ w.valSum := by linarith
      exact_mod_cast this
    have hB := mul_logb_le_ceilLog3 (w.length - b)
    rw [Nat.cast_sub hs] at hB
    have hle : (w.length : ℝ) - b ≤ wd b := by
      have : (w.length : ℤ) - b ≤ wd b := by omega
      exact_mod_cast this
    have hs' : (b : ℝ) ≤ w.length := by exact_mod_cast hs
    nlinarith
  · rw [barrier_of_ge _ hs] at hA
    have hA' : (2 * (b : ℝ) - ceilLog3 (b - w.length)) ≤ w.valSum := by
      have : (2 * (b : ℤ) - ceilLog3 (b - w.length) : ℤ) ≤ w.valSum := by linarith
      exact_mod_cast this
    have hB := ceilLog3_lt_mul_logb_add_one (b - w.length)
    rw [Nat.cast_sub hs] at hB
    have hs' : (w.length : ℝ) ≤ b := by exact_mod_cast hs
    have hdw : (0 : ℝ) ≤ wd b := by positivity
    have hle : (b : ℝ) - w.length ≤ wd b := by
      have : (b : ℤ) - w.length ≤ wd b := by omega
      exact_mod_cast this
    nlinarith

/-- A word `w ∈ 𝒲(b, u, K)` with `Λ_{b,u}(w)` satisfies `A(w) ≥ 2|w| - b / 8`. -/
theorem sub_le_valSum_of_lengthOk {b : ℕ} {u : ℤ} {K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b u K) (hl : LengthOk b u w) :
    2 * (w.length : ℝ) - (b : ℝ) / 8 ≤ w.valSum := by
  have hA := barrier_le_valSum_of_mem_firstCrossing hw
  rw [lengthOk_iff] at hl
  have h1 : 2 * (w.length : ℝ) - ((b / 8 : ℕ) : ℝ) ≤ w.valSum := by
    have : 2 * (w.length : ℤ) - ((b / 8 : ℕ) : ℤ) ≤ w.valSum := by linarith
    exact_mod_cast this
  have h2 : ((b / 8 : ℕ) : ℝ) ≤ (b : ℝ) / 8 := by
    have := Nat.cast_div_le (α := ℝ) (m := b) (n := 8)
    simpa using this
  linarith

/-- **Valuation lower bound.** For a selected pair `(h, w)` of level `(t, n, X)` with full word
`𝐰 = 𝐰(h, w)` of length `d`,
`A(𝐰) log 2 ≥ 2d log 2 - log (4/3) W_*(n) - (2n + 1) log 2 - (b_n / 8) log 2`. -/
@[collatz_pos_dens "lem_valuation_lower"]
theorem valSum_fullWord_mul_log_two_ge {n : ℕ} {X : ℝ} {t : ℚ} {h : Fin n → Word}
    {w : Word} (hp : IsSelectedPair n X t h w) :
    2 * ((fullWord h w).length : ℝ) * log 2 - log (4 / 3) * widthSum n -
        (2 * n + 1) * log 2 - (scale n : ℝ) / 8 * log 2 ≤
      ((fullWord h w).valSum : ℝ) * log 2 := by
  have hcent : ∀ k : Fin n,
      2 * ((h k).length : ℝ) - (2 - logb 2 3) * wd (scale k) - 1 ≤ (h k).valSum :=
    fun k => sub_le_valSum_of_mem_centralFamily
      (selectedTuples_mem_centralFamily
        (centralHistories_subset_selectedTuples t n hp.mem_centralHistories) k)
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin n))) => hcent k
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hW : (widthSum n : ℝ) = ∑ k : Fin n, (wd (scale k) : ℝ) := by
    rw [widthSum, Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun k => (wd (scale k) : ℝ))]
  have hterm := sub_le_valSum_of_lengthOk hp.mem_firstCrossing hp.lengthOk
  have hA : ((fullWord h w).valSum : ℝ) = ∑ k, ((h k).valSum : ℝ) + w.valSum := by
    rw [fullWord, Word.valSum_append, Nat.cast_add, valSum_concatWord, Nat.cast_sum]
  have hd : ((fullWord h w).length : ℝ) = ∑ k, ((h k).length : ℝ) + w.length := by
    rw [length_fullWord]; push_cast; rfl
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have h43 : log (4 / 3) = 2 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast; ring
  have hlam : logb 2 3 * log 2 = log 3 := by
    rw [logb, div_mul_cancel₀ _ hlog2.ne']
  have key : 2 * ((fullWord h w).length : ℝ) - (2 - logb 2 3) * widthSum n - n -
      (scale n : ℝ) / 8 ≤ (fullWord h w).valSum := by
    rw [hA, hd, hW]; linarith
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have := mul_le_mul_of_nonneg_right key hlog2.le
  rw [h43]
  nlinarith

end CollatzPosDens
