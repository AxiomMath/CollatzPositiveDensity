/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChPairFactorRange
public import CollatzPosDens.CharSum.ChPenalty
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChWhiteCancel
public import CollatzPosDens.CharSum.ChWhiteCancelFour
public import CollatzPosDens.CharSum.ChWhiteCancelFive
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.Transfer.Z

/-!
# The pair factors of a word are bounded by its penalty

Fix `n`, `ξ ∈ G_n` and `ε ≥ ε_* = 8/217`. For every word `b = (b₁, …, b_k)` of integers,
`∏_{i=1}^k Fp(i, b₁ + ⋯ + b_{i-1}, b_i) ≤ Pen(b)`.

Both sides are products of nonnegative factors over `i`, and the comparison is factor by
factor. Write `s_i = b₁ + ⋯ + b_{i-1}` and `p_i = (i, s_i + b_i)`. On the right the `i`-th
factor is `w(p_i)` if `b_i ∈ {4,5}`, `w₃(p_i)` if `b_i = 3` and `1` otherwise. Since
`0 ≤ Fp ≤ 1`, only a white point `p_i` with `b_i ∈ {3,4,5}` needs an argument; there
`|ϑ_{n,ξ}(p_i)| > ε ≥ 8/217`, and the cancellation lemmas for the letters `3`, `4` and `5` give
`Fp(i, s_i, 3) < e^{-κ_* z_*} = w₃(p_i)` and `Fp(i, s_i, b_i) < e^{-z_*} = w(p_i)` for
`b_i ∈ {4,5}`.

## Main results

* `CollatzPosDens.prod_chPairFactor_le_chPenalty`:
  `∏ᵢ Fp(i, b₁ + ⋯ + b_{i-1}, b_i) ≤ Pen(b)`.
* `CollatzPosDens.prod_chPairFactor_le_chPenaltyFrom`: the same bound for the penalty
  shifted by a starting index and a starting height.
* `CollatzPosDens.chPairFactor_le_chPenaltyFrom_letter`: the factor-by-factor comparison.

## Implementation notes

Words are `List ℤ`, indexed from `0`, so the factor with index `i` above is the term
`i - 1 : Fin b.length`, with letter `b[i - 1]` and prefix sum `(b.take (i - 1)).sum`. The
statement is proved, by induction on the word, for the penalty shifted by a starting index and
a starting height.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The pair factor `Fp(j + 1, s, a)` is at most the contribution of the letter `a` at the point
`(j + 1, s + a)` to the penalty, provided `ε ≥ ε_*`. -/
theorem chPairFactor_le_chPenaltyFrom_letter {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (j : ℕ) (s a : ℤ) :
    chPairFactor n ξ (j + 1) s a ≤
      (if a ∈ ({4, 5} : Finset ℤ) then chWhiteFactor n ξ ε ((j : ℤ) + 1, s + a) else 1) *
        (if a = 3 then chRaw3Factor n ξ ε ((j : ℤ) + 1, s + a) else 1) := by
  have hle := chPairFactor_le_one n ξ (j + 1) s a
  have hθ : IsBkWhite n ξ ε ((j : ℤ) + 1, s + a) →
      8 / 217 < |bkTheta n ξ (((j + 1 : ℕ) : ℤ), s + a)| := fun hw => by
    have h := hw.lt_abs_bkTheta
    rw [epsStar_cast] at hε
    push_cast
    linarith
  by_cases hw : IsBkWhite n ξ ε ((j : ℤ) + 1, s + a)
  · have h8 := hθ hw
    rw [chWhiteFactor_of_isBkWhite' hw, chRaw3Factor_of_isBkWhite' hw]
    by_cases h3 : a = 3
    · subst h3
      simpa using chPairFactor_three_lt_exp h8 |>.le
    by_cases h4 : a = 4
    · subst h4
      simpa using (chPairFactor_four_lt_exp_neg n ξ (j + 1) s h8).le
    by_cases h5 : a = 5
    · subst h5
      simpa using (chPairFactor_five_lt_exp h8).le
    simp [h3, h4, h5, hle]
  · rw [chWhiteFactor_of_not_isBkWhite hw, chRaw3Factor_of_not_isBkWhite hw]
    simpa using hle

/-- The product of the pair factors of a word `b`, read from index `j` and height `s`, is at
most the penalty of `b` shifted by `(j, s)`. -/
theorem prod_chPairFactor_le_chPenaltyFrom {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (j : ℕ) (s : ℤ) (b : List ℤ) :
    ∏ i : Fin b.length, chPairFactor n ξ (j + i + 1) (s + (b.take i).sum) b[i] ≤
      chPenaltyFrom n ξ ε j s b := by
  induction b generalizing j s with
  | nil => simp
  | cons a b ih =>
    rw [chPenaltyFrom_cons]
    erw [Fin.prod_univ_succ (n := b.length)]
    refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => chPairFactor_nonneg _ _ _ _ _)
      (mul_nonneg (by split_ifs <;> first | exact chWhiteFactor_nonneg _ _ _ _ |
        exact zero_le_one) (by split_ifs <;> first | exact chRaw3Factor_nonneg _ _ _ _ |
        exact zero_le_one))
    · simpa using chPairFactor_le_chPenaltyFrom_letter hε j s a
    · convert ih (j + 1) (s + a) using 2 with i
      · simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons]
        congr 1
        · ring
        · ring
      · push_cast; rfl

/-- **The pair factors of a word are bounded by its penalty.** For `ε ≥ ε_*` and every word
`b = (b₁, …, b_k)`, `∏_{i=1}^k Fp(i, b₁ + ⋯ + b_{i-1}, b_i) ≤ Pen(b)`. -/
@[collatz_pos_dens "lem_ch_factor_penalty"]
theorem prod_chPairFactor_le_chPenalty {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (b : List ℤ) :
    ∏ i : Fin b.length, chPairFactor n ξ (i + 1) (b.take i).sum b[i] ≤ chPenalty n ξ ε b := by
  simpa [chPenalty] using prod_chPairFactor_le_chPenaltyFrom hε 0 0 b

end CollatzPosDens
