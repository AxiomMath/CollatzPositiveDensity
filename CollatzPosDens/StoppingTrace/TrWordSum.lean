/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Fin
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnPascalTotal

/-!
# A weighted sum over nonclosing words

For a word `c ∈ ℤ^m`, weight each letter `a` by the Pascal weight `ϖ(a)` unless `a` is a closing
letter `4` or `5` (which gets weight `0`), and multiply further by `1163/1250` for each letter
equal to `3`. The total weight of all words of length `m` is `(6701/10000)^m`:
\[
\sum_{c\in\mathbb{Z}^m}\Bigl(\prod_{i=1}^m[c_i\notin\{4,5\}]\varpi(c_i)\Bigr)
  \Bigl(\frac{1163}{1250}\Bigr)^{\#\{i : c_i = 3\}} = \Bigl(\frac{6701}{10000}\Bigr)^m.
\]
The summand is the product `∏ᵢ φ(cᵢ)` of a nonnegative one-letter weight `φ`, so the sum
factorises as `(∑_a φ(a))^m`, and `∑_a φ(a) = 1 - ϖ(3) - ϖ(4) - ϖ(5) + (1163/1250) ϖ(3)
= 6701/10000` since `ϖ(3) = 1/4`, `ϖ(4) = 3/16`, `ϖ(5) = 1/8`.

## Main results

* `CollatzPosDens.hasSum_trWordSum`: the identity above, as an unconditionally convergent
  sum over `Fin m → ℤ`.
* `CollatzPosDens.tsum_trWordSum`: the same identity for `tsum`.

## Implementation notes

`ℤ^m` is `Fin m → ℤ`. The sum is stated with `HasSum`, i.e. as an unconditional sum; since the
terms are nonnegative this agrees with the sum in the Tonelli sense, and it also records
convergence. The factorisation `∑_{c ∈ ι^m} ∏ᵢ φ(cᵢ) = (∑_a φ(a))^m` for nonnegative summable
`φ` is `hasSum_pi_fin_prod_of_nonneg`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The one-letter weight: `ϖ(a)` off the closing letters `4, 5`, damped by `1163/1250` at
`a = 3`. -/
private noncomputable def trWordSumLetter (a : ℤ) : ℝ :=
  varpiIn a * (1163 / 1250 : ℝ) ^ (if a = 3 then 1 else 0)

private lemma trWordSumLetter_eq :
    trWordSumLetter = Function.update (Function.update (Function.update varpi 3
      (varpi 3 * (1163 / 1250))) 4 0) 5 0 := by
  funext a
  simp only [trWordSumLetter, varpiIn, Set.mem_insert_iff, Set.mem_singleton_iff,
    Function.update_apply]
  by_cases h5 : a = 5
  · simp [h5]
  by_cases h4 : a = 4
  · simp [h4]
  by_cases h3 : a = 3
  · simp [h3]
  simp [h3, h4, h5]

private lemma hasSum_trWordSumLetter : HasSum trWordSumLetter (6701 / 10000) := by
  rw [trWordSumLetter_eq]
  convert ((hasSum_varpi.update 3 (varpi 3 * (1163 / 1250))).update 4 0).update 5 0 using 1
  simp [varpi_three, varpi_four, varpi_five]
  norm_num

private lemma trWordSumLetter_nonneg (a : ℤ) : 0 ≤ trWordSumLetter a := by
  unfold trWordSumLetter
  have := varpiIn_nonneg a
  positivity

/-- **Weighted sum over nonclosing words.** For every `m`,
`∑_{c ∈ ℤ^m} (∏ᵢ ϖ_in(cᵢ)) (1163/1250)^{#{i : cᵢ = 3}} = (6701/10000)^m`, where
`ϖ_in(a) = [a ∉ {4, 5}] ϖ(a)`. -/
@[collatz_pos_dens "lem_tr_word_sum"]
theorem hasSum_trWordSum (m : ℕ) :
    HasSum (fun c : Fin m → ℤ ↦ (∏ i, varpiIn (c i)) * (1163 / 1250 : ℝ) ^ #{i | c i = 3})
      ((6701 / 10000 : ℝ) ^ m) := by
  convert hasSum_pi_fin_prod_of_nonneg hasSum_trWordSumLetter trWordSumLetter_nonneg m using 1
  ext c
  simp only [trWordSumLetter, prod_mul_distrib, prod_pow_eq_pow_sum, sum_boole, Nat.cast_id]

/-- The weighted sum over nonclosing words of length `m`, as a `tsum`. -/
theorem tsum_trWordSum (m : ℕ) :
    ∑' c : Fin m → ℤ, (∏ i, varpiIn (c i)) * (1163 / 1250 : ℝ) ^ #{i | c i = 3} =
      (6701 / 10000 : ℝ) ^ m :=
  (hasSum_trWordSum m).tsum_eq

end CollatzPosDens
