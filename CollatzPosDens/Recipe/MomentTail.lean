/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Varrho
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Whole tails of polynomial-geometric sums

Let `ϱ = 𝗀^{-1} = 100/101` be the error decay ratio. For a real exponent `d` with
`0 ≤ d ≤ 9/2` and an integer `n ≥ 6000000`, the tail of the moment series satisfies
$$\sum_{j \ge n} j^d \varrho^j < 162\, n^d \varrho^n.$$

The proof is a ratio test with explicit constants: for `j ≥ n`,
$$\frac{(j+1)^d\varrho^{j+1}}{j^d\varrho^j} \le \Bigl(\frac{n+1}{n}\Bigr)^{9/2}\varrho
  \le \Bigl(\frac{6000001}{6000000}\Bigr)^{9/2}\frac{100}{101}
  < \frac{161}{162},$$
the last step being, after squaring, the exact rational comparison
`6000001^9 · 100^2 · 162^2 < 161^2 · 6000000^9 · 101^2`. Hence the terms are dominated by
`(161/162)^{j-n} n^d ϱ^n`, strictly for `j > n`, and the geometric series sums to `162 n^d ϱ^n`.

## Main results

* `CollatzPosDens.moment_tail_lt`: the tail series is summable and
  `∑_{j ≥ n} j^d ϱ^j < 162 n^d ϱ^n`.
* `CollatzPosDens.moment_tail_lt_ratio`: the one-step ratio bound
  `(j+1)^d ϱ^{j+1} < (161/162) j^d ϱ^j` for real `j ≥ 6000000`.

## Implementation notes

The power `j^d` with real exponent is `Real.rpow` of the cast `(j : ℝ)`. The tail is the sum over
the subtype `Set.Ici n` of `ℕ`; summability is part of the conclusion, so that the bound on the
`tsum` is not vacuous. The hypothesis `0 ≤ d` of the source is not needed: the ratio
`((j+1)/j)^d` is at most `1` for `d ≤ 0`, so only `d ≤ 9/2` is assumed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The numerical core: `(6000001/6000000)^{9/2} ϱ < 161/162`. -/
private lemma moment_tail_lt_const :
    (6000001 / 6000000 : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio < 161 / 162 := by
  have h0 : 0 ≤ (6000001 / 6000000 : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio :=
    mul_nonneg (by positivity) errorDecayRatio_nonneg
  refine (pow_lt_pow_iff_left₀ h0 (by norm_num) (n := 2) (by norm_num)).1 ?_
  rw [mul_pow, errorDecayRatio_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **One-step ratio bound.** For real `j ≥ 6000000` and `d ≤ 9/2`,
`(j+1)^d ϱ^{k+1} < (161/162) j^d ϱ^k`. -/
theorem moment_tail_lt_ratio {d : ℝ} (hd : d ≤ 9 / 2) {j : ℝ} (hj : 6000000 ≤ j) (k : ℕ) :
    (j + 1) ^ d * errorDecayRatio ^ (k + 1) < 161 / 162 * (j ^ d * errorDecayRatio ^ k) := by
  have hj0 : 0 < j := by linarith
  set x : ℝ := (j + 1) / j with hx
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ hj0]
    linarith
  have hxle : x ≤ 6000001 / 6000000 := by
    rw [hx, div_le_div_iff₀ hj0 (by norm_num)]
    linarith
  have hxd : x ^ d ≤ (6000001 / 6000000 : ℝ) ^ (9 / 2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1 hd).trans
      (Real.rpow_le_rpow (by linarith) hxle (by norm_num))
  have hsplit : (j + 1) ^ d = x ^ d * j ^ d := by
    rw [hx, Real.div_rpow (by linarith) hj0.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hj0 d).ne']
  have hpos : 0 < j ^ d * errorDecayRatio ^ k :=
    mul_pos (Real.rpow_pos_of_pos hj0 d) (pow_pos errorDecayRatio_pos k)
  calc (j + 1) ^ d * errorDecayRatio ^ (k + 1)
      = (x ^ d * errorDecayRatio) * (j ^ d * errorDecayRatio ^ k) := by
        rw [hsplit, pow_succ]
        ring
    _ ≤ ((6000001 / 6000000 : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio) *
          (j ^ d * errorDecayRatio ^ k) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hxd errorDecayRatio_nonneg) hpos.le
    _ < 161 / 162 * (j ^ d * errorDecayRatio ^ k) :=
        mul_lt_mul_of_pos_right moment_tail_lt_const hpos

/-- The shift `k ↦ n + k` identifies `ℕ` with the tail `Set.Ici n`. -/
private def moment_tail_lt_equiv (n : ℕ) : ℕ ≃ Set.Ici n where
  toFun k := ⟨n + k, by simp⟩
  invFun j := (j : ℕ) - n
  left_inv k := by simp
  right_inv j := Subtype.ext (Nat.add_sub_of_le j.2)

/-- **Whole tails of polynomial-geometric sums.** For real `d ≤ 9/2` (in particular for
`0 ≤ d ≤ 9/2`) and an integer `n ≥ 6000000`, the series `∑_{j ≥ n} j^d ϱ^j` is summable and
`∑_{j ≥ n} j^d ϱ^j < 162 n^d ϱ^n`. -/
@[collatz_pos_dens "lem_moment_tail"]
theorem moment_tail_lt {d : ℝ} (hd : d ≤ 9 / 2) {n : ℕ} (hn : 6000000 ≤ n) :
    Summable (fun j : Set.Ici n => ((j : ℕ) : ℝ) ^ d * errorDecayRatio ^ (j : ℕ)) ∧
      ∑' j : Set.Ici n, ((j : ℕ) : ℝ) ^ d * errorDecayRatio ^ (j : ℕ) <
        162 * ((n : ℝ) ^ d * errorDecayRatio ^ n) := by
  set f : Set.Ici n → ℝ := fun j => ((j : ℕ) : ℝ) ^ d * errorDecayRatio ^ (j : ℕ) with hf
  set e := moment_tail_lt_equiv n
  set b : ℕ → ℝ := fun k => ((n + k : ℕ) : ℝ) ^ d * errorDecayRatio ^ (n + k) with hb
  have hfe : f ∘ e = b := rfl
  set a : ℝ := (n : ℝ) ^ d * errorDecayRatio ^ n with ha
  set q : ℝ := 161 / 162 with hq
  have hn' : (6000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hstep : ∀ k, b (k + 1) < q * b k := by
    intro k
    have h := moment_tail_lt_ratio hd (j := ((n + k : ℕ) : ℝ))
      (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (n + k)
    simp only [hb]
    convert h using 2
    rw [← add_assoc]
    push_cast
    rfl
  have hbnn : ∀ k, 0 ≤ b k := fun k =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg errorDecayRatio_nonneg _)
  have hle : ∀ k, b k ≤ q ^ k * a := by
    intro k
    induction k with
    | zero => simp [hb, ha]
    | succ k ih =>
      calc b (k + 1) ≤ q * b k := (hstep k).le
        _ ≤ q * (q ^ k * a) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = q ^ (k + 1) * a := by ring
  have hg : HasSum (fun k : ℕ => q ^ k * a) (162 * a) := by
    have := (hasSum_geometric_of_lt_one (r := q) (by norm_num) (by norm_num)).mul_right a
    convert this using 1
    norm_num [hq]
  have hbs : Summable b := hg.summable.of_nonneg_of_le hbnn hle
  refine ⟨e.summable_iff.1 (hfe ▸ hbs), ?_⟩
  rw [← e.tsum_eq, ← hg.tsum_eq]
  change ∑' k, b k < _
  exact hbs.tsum_lt_tsum hle ((hstep 0).trans_le (by simp [hb, ha])) hg.summable

end CollatzPosDens
