/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3Exc
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The exceptional allowances are summable

Write `b = (25/27)^136` and `b₂ = (3/8)^14`. Since `e ≥ 8/3` we have `e^(-14) ≤ b₂`, so for
`v ≥ 1` the exceptional allowance satisfies `Exc(v) ≤ 9 b^(v+1) + b (8b)^v + b₂^(v+1)`, while
`Exc(0) = 9b`. As `8b < 1` and `b₂ < 1`, summing over any finite set `V` of positive offsets
and comparing with the full geometric series gives
`Exc(0) + ∑_{v ∈ V} Exc(v) ≤ 9 (b + b²/(1-b)) + b · 8b/(1-8b) + b₂²/(1-b₂)`,
and exact rational arithmetic shows that `3360` times the right-hand side is `< 1`.

## Main results

* `CollatzPosDens.c3Exc_zero_add_sum_lt`: for every finite set `V` of offsets `v ≥ 1`,
  `Exc(0) + ∑_{v ∈ V} Exc(v) < 1/3360`.
* `CollatzPosDens.c3Exc_le_geom`: the geometric majorant of `Exc(v)` for `v ≥ 1`.

## Implementation notes

Since `Exc` is defined on `ℕ`, the set `V` is a `Finset ℕ`, and the hypothesis on its elements
is `v ≥ 1` rather than `v ≥ 2`: the same geometric comparison, started at `v = 1`, still gives
the bound, so the statement covers the case `v ≥ 2`.

## References

* [Mazur, *Collatz positive density*], §10.1 ("Scalar facts").
-/

@[expose] public section

namespace CollatzPosDens

/-- `e^(-14) ≤ (3/8)^14`, from `e ≥ 8/3`. -/
private lemma exp_neg_fourteen_le : Real.exp (-14) ≤ (3 / 8 : ℝ) ^ 14 := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
  have h14 : Real.exp 14 = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (8 / 3 : ℝ) ^ 14 ≤ Real.exp 14 := h14 ▸ pow_le_pow_left₀ (by norm_num) he 14
  rw [Real.exp_neg, show (3 / 8 : ℝ) ^ 14 = ((8 / 3 : ℝ) ^ 14)⁻¹ by norm_num]
  exact inv_anti₀ (by positivity) hpow

/-- For `v ≥ 1`, with `b = (25/27)^136` and `b₂ = (3/8)^14`,
`Exc(v) ≤ 9 b b^v + b (8b)^v + b₂ b₂^v`. -/
theorem c3Exc_le_geom {v : ℕ} (hv : 1 ≤ v) :
    c3Exc v ≤ 9 * (25 / 27 : ℝ) ^ 136 * ((25 / 27 : ℝ) ^ 136) ^ v +
      (25 / 27 : ℝ) ^ 136 * (8 * (25 / 27 : ℝ) ^ 136) ^ v +
      (3 / 8 : ℝ) ^ 14 * ((3 / 8 : ℝ) ^ 14) ^ v := by
  rw [c3Exc_of_one_le hv]
  have hb : (25 / 27 : ℝ) ^ (136 * (v + 1)) =
      (25 / 27 : ℝ) ^ 136 * ((25 / 27 : ℝ) ^ 136) ^ v := by
    rw [pow_mul, pow_succ]
    ring
  have he : Real.exp (-14 * ((v : ℝ) + 1)) = Real.exp (-14) ^ (v + 1) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have he' : Real.exp (-14) ^ (v + 1) ≤ ((3 / 8 : ℝ) ^ 14) ^ (v + 1) :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_fourteen_le _
  rw [pow_succ' ((3 / 8 : ℝ) ^ 14)] at he'
  rw [hb, he, mul_pow]
  linarith [he']

/-- **The exceptional allowances are summable**: for every finite set `V` of offsets `v ≥ 1`,
`Exc(0) + ∑_{v ∈ V} Exc(v) < 1/3360`. -/
@[collatz_pos_dens "lem_c3_exc_sum"]
theorem c3Exc_zero_add_sum_lt (V : Finset ℕ) (hV : ∀ v ∈ V, 1 ≤ v) :
    c3Exc 0 + ∑ v ∈ V, c3Exc v < 1 / 3360 := by
  set b : ℝ := (25 / 27 : ℝ) ^ 136 with hb
  set b₂ : ℝ := (3 / 8 : ℝ) ^ 14 with hb₂
  have hb1 : b < 1 := by norm_num [hb]
  have h8b1 : 8 * b < 1 := by norm_num [hb]
  have hb₂1 : b₂ < 1 := by norm_num [hb₂]
  set N := V.sup id + 1
  have hVsub : V ⊆ Finset.Ico 1 N := fun v hv =>
    Finset.mem_Ico.2 ⟨hV v hv, Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)⟩
  have hgeom : ∀ x : ℝ, 0 ≤ x → x < 1 → ∑ v ∈ Finset.Ico 1 N, x ^ v ≤ x / (1 - x) := by
    intro x hx0 hx1
    simpa using geom_sum_Ico_le_of_lt_one (m := 1) (n := N) hx0 hx1
  have hsum : ∑ v ∈ V, c3Exc v ≤
      9 * b * (b / (1 - b)) + b * (8 * b / (1 - 8 * b)) + b₂ * (b₂ / (1 - b₂)) := by
    calc ∑ v ∈ V, c3Exc v
        ≤ ∑ v ∈ V, (9 * b * b ^ v + b * (8 * b) ^ v + b₂ * b₂ ^ v) :=
          Finset.sum_le_sum fun v hv => c3Exc_le_geom (hV v hv)
      _ ≤ ∑ v ∈ Finset.Ico 1 N, (9 * b * b ^ v + b * (8 * b) ^ v + b₂ * b₂ ^ v) :=
          Finset.sum_le_sum_of_subset_of_nonneg hVsub fun v _ _ => by positivity
      _ = 9 * b * ∑ v ∈ Finset.Ico 1 N, b ^ v + b * ∑ v ∈ Finset.Ico 1 N, (8 * b) ^ v +
            b₂ * ∑ v ∈ Finset.Ico 1 N, b₂ ^ v := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          · exact hgeom b (by positivity) hb1
          · exact hgeom (8 * b) (by positivity) h8b1
          · exact hgeom b₂ (by positivity) hb₂1
  have hfin : 9 * b + (9 * b * (b / (1 - b)) + b * (8 * b / (1 - 8 * b)) +
      b₂ * (b₂ / (1 - b₂))) < 1 / 3360 := by
    rw [hb, hb₂]
    norm_num
  rw [c3Exc_zero]
  linarith

end CollatzPosDens
