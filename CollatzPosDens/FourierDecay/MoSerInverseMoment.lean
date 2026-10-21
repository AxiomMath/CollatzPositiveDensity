/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnMgfBound
public import CollatzPosDens.Monotone.MoLogSqrt
public import CollatzPosDens.Monotone.MoInvpowSummable

/-!
# A shifted inverse moment of the initial hold

For every real `A` with `1 < A ≤ 5/2` and every integer `J ≥ 2^24`,
`∑_{r ≥ 1} ν₄₅(r) max(J - r, 1)^{-A} ≤ (J - 7/2)^{-A}`.

Put `t = 32A/(31J) ≤ 1/1024`. For `r ≤ J/32` one has
`(J - r)^{-A} ≤ J^{-A} e^{tr}`, because `log J - log(J - r) ≤ r/(J - r) ≤ 32r/(31J)`, so these
terms contribute at most `J^{-A} M₄₅(t) ≤ J^{-A} e^{104A/(31J)}`. For `r > J/32` the power is at
most `1`, and the geometric tail is `(11/16)^{⌊J/32⌋} ≤ e^{-⌊J/32⌋/4}`, which is smaller than
`J^{-A}/(8J)` because `log J ≤ √J`. Finally
`e^{104A/(31J)} + 1/(8J) ≤ e^{7A/(2J)}` and `J^{-A} e^{7A/(2J)} ≤ (J - 7/2)^{-A}`.

## Main results

* `CollatzPosDens.tsum_nu45_mul_max_rpow_neg_le_sub`: the bound above.

## Implementation notes

As in `CollatzPosDens.tsum_nu45_mul_max_rpow_neg_le`, the index `r ≥ 1` is written `r + 1` with
`r : ℕ`, and `max(J - r, 1)^{-A}` is the real power of the integer `max(J - r, 1)` cast to `ℝ`.
Rather than splitting the series at `⌊J/32⌋`, each term is bounded by the sum of a term of the
majorant `J^{-A} ν₄₅(r) e^{tr}` and a term of the geometric tail.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- For `0 ≤ A`, `0 ≤ s` and `32 s ≤ x` with `0 < x - s`,
`(x - s)^{-A} ≤ x^{-A} e^{(32A/(31x)) s}`. -/
lemma sub_rpow_neg_le_rpow_neg_mul_exp {A x s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hsx : 32 * s ≤ x) (hxs : 0 < x - s) :
    (x - s) ^ (-A) ≤ x ^ (-A) * exp (32 * A / (31 * x) * s) := by
  have hx : 0 < x := by linarith
  rw [rpow_def_of_pos hxs, rpow_def_of_pos hx, ← exp_add, exp_le_exp]
  -- `log x - log (x - s) = log (x / (x - s)) ≤ s / (x - s) ≤ 32 s / (31 x)`.
  have hlog : log x - log (x - s) ≤ s / (x - s) := by
    rw [← log_div hx.ne' hxs.ne']
    have := log_le_sub_one_of_pos (div_pos hx hxs)
    have heq : x / (x - s) - 1 = s / (x - s) := by field_simp; ring
    linarith
  have hfrac : s / (x - s) ≤ 32 * s / (31 * x) := by
    rw [div_le_div_iff₀ hxs (by positivity)]
    nlinarith
  have h1 : A * (log x - log (x - s)) ≤ A * (32 * s / (31 * x)) :=
    mul_le_mul_of_nonneg_left (hlog.trans hfrac) hA
  have h2 : 32 * A / (31 * x) * s = A * (32 * s / (31 * x)) := by ring
  nlinarith

/-- The tail `∑_{r ≥ K} ν₄₅(r + 1)` of the geometric law equals `(11/16)^K`. -/
lemma hasSum_nu45_tail (K : ℕ) :
    HasSum (fun r : ℕ ↦ if K ≤ r then nu45 ((r : ℤ) + 1) else 0) ((11 / 16 : ℝ) ^ K) := by
  refine (hasSum_nat_add_iff' K).mp ?_
  have hz : ∑ i ∈ Finset.range K, (if K ≤ i then nu45 ((i : ℤ) + 1) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by simp [Finset.mem_range.mp hi]
  rw [hz, sub_zero]
  have := hasSum_nu45_natCast_add_one.mul_left ((11 / 16 : ℝ) ^ K)
  rw [mul_one] at this
  convert this using 1
  ext i
  have hiK : K ≤ i + K := by omega
  simp only [hiK, ↓reduceIte]
  rw [nu45_natCast_add_one, nu45_natCast_add_one, pow_add]
  ring

/-- **A shifted inverse moment of the initial hold.** For every real `A` with `1 < A ≤ 5/2` and
every integer `J ≥ 2^24`, `∑_{r ≥ 1} ν₄₅(r) max(J - r, 1)^{-A} ≤ (J - 7/2)^{-A}`. -/
@[collatz_pos_dens "lem_mo_ser_inverse_moment"]
theorem tsum_nu45_mul_max_rpow_neg_le_sub {A : ℝ} (hA₁ : 1 < A) (hA₂ : A ≤ 5 / 2) {J : ℤ}
    (hJ : 2 ^ 24 ≤ J) :
    ∑' r : ℕ, nu45 ((r : ℤ) + 1) * (((max (J - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) ≤
      ((J : ℝ) - 7 / 2) ^ (-A) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, J = n := ⟨J.toNat, by omega⟩
  have hn : 2 ^ 24 ≤ n := by exact_mod_cast hJ
  rw [Int.cast_natCast]
  set x : ℝ := (n : ℝ) with hx
  have hx24 : (2 : ℝ) ^ 24 ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hA0 : 0 ≤ A := by linarith
  set K := n / 32 with hKdef
  have hK : x ≤ 32 * (K : ℝ) + 31 := by
    rw [hx]; exact_mod_cast (show n ≤ 32 * K + 31 by omega)
  set t := 32 * A / (31 * x) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 1024 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- The majorant series `∑ ν₄₅(r) e^{t r}` converges, with sum at most `e^{13t/4}`.
  set g : ℕ → ℝ := fun r ↦ nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1)) with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r ↦ mul_nonneg (nu45_nonneg _) (exp_pos _).le
  have hM := mgfNu45_le_exp ht0 ht1
  rw [mgfNu45_def] at hM
  have hne : ∑' r : ℕ, ENNReal.ofReal (g r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM
  have hgs : Summable g := by
    simpa [ENNReal.toReal_ofReal (hg0 _)] using ENNReal.summable_toReal hne
  have hgsum : ∑' r, g r ≤ exp (13 * t / 4) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hgs] at hM
    exact (ENNReal.ofReal_le_ofReal_iff (exp_pos _).le).mp hM
  -- The geometric tail beyond `K = ⌊J/32⌋`.
  set h : ℕ → ℝ := fun r ↦ if K ≤ r then nu45 ((r : ℤ) + 1) else 0 with hh
  have hhs : HasSum h ((11 / 16 : ℝ) ^ K) := hasSum_nu45_tail K
  have hxA : 0 ≤ x ^ (-A) := rpow_nonneg hx0.le _
  -- Termwise comparison.
  have hbound : ∀ r : ℕ,
      nu45 ((r : ℤ) + 1) * (((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) ≤
        x ^ (-A) * g r + h r := by
    intro r
    by_cases hr : K ≤ r
    · have hle : (((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) ≤ 1 :=
        rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast le_max_right _ _) (by linarith)
      have : h r = nu45 ((r : ℤ) + 1) := by simp [hh, hr]
      rw [this]
      nlinarith [nu45_nonneg ((r : ℤ) + 1), mul_nonneg hxA (hg0 r)]
    · have h0 : h r = 0 := by simp [hh, hr]
      rw [h0, add_zero]
      have hr' : 32 * (r + 1) ≤ n := by omega
      have hmax : (max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ) = (n : ℤ) - ((r : ℤ) + 1) := by omega
      have hcast : (((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ)) : ℝ) = x - ((r : ℝ) + 1) := by
        rw [hmax]; push_cast; rfl
      rw [hcast]
      have hr32 : 32 * ((r : ℝ) + 1) ≤ x := by rw [hx]; exact_mod_cast hr'
      have key := sub_rpow_neg_le_rpow_neg_mul_exp hA0 (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)
        hr32 (by linarith)
      calc nu45 ((r : ℤ) + 1) * (x - ((r : ℝ) + 1)) ^ (-A)
          ≤ nu45 ((r : ℤ) + 1) * (x ^ (-A) * exp (t * ((r : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left key (nu45_nonneg _)
        _ = x ^ (-A) * g r := by rw [hg]; ring
  -- Numerical part: write `L = log x`, `a = 13t/4`, `b = 7A/(2x)`.
  set L := log x with hL
  have hL0 : 0 ≤ L := log_nonneg (by linarith)
  have hxA' : x ^ (-A) = exp (L * (-A)) := rpow_def_of_pos hx0 _
  -- The tail is at most `x^{-A}/(8x)`.
  have htail : (11 / 16 : ℝ) ^ K ≤ x ^ (-A) / (8 * x) := by
    have h1 : (11 / 16 : ℝ) ^ K ≤ exp (-(K : ℝ) / 4) := by
      rw [show -(K : ℝ) / 4 = K * (-1 / 4) by ring, exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (-1 / 4 : ℝ)]) K
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity), hxA',
      show 8 * x = exp (log 8 + L) by rw [exp_add, exp_log (by norm_num), hL, exp_log hx0],
      ← exp_add, exp_le_exp]
    have hs : 4096 ≤ sqrt x := le_sqrt_of_sq_le (by nlinarith)
    have hsq : sqrt x ^ 2 = x := sq_sqrt hx0.le
    have hLs : L ≤ sqrt x := log_le_sqrt hx0.le
    have hlog8 : log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
      have := log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      push_cast; linarith
    nlinarith [mul_le_mul_of_nonneg_right hA₂ hL0]
  -- `e^{a} + 1/(8x) ≤ e^{b}`.
  have hexp : exp (13 * t / 4) + 1 / (8 * x) ≤ exp (7 * A / (2 * x)) := by
    have hab : 7 * A / (2 * x) - 13 * t / 4 = 9 * A / (62 * x) := by
      rw [ht]; field_simp; ring
    have hdiff : 1 / (8 * x) ≤ 9 * A / (62 * x) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hea : 1 ≤ exp (13 * t / 4) := one_le_exp (by positivity)
    have he := add_one_le_exp (7 * A / (2 * x) - 13 * t / 4)
    have hsplit : exp (7 * A / (2 * x)) =
        exp (13 * t / 4) * exp (7 * A / (2 * x) - 13 * t / 4) := by
      rw [← exp_add]; ring_nf
    rw [hsplit, hab] at *
    have h9 : 0 ≤ 9 * A / (62 * x) := by positivity
    nlinarith
  -- `x^{-A} e^{b} ≤ (x - 7/2)^{-A}`.
  have hfin : x ^ (-A) * exp (7 * A / (2 * x)) ≤ (x - 7 / 2) ^ (-A) := by
    have hx7 : 0 < x - 7 / 2 := by linarith
    rw [hxA', rpow_def_of_pos hx7, ← exp_add, exp_le_exp]
    have hlog : log (x - 7 / 2) - L ≤ -(7 / (2 * x)) := by
      rw [hL, ← log_div hx7.ne' hx0.ne']
      have := log_le_sub_one_of_pos (div_pos hx7 hx0)
      have heq : (x - 7 / 2) / x - 1 = -(7 / (2 * x)) := by field_simp; ring
      linarith
    have := mul_le_mul_of_nonneg_left hlog hA0
    have heq : 7 * A / (2 * x) = A * (7 / (2 * x)) := by ring
    nlinarith
  calc ∑' r : ℕ, nu45 ((r : ℤ) + 1) * (((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A))
      ≤ ∑' r, (x ^ (-A) * g r + h r) :=
        (summable_nu45_mul_max_rpow_neg A (n : ℤ)).tsum_le_tsum hbound
          ((hgs.mul_left _).add hhs.summable)
    _ = x ^ (-A) * ∑' r, g r + (11 / 16 : ℝ) ^ K := by
        rw [(hgs.mul_left _).tsum_add hhs.summable, tsum_mul_left, hhs.tsum_eq]
    _ ≤ x ^ (-A) * exp (13 * t / 4) + x ^ (-A) / (8 * x) := by gcongr
    _ = x ^ (-A) * (exp (13 * t / 4) + 1 / (8 * x)) := by ring
    _ ≤ x ^ (-A) * exp (7 * A / (2 * x)) := by gcongr
    _ ≤ (x - 7 / 2) ^ (-A) := hfin

end CollatzPosDens
