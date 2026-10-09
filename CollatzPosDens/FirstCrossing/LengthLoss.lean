/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.LengthOk
public import CollatzPosDens.FirstCrossing.BarrierMono
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.Transfer.Concentration
public import CollatzPosDens.Transfer.PrefixExtension

/-!
# Geometric deficit of first crossings failing the length condition

Let `b ≥ 1`, `K ≥ 0` and `u` be integers. Then the first crossings `w ∈ 𝒲(b, u, K)` that
fail the length condition `Λ_{b,u}` carry little geometric mass:
$$\mathbf p(\{w \in \mathcal W(b,u,K) : \neg\Lambda_{b,u}(w)\}) \le 2^{114}/b^6.$$

The family `F` in question is prefix-disjoint with lengths at most `h_b`, so `𝐩(F) ≤ 1`, which
settles `b ≤ 47` since `48^6 < 2^{114}`. For `b ≥ 48`, if `w ∈ F` has length `s` its prefix `p`
of length `t = s - 1 ≥ ℓ_b` satisfies `A(p) < H_{b,u}(t) ≤ H_{b,u}(s) < 2s - ⌊b/8⌋`, hence
`2t - A(p) ≥ ⌊b/8⌋ ≥ b/16`. By `CollatzPosDens.geomMass_eq_geomMass_setOf_prefix_mem`, `𝐩(F)`
is the mass of the words of length `h_b` with a prefix in `F`, each of which has a prefix of
some length `t ∈ [ℓ_b, h_b)` with `|A - 2t| ≥ b/16`. By
`CollatzPosDens.geomMass_setOf_take_mem` and `CollatzPosDens.geomMass_abs_valSum_sub_ge_le`
each `t` contributes at most `2 e^{-b/16384}`, and there are at most `2b` values of `t`.
Finally `4b e^{-b/16384} ≤ 4 · 7! · 16384^7 / b^6 < 2^{114}/b^6`.

## Main results

* `CollatzPosDens.geomMass_firstCrossing_not_lengthOk_le`: the bound above.

## Implementation notes

As in `CollatzPosDens.firstCrossing`, `b` and `K` are natural numbers. The hypothesis
`b ≥ 1` is dropped: the bound is stated in `ℝ≥0∞`, where `2^{114}/0^6 = ⊤`, so the case `b = 0`
holds trivially.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open InformationTheory Real

namespace CollatzPosDens

/-- The final numerical estimate: `4b e^{-b/16384} ≤ 2^{114}/b^6` for `b > 0`. -/
private theorem lengthLoss_real_bound {b : ℝ} (hb : 0 < b) :
    4 * b * exp (-(b / 16384)) ≤ 2 ^ 114 / b ^ 6 := by
  have hx : 0 ≤ b / 16384 := by positivity
  have h7 := Real.pow_div_factorial_le_exp (b / 16384) hx 7
  have hfac : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hfac] at h7
  have hexp : exp (-(b / 16384)) ≤ 5040 * 16384 ^ 7 / b ^ 7 := by
    rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by positivity)]
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h7
    nlinarith
  calc 4 * b * exp (-(b / 16384)) ≤ 4 * b * (5040 * 16384 ^ 7 / b ^ 7) := by gcongr
    _ = 4 * 5040 * 16384 ^ 7 / b ^ 6 := by field_simp
    _ ≤ 2 ^ 114 / b ^ 6 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      norm_num

/-- **Length loss.** For any `b`, `u` and `K`, the first crossings `w ∈ 𝒲(b, u, K)` failing
the length condition `Λ_{b,u}` have geometric mass at most `2^{114}/b^6`. -/
@[collatz_pos_dens "lem_length_loss"]
theorem geomMass_firstCrossing_not_lengthOk_le (b : ℕ) (u : ℤ) (K : ℕ) :
    geomMass {w | w ∈ firstCrossing b u K ∧ ¬LengthOk b u w} ≤ 2 ^ 114 / (b : ℝ≥0∞) ^ 6 := by
  set F := {w | w ∈ firstCrossing b u K ∧ ¬LengthOk b u w}
  have hF : IsPrefixFree F := fun x hx y hy hxy =>
    isPrefixFree_firstCrossing b u K x hx.1 y hy.1 hxy
  have hFlen : ∀ w ∈ F, w.length ≤ hb b := fun w hw =>
    length_le_hb_of_mem_firstCrossing hw.1
  -- small `b`: the trivial bound `𝐩(F) ≤ 1`
  rcases lt_or_ge b 48 with hsmall | h48
  · refine (geomMass_le_one_of_isPrefixFree hF hFlen).trans ?_
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [ENNReal.div_zero (by norm_num)]
      exact le_top
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    have : b ^ 6 ≤ 2 ^ 114 := (Nat.pow_le_pow_left hsmall.le 6).trans (by norm_num)
    exact_mod_cast this
  set v : ℝ := b / 16
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- every word of `F` has a prefix of length `t ∈ [ℓ_b, h_b)` deviating by `b/16`
  have hdev : ∀ w ∈ F, ∃ t ∈ Finset.Ico (lb b) (hb b), ∃ p ∈ valSumDevSet v t, p <+: w := by
    rintro w ⟨hw, hΛ⟩
    have hl := lb_lt_length_of_mem_firstCrossing hw
    have hh := length_le_hb_of_mem_firstCrossing hw
    obtain ⟨t, ht⟩ : ∃ t, w.length = t + 1 := ⟨w.length - 1, by omega⟩
    have hA := valSum_take_lt_of_mem_firstCrossing hw (i := t) (by omega) (by omega)
    have hmono := barrier_le_barrier_succ b u t
    rw [lengthOk_iff, not_le, ht] at hΛ
    have hlen : (w.take t).length = t := by simp; omega
    refine ⟨t, Finset.mem_Ico.2 ⟨by omega, by omega⟩, w.take t, ⟨hlen, ?_⟩, List.take_prefix _ _⟩
    have hint : ((Word.valSum (w.take t) : ℕ) : ℤ) + (b / 8 : ℕ) ≤ 2 * t := by
      push_cast at hΛ ⊢; linarith
    have hreal : ((Word.valSum (w.take t) : ℕ) : ℝ) + (b / 8 : ℕ) ≤ 2 * t := by
      exact_mod_cast hint
    have h8 : (b : ℝ) / 16 ≤ ((b / 8 : ℕ) : ℝ) := by
      have h1 : (b : ℝ) < 8 * (((b / 8 : ℕ) : ℝ) + 1) := by
        have : b < 8 * (b / 8 + 1) := by omega
        exact_mod_cast this
      have h2 : (48 : ℝ) ≤ b := by exact_mod_cast h48
      linarith
    rw [abs_sub_comm]
    exact (h8.trans (by linarith)).trans (le_abs_self _)
  -- the deviation bound for each `t ∈ [ℓ_b, h_b)`
  have hconc : ∀ t ∈ Finset.Ico (lb b) (hb b),
      geomMass (valSumDevSet v t) ≤ ENNReal.ofReal (2 * exp (-(b / 16384 : ℝ))) := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
    refine (geomMass_abs_valSum_sub_ge_le t v (by positivity)).trans ?_
    gcongr
    have htpos : (0 : ℝ) < t := by
      have : 0 < lb b := by rw [lb_eq]; omega
      exact_mod_cast (show 0 < t by omega)
    have ht2 : (t : ℝ) ≤ 2 * b := by
      have := hb_le_two_mul b
      exact_mod_cast (show t ≤ 2 * b by omega)
    refine le_min ?_ ?_
    · rw [le_div_iff₀ (by positivity)]
      simp only [v]
      nlinarith
    · simp only [v]
      linarith
  -- assembling the pieces
  have hcard : ((Finset.Ico (lb b) (hb b)).card : ℝ) ≤ 2 * b := by
    have := hb_le_two_mul b
    rw [Nat.card_Ico]
    exact_mod_cast (show hb b - lb b ≤ 2 * b by omega)
  calc geomMass F
      = geomMass {x : Word | x.length = hb b ∧ ∃ w ∈ F, w <+: x} :=
        geomMass_eq_geomMass_setOf_prefix_mem hF hFlen
    _ ≤ geomMass (⋃ t ∈ Finset.Ico (lb b) (hb b),
          {x : Word | x.length = hb b ∧ x.take t ∈ valSumDevSet v t}) := by
        apply geomMass_mono
        rintro x ⟨hx, w, hw, hwx⟩
        obtain ⟨t, ht, p, hp, hpw⟩ := hdev w hw
        have hpx := hpw.trans hwx
        have : x.take t = p := by
          rw [List.prefix_iff_eq_take.mp hpx, hp.1]
        exact Set.mem_biUnion ht ⟨hx, this ▸ hp⟩
    _ ≤ ∑ t ∈ Finset.Ico (lb b) (hb b),
          geomMass {x : Word | x.length = hb b ∧ x.take t ∈ valSumDevSet v t} :=
        ENNReal.tsum_biUnion_le _ _ _
    _ = ∑ t ∈ Finset.Ico (lb b) (hb b), geomMass (valSumDevSet v t) :=
        Finset.sum_congr rfl fun t ht =>
          geomMass_setOf_take_mem (Finset.mem_Ico.1 ht).2.le fun _ hp => hp.1
    _ ≤ ∑ _t ∈ Finset.Ico (lb b) (hb b), ENNReal.ofReal (2 * exp (-(b / 16384 : ℝ))) :=
        Finset.sum_le_sum hconc
    _ = ENNReal.ofReal ((Finset.Ico (lb b) (hb b)).card * (2 * exp (-(b / 16384 : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 ^ 114 / (b : ℝ) ^ 6) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ((Finset.Ico (lb b) (hb b)).card : ℝ) * (2 * exp (-(b / 16384 : ℝ)))
            ≤ 2 * b * (2 * exp (-(b / 16384 : ℝ))) := by gcongr
          _ = 4 * b * exp (-(b / 16384 : ℝ)) := by ring
          _ ≤ _ := lengthLoss_real_bound hbpos
    _ = 2 ^ 114 / (b : ℝ≥0∞) ^ 6 := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hbpos.le,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

end CollatzPosDens
