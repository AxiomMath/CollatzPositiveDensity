/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.EbLower
public import CollatzPosDens.FirstCrossing.FcComplement
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.Overshoot
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.Transfer.Concentration
public import CollatzPosDens.Transfer.GeometricMass

/-!
# Deficit of a full first-crossing family

Let `b`, `K ≥ 0` and `u` be integers with `0 ≤ u ≤ 2 r_b`. Then the first-crossing family
`𝒲(b, u, K)` misses little geometric mass:
$$1 - \mathbf p(\mathcal W(b,u,K)) \le 2^{140}/b^6 + 2^{-(K+1)}.$$

Write `H = H_{b,u}`, `ℓ = ℓ_b`, `h = h_b` and `e = e_b`. The family is prefix-disjoint with
lengths at most `h`, so `1 - 𝐩(𝒲(b, u, K))` is the mass of the words `v` of length `h` with no
prefix in it. Such a word either has `A_ℓ(v) ≥ H(ℓ)`, or `A_h(v) < H(h)`, or its first
crossing of `H` after time `ℓ` overshoots by more than `K`. Since `H(ℓ) = 2ℓ + 2e + u` and
`H(h) = 2h - 2e + u - 2 r_b`, the hypothesis `0 ≤ u ≤ 2 r_b` puts the first two events inside
`{|A_ℓ - 2ℓ| ≥ 2e}` and `{|A_h - 2h| ≥ 2e}`. As `e ≥ b/100` and `1 ≤ ℓ, h ≤ 2b`, the
concentration bound gives each of them mass at most `2 e^{-b/160000}`; the third event has mass
at most `2^{-(K+1)}` by the overshoot bound. Finally
`4 e^{-b/160000} ≤ 4 · 6! · 160000^6 / b^6 < 2^{140}/b^6`.

## Main results

* `CollatzPosDens.one_sub_geomMass_firstCrossing_le`: the bound above.

## Implementation notes

As in `CollatzPosDens.firstCrossing`, `b` and `K` are natural numbers. The bound is stated in
`ℝ≥0∞`, where `1 - 𝐩(𝒲(b, u, K))` is truncated subtraction and `2^{-(K+1)}` is `2⁻¹ ^ (K + 1)`.
No lower bound on `b` is assumed: for `b ≤ 1` the right-hand side is at least `1`, and for
`b ≥ 2` the window satisfies `1 ≤ ℓ_b < h_b`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open InformationTheory Real

namespace CollatzPosDens

/-- The barrier at the lower end of the window: `H_{b,u}(ℓ_b) = 2ℓ_b + 2e_b + u`. -/
private theorem deficitFamily_barrier_lb (b : ℕ) (u : ℤ) :
    barrier b u (lb b) = 2 * (lb b : ℤ) + 2 * eb b + u := by
  have h := lb_add_wb b
  rw [barrier_of_ge u (lb_le_self b), show b - lb b = wb b by omega, rb_def]
  have : (b : ℤ) = lb b + wb b := by exact_mod_cast h.symm
  rw [this]
  ring

/-- The barrier at the upper end of the window: `H_{b,u}(h_b) = 2h_b - 2e_b + u - 2r_b`. -/
private theorem deficitFamily_barrier_hb (b : ℕ) (u : ℤ) :
    barrier b u (hb b) = 2 * (hb b : ℤ) - 2 * eb b + u - 2 * rb b := by
  rw [barrier_of_le u (le_hb b), show hb b - b = wb b by rw [hb_def]; omega, rb_def, hb_def]
  push_cast
  ring

/-- The final numerical estimate: `4 e^{-b/160000} ≤ 2^{140}/b^6` for `b > 0`. -/
private theorem deficitFamily_real_bound {b : ℝ} (hb : 0 < b) :
    4 * exp (-(b / 160000)) ≤ 2 ^ 140 / b ^ 6 := by
  have hx : 0 ≤ b / 160000 := by positivity
  have h6 := Real.pow_div_factorial_le_exp (b / 160000) hx 6
  have hfac : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfac] at h6
  have hexp : exp (-(b / 160000)) ≤ 720 * 160000 ^ 6 / b ^ 6 := by
    rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by positivity)]
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h6
    nlinarith
  calc 4 * exp (-(b / 160000)) ≤ 4 * (720 * 160000 ^ 6 / b ^ 6) := by gcongr
    _ = 4 * 720 * 160000 ^ 6 / b ^ 6 := by ring
    _ ≤ 2 ^ 140 / b ^ 6 := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- Every length-`h_b` word with no prefix in `𝒲(b, u, K)` deviates at `ℓ_b`, deviates at `h_b`,
or overshoots the barrier by more than `K` at its first crossing after `ℓ_b`. -/
private theorem setOf_not_prefix_firstCrossing_subset {b : ℕ} {u : ℤ} (hu0 : 0 ≤ u)
    (hu : u ≤ 2 * rb b) (K : ℕ) (hb2 : 2 ≤ b) :
    {x : Word | x.length = hb b ∧ ¬ ∃ w ∈ firstCrossing b u K, w <+: x} ⊆
      {x : Word | x.length = hb b ∧ x.take (lb b) ∈ valSumDevSet (2 * eb b : ℝ) (lb b)} ∪
        valSumDevSet (2 * eb b : ℝ) (hb b) ∪
        {x : Word | x.length = hb b ∧ ∃ s, lb b < s ∧ s ≤ hb b ∧
          (∀ i, lb b ≤ i → i < s → (Word.valSum (x.take i) : ℤ) < barrier b u i) ∧
          barrier b u s + K < (Word.valSum (x.take s) : ℤ)} := by
  have hlh : lb b < hb b := (lb_le_self b).trans_lt (lt_hb (by omega))
  have hHl := deficitFamily_barrier_lb b u
  have hHh := deficitFamily_barrier_hb b u
  rintro x ⟨hx, hnot⟩
  by_cases h1 : barrier b u (lb b) ≤ (Word.valSum (x.take (lb b)) : ℤ)
  · refine Or.inl (Or.inl ⟨hx, List.length_take_of_le (by omega), ?_⟩)
    have hint : 2 * (lb b : ℤ) + 2 * eb b ≤ Word.valSum (x.take (lb b)) := by omega
    have hreal : 2 * (lb b : ℝ) + 2 * eb b ≤ Word.valSum (x.take (lb b)) := by
      exact_mod_cast hint
    exact (by linarith : (2 * eb b : ℝ) ≤ _).trans (le_abs_self _)
  by_cases h2 : (Word.valSum x : ℤ) < barrier b u (hb b)
  · refine Or.inl (Or.inr ⟨hx, ?_⟩)
    have hint : (Word.valSum x : ℤ) + 2 * eb b ≤ 2 * hb b := by omega
    have hreal : (Word.valSum x : ℝ) + 2 * eb b ≤ 2 * hb b := by exact_mod_cast hint
    rw [abs_sub_comm]
    exact (by linarith : (2 * eb b : ℝ) ≤ _).trans (le_abs_self _)
  have hex : ∃ s, lb b < s ∧ s ≤ hb b ∧
      barrier b u s ≤ (Word.valSum (x.take s) : ℤ) :=
    ⟨hb b, hlh, le_rfl, by
      rw [List.take_of_length_le hx.le]
      omega⟩
  classical
  set s := Nat.find hex
  obtain ⟨hs1, hs2, hs3⟩ := Nat.find_spec hex
  have hbelow : ∀ i, lb b ≤ i → i < s →
      (Word.valSum (x.take i) : ℤ) < barrier b u i := by
    intro i hi his
    rcases hi.eq_or_lt with rfl | hi'
    · exact lt_of_not_ge h1
    · exact lt_of_not_ge fun h => Nat.find_min hex his ⟨hi', by omega, h⟩
  by_cases hK : (Word.valSum (x.take s) : ℤ) ≤ barrier b u s + K
  · refine absurd ⟨x.take s, ?_, List.take_prefix _ _⟩ hnot
    have hlen : (x.take s).length = s := List.length_take_of_le (by omega)
    refine ⟨by rw [hlen]; exact hs1, by rw [hlen]; exact hs2, ?_, by rw [hlen]; exact hs3,
      by rw [hlen]; exact hK⟩
    intro i hi his
    rw [hlen] at his
    rw [List.take_take, Nat.min_eq_left his.le]
    exact hbelow i hi his
  · exact Or.inr ⟨hx, s, hs1, hs2, hbelow, lt_of_not_ge hK⟩

/-- The concentration bound at a time `0 < t ≤ 2b` with deviation `2e_b`. -/
private theorem geomMass_valSumDevSet_two_mul_eb_le {b t : ℕ} (ht0 : 0 < t) (ht2 : t ≤ 2 * b) :
    geomMass (valSumDevSet (2 * eb b : ℝ) t) ≤ ENNReal.ofReal (2 * exp (-(b / 160000 : ℝ))) := by
  refine (geomMass_abs_valSum_sub_ge_le t _ (by positivity)).trans ?_
  gcongr
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht0
  have ht2' : (t : ℝ) ≤ 2 * b := by exact_mod_cast ht2
  have he : (b : ℝ) ≤ 100 * eb b := by linarith [(le_max_right _ _).trans (eb_lower b)]
  refine le_min ?_ (by linarith)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Deficit of a full first-crossing family.** For `K ≥ 0` and `0 ≤ u ≤ 2 r_b`,
`1 - 𝐩(𝒲(b, u, K)) ≤ 2^{140}/b^6 + 2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_deficit_family"]
theorem one_sub_geomMass_firstCrossing_le (b : ℕ) {u : ℤ} (hu0 : 0 ≤ u)
    (hu : u ≤ 2 * rb b) (K : ℕ) :
    1 - geomMass (firstCrossing b u K) ≤ 2 ^ 140 / (b : ℝ≥0∞) ^ 6 + 2⁻¹ ^ (K + 1) := by
  by_cases hsmall : b < 2
  · refine tsub_le_self.trans (le_add_right ?_)
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · simp [ENNReal.div_zero (pow_ne_zero 140 two_ne_zero)]
    · simp [one_le_pow₀ (one_le_two : (1 : ℝ≥0∞) ≤ 2)]
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlpos : 0 < lb b := by rw [lb_eq]; omega
  have hlh : lb b < hb b := (lb_le_self b).trans_lt (lt_hb (by omega))
  have hcover := setOf_not_prefix_firstCrossing_subset hu0 hu K (by omega)
  have hY := one_sub_geomMass_eq_geomMass_setOf_not_prefix_mem (isPrefixFree_firstCrossing b u K)
    (h := hb b) fun w hw => length_le_hb_of_mem_firstCrossing hw
  set D1 := {x : Word | x.length = hb b ∧ x.take (lb b) ∈ valSumDevSet (2 * eb b : ℝ) (lb b)}
  set O := {x : Word | x.length = hb b ∧ ∃ s, lb b < s ∧ s ≤ hb b ∧
      (∀ i, lb b ≤ i → i < s → (Word.valSum (x.take i) : ℤ) < barrier b u i) ∧
      barrier b u s + K < (Word.valSum (x.take s) : ℤ)}
  have hD1 : geomMass D1 = geomMass (valSumDevSet (2 * eb b : ℝ) (lb b)) :=
    geomMass_setOf_take_mem hlh.le fun w hw => hw.1
  calc 1 - geomMass (firstCrossing b u K)
      ≤ geomMass D1 + geomMass (valSumDevSet (2 * eb b : ℝ) (hb b)) + geomMass O := by
        rw [hY]
        refine (geomMass_mono hcover).trans ((geomMass_union_le _ _).trans ?_)
        gcongr
        exact geomMass_union_le _ _
    _ ≤ (ENNReal.ofReal (2 * exp (-(b / 160000 : ℝ))) +
          ENNReal.ofReal (2 * exp (-(b / 160000 : ℝ)))) + 2⁻¹ ^ (K + 1) := by
        rw [hD1]
        gcongr
        · exact geomMass_valSumDevSet_two_mul_eb_le hlpos ((lb_le_self b).trans (by omega))
        · exact geomMass_valSumDevSet_two_mul_eb_le (by omega) (hb_le_two_mul b)
        · exact geomMass_overshoot_le b u K
    _ ≤ ENNReal.ofReal (2 ^ 140 / (b : ℝ) ^ 6) + 2⁻¹ ^ (K + 1) := by
        gcongr
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith [deficitFamily_real_bound hbpos])
    _ = 2 ^ 140 / (b : ℝ≥0∞) ^ 6 + 2⁻¹ ^ (K + 1) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hbpos.le,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

end CollatzPosDens
