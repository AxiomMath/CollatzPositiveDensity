/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.Log3Bounds
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Width
public import CollatzPosDens.FirstCrossing.FcComplement
public import CollatzPosDens.FirstCrossing.FcGeomTail
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.FirstCrossing.FcReflection
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.Overshoot

/-!
# Binomial lower bound for central families

Let `u ≥ 256` and `K ≥ 0` be integers, `w = wd(u)`, `v₊ = ⌊83w/200⌋`, `v₋ = v₊ + 1`,
`h₊ = u - w`, `h₋ = u + w`, `n₊ = 2h₊ + v₊ - 1` and `n₋ = 2h₋ - v₋`. Then
$$\mathbf{p}(\mathcal{C}(u,K)) \ge 1 - 2\cdot 2^{-n_+}\sum_{t=0}^{h_+-1}\binom{n_+}{t}
  - 2^{-n_-}\sum_{t=0}^{h_- - v_-}\binom{n_-}{t} - 2^{-(K+1)}.$$

The central family is prefix-disjoint, so `1 - 𝐩(𝒞(u, K))` is the mass of the words
`v ∈ ℤ_{≥1}^{h_u}` with no prefix in `𝒞(u, K)`. Such a word either crosses the barrier
`H = H_{u,r_u}` too early (at a time `ℓ_u ≤ i < h₊`), or is still below it at time `h₋`, or
overshoots it by more than `K` at its first crossing. An early crossing forces the centred walk
`A_i(v) - 2i` to reach `v₊` within `h₊` steps, which by the reflection bound and the binomial
form of geometric tails has mass at most `2 · 2^{-n₊} ∑_{t < h₊} (n₊ choose t)`; staying below
at time `h₋` forces `A_{h₋}(v) ≤ n₋`, of mass `2^{-n₋} ∑_{t ≤ h₋ - v₋} (n₋ choose t)`; and the
overshoot has mass at most `2^{-(K+1)}`.

## Main results

* `CollatzPosDens.geomMass_centralFamily_ge_binomial`: the lower bound above.

## Implementation notes

All parameters are natural numbers; the subtractions defining `h₊`, `n₊`, `n₋` and the upper
summation index `h₋ - v₋` are never truncated, since `w < u` and `v₋ ≤ h₋`. The mass lives in
`ℝ≥0∞`, where subtraction is truncated; as `𝐩(𝒞(u, K)) ≥ 0`, the truncated inequality is
equivalent to the real one. The sum `∑_{t=0}^{h₋-v₋}` is a sum over `Finset.range (h₋ - v₋ + 1)`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- `200 B(j) < 317 j + 200`, from `log₂ 3 ≤ 317/200`. -/
private theorem fcBinomialLower_ceilLog3_bound (j : ℕ) : 200 * ceilLog3 j < 317 * j + 200 := by
  have h1 := ceilLog3_lt_mul_logb_add_one j
  have h2 := logb_two_three_bounds.2
  have h3 : (200 * ceilLog3 j : ℝ) < 317 * j + 200 := by
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  exact_mod_cast h3

/-- The binomial identity `∑_{t < a} (n choose t) + ∑_{t < b} (n choose t) = 2 ^ n` for
`a + b = n + 1`. -/
private theorem fcBinomialLower_choose_sum {n a b : ℕ} (hab : a + b = n + 1) :
    ∑ t ∈ Finset.range a, n.choose t + ∑ t ∈ Finset.range b, n.choose t = 2 ^ n := by
  rw [← Nat.sum_range_choose n, ← hab, Finset.sum_range_add]
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  rw [show a + x = n - (b - 1 - x) by omega, Nat.choose_symm (by omega)]

/-- The lower tail `𝐩(A_h ≤ n) = 2^{-n} ∑_{t < n + 1 - h} (n choose t)` for `h ≤ n + 1`. -/
theorem geomMass_setOf_length_eq_valSum_le {h n : ℕ} (hn : h ≤ n + 1) :
    geomMass {x : Word | x.length = h ∧ x.valSum ≤ n} =
      2⁻¹ ^ n * ∑ t ∈ Finset.range (n + 1 - h), (n.choose t : ℝ≥0∞) := by
  set a := geomMass {x : Word | x.length = h ∧ n + 1 ≤ x.valSum} with ha
  have hsplit : geomMass {x : Word | x.length = h ∧ x.valSum ≤ n} + a = 1 := by
    rw [ha, ← geomMass_union, ← geomMass_setOf_length_eq h]
    · congr 1
      ext x
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      omega
    · rw [Set.disjoint_left]
      rintro x ⟨-, hx⟩ ⟨-, hx'⟩
      omega
  have hsum : 2⁻¹ ^ n * ∑ t ∈ Finset.range (n + 1 - h), (n.choose t : ℝ≥0∞) + a = 1 := by
    rw [ha, geomMass_setOf_length_eq_le_valSum h (n + 1) (by omega), Nat.add_sub_cancel,
      ← mul_add, show ∑ t ∈ Finset.range (n + 1 - h), (n.choose t : ℝ≥0∞) +
        ∑ t ∈ Finset.range h, (n.choose t : ℝ≥0∞) = 2 ^ n by
          exact_mod_cast fcBinomialLower_choose_sum (by omega : n + 1 - h + h = n + 1),
      ← ENNReal.inv_pow]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit ▸ le_add_self)
  exact (ENNReal.add_left_inj hatop).1 (hsplit.trans hsum.symm)

/-- The centred condition `v ≤ A_h - 2h` is the natural-number condition `2h + v ≤ A_h`. -/
theorem setOf_length_eq_le_valSum_sub_two_mul (h v : ℕ) :
    {x : Word | x.length = h ∧ (v : ℝ) ≤ (x.valSum : ℝ) - 2 * h} =
      {x : Word | x.length = h ∧ 2 * h + v ≤ x.valSum} := by
  ext x
  simp only [Set.mem_ofPred_eq, le_sub_iff_add_le]
  rw [add_comm (v : ℝ)]
  norm_cast

/-- Crossing the barrier at an early time `i < h₊` lifts the centred walk to `v₊`. -/
theorem cast_le_sub_two_mul_of_barrier_le {u i s : ℕ} (hi : i < u - wd u)
    (h : barrier u (rb u) i ≤ s) : ((83 * wd u / 200 : ℕ) : ℝ) ≤ s - 2 * i := by
  rw [barrier_of_ge _ (by omega)] at h
  have := fcBinomialLower_ceilLog3_bound (u - i)
  have := Nat.mul_div_le (83 * wd u) 200
  have hui : ((u - i : ℕ) : ℤ) = u - i := by push_cast [show i ≤ u by omega]; ring
  have hz : ((83 * wd u / 200 : ℕ) : ℤ) ≤ s - 2 * i := by omega
  have := (Int.cast_le (R := ℝ)).2 hz
  push_cast at this
  exact this

/-- Being below the barrier at time `h₋` forces `A_{h₋} ≤ n₋`. -/
theorem le_of_lt_barrier_add_wd {u s : ℕ} (h : (s : ℤ) < barrier u (rb u) (u + wd u)) :
    s ≤ 2 * (u + wd u) - (83 * wd u / 200 + 1) := by
  rw [barrier_of_le _ (by omega), show u + wd u - u = wd u by omega] at h
  have := fcBinomialLower_ceilLog3_bound (wd u)
  have := Nat.mul_div_le (83 * wd u) 200
  omega

/-- A first crossing at a time `s ∈ [h₊, h₋]` with overshoot at most `K` is in `𝒞(u, K)`. -/
theorem take_mem_centralFamily {u K s : ℕ} (hu : 256 ≤ u) {v : Word} (hv : v.length = hb u)
    (hs₁ : u - wd u ≤ s) (hs₂ : s ≤ u + wd u)
    (hbelow : ∀ i, lb u ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier u (rb u) i)
    (hcross : barrier u (rb u) s ≤ (Word.valSum (v.take s) : ℤ))
    (hover : (Word.valSum (v.take s) : ℤ) ≤ barrier u (rb u) s + K) :
    v.take s ∈ centralFamily u K := by
  have := wd_le_floor_sub_one u
  have := lb_eq u
  have := hb_eq u
  have hlen : (v.take s).length = s := by simp only [List.length_take, hv]; omega
  rw [mem_centralFamily_of_large hu, mem_firstCrossing, hlen]
  refine ⟨⟨by omega, by omega, fun i hi₁ hi₂ => ?_, hcross, hover⟩, hs₁, hs₂⟩
  rw [List.take_take, min_eq_left hi₂.le]
  exact hbelow i hi₁ hi₂

/-- A word with no prefix in `𝒞(u, K)` crosses the barrier too early, is still below it at
time `h₋`, or overshoots it by more than `K` at its first crossing. -/
theorem setOf_not_prefix_centralFamily_subset {u : ℕ} (hu : 256 ≤ u) (K : ℕ) :
    {v : Word | v.length = hb u ∧ ¬ ∃ c ∈ centralFamily u K, c <+: v} ⊆
      {v : Word | v.length = hb u ∧ v.take (u - wd u) ∈ {x : Word | x.length = u - wd u ∧
        ∃ i, 1 ≤ i ∧ i ≤ u - wd u ∧
          ((83 * wd u / 200 : ℕ) : ℝ) ≤ (Word.valSum (x.take i) : ℝ) - 2 * i}} ∪
      {v : Word | v.length = hb u ∧ v.take (u + wd u) ∈ {x : Word | x.length = u + wd u ∧
        x.valSum ≤ 2 * (u + wd u) - (83 * wd u / 200 + 1)}} ∪
      {v : Word | v.length = hb u ∧ ∃ s, lb u < s ∧ s ≤ hb u ∧
        (∀ i, lb u ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier u (rb u) i) ∧
        barrier u (rb u) s + K < (Word.valSum (v.take s) : ℤ)} := by
  rintro v ⟨hv, hvC⟩
  by_contra hnot
  simp only [Set.mem_union, not_or] at hnot
  obtain ⟨⟨hn₁, hn₂⟩, hn₃⟩ := hnot
  have := wd_le_floor_sub_one u
  have := lb_eq u
  have := hb_eq u
  have hearly : ∀ i, lb u ≤ i → i < u - wd u →
      (Word.valSum (v.take i) : ℤ) < barrier u (rb u) i := by
    refine fun i hi₁ hi₂ => lt_of_not_ge fun hge => hn₁ ⟨hv, ?_, i, by omega, hi₂.le, ?_⟩
    · simp only [List.length_take, hv]
      omega
    · rw [List.take_take, min_eq_left hi₂.le]
      exact cast_le_sub_two_mul_of_barrier_le hi₂ hge
  have hlate : barrier u (rb u) (u + wd u) ≤ (Word.valSum (v.take (u + wd u)) : ℤ) :=
    le_of_not_gt fun hlt => hn₂ ⟨hv, by simp only [List.length_take, hv]; omega,
      le_of_lt_barrier_add_wd hlt⟩
  have hex : ∃ s, u - wd u ≤ s ∧ barrier u (rb u) s ≤ (Word.valSum (v.take s) : ℤ) :=
    ⟨_, by omega, hlate⟩
  classical
  have hs := Nat.find_spec hex
  have hsm : Nat.find hex ≤ u + wd u := Nat.find_min' hex ⟨by omega, hlate⟩
  have hbelow : ∀ i, lb u ≤ i → i < Nat.find hex →
      (Word.valSum (v.take i) : ℤ) < barrier u (rb u) i := fun i hi₁ hi₂ =>
    if hip : i < u - wd u then hearly i hi₁ hip
    else lt_of_not_ge fun h => Nat.find_min hex hi₂ ⟨by omega, h⟩
  refine hvC ⟨_, take_mem_centralFamily hu hv hs.1 hsm hbelow hs.2
    (le_of_not_gt fun hgt => hn₃ ⟨hv, _, ?_, ?_, hbelow, hgt⟩), List.take_prefix _ _⟩ <;> omega

/-- **Binomial lower bound for central families.** For `u ≥ 256` and `K ≥ 0`, with
`w = wd(u)`, `v₊ = ⌊83w/200⌋`, `v₋ = v₊ + 1`, `h₊ = u - w`, `h₋ = u + w`, `n₊ = 2h₊ + v₊ - 1` and
`n₋ = 2h₋ - v₋`,
`𝐩(𝒞(u, K)) ≥ 1 - 2 · 2^{-n₊} ∑_{t=0}^{h₊-1} (n₊ choose t)
  - 2^{-n₋} ∑_{t=0}^{h₋-v₋} (n₋ choose t) - 2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_fc_binomial_lower"]
theorem geomMass_centralFamily_ge_binomial {u : ℕ} (hu : 256 ≤ u) (K : ℕ) :
    1 - 2 * 2⁻¹ ^ (2 * (u - wd u) + 83 * wd u / 200 - 1) *
        ∑ t ∈ Finset.range (u - wd u),
          ((2 * (u - wd u) + 83 * wd u / 200 - 1).choose t : ℝ≥0∞) -
      2⁻¹ ^ (2 * (u + wd u) - (83 * wd u / 200 + 1)) *
        ∑ t ∈ Finset.range (u + wd u - (83 * wd u / 200 + 1) + 1),
          ((2 * (u + wd u) - (83 * wd u / 200 + 1)).choose t : ℝ≥0∞) -
      2⁻¹ ^ (K + 1) ≤ geomMass (centralFamily u K) := by
  set w := wd u
  set vp := 83 * w / 200
  set hp := u - w
  set hm := u + w
  set np := 2 * hp + vp - 1
  set nm := 2 * hm - (vp + 1)
  have := wd_le_floor_sub_one u
  have := hb_eq u
  have hvpw : 200 * vp ≤ 83 * w := Nat.mul_div_le _ _
  have hE1 : geomMass {v : Word | v.length = hb u ∧ v.take hp ∈ {x : Word | x.length = hp ∧
      ∃ i, 1 ≤ i ∧ i ≤ hp ∧ (vp : ℝ) ≤ (Word.valSum (x.take i) : ℝ) - 2 * i}} ≤
      2 * 2⁻¹ ^ np * ∑ t ∈ Finset.range hp, (np.choose t : ℝ≥0∞) := by
    rw [geomMass_setOf_take_mem (by omega) fun x hx => hx.1]
    refine (fcReflection_geomMass_le hp vp).trans_eq ?_
    rw [setOf_length_eq_le_valSum_sub_two_mul,
      geomMass_setOf_length_eq_le_valSum hp (2 * hp + vp) (by omega), mul_assoc]
  have hE2 : geomMass {v : Word | v.length = hb u ∧
      v.take hm ∈ {x : Word | x.length = hm ∧ x.valSum ≤ nm}} =
      2⁻¹ ^ nm * ∑ t ∈ Finset.range (hm - (vp + 1) + 1), (nm.choose t : ℝ≥0∞) := by
    rw [geomMass_setOf_take_mem (by omega) fun x hx => hx.1,
      geomMass_setOf_length_eq_valSum_le (by omega), show nm + 1 - hm = hm - (vp + 1) + 1 by omega]
  have htot : 1 ≤ 2 * 2⁻¹ ^ np * ∑ t ∈ Finset.range hp, (np.choose t : ℝ≥0∞) +
      2⁻¹ ^ nm * ∑ t ∈ Finset.range (hm - (vp + 1) + 1), (nm.choose t : ℝ≥0∞) +
      2⁻¹ ^ (K + 1) + geomMass (centralFamily u K) :=
    tsub_le_iff_right.1 <| (one_sub_geomMass_eq_geomMass_setOf_not_prefix_mem
      (fun x hx y hy hxy => isPrefixFree_firstCrossing u (rb u) K x hx.1 y hy.1 hxy)
      fun c hc => hc.1.2.1).trans_le <|
      (geomMass_mono (setOf_not_prefix_centralFamily_subset hu K)).trans <|
      (geomMass_union_le _ _).trans <| add_le_add
        ((geomMass_union_le _ _).trans (add_le_add hE1 hE2.le)) (geomMass_overshoot_le u (rb u) K)
  rw [tsub_le_iff_right, tsub_le_iff_right, tsub_le_iff_right]
  calc (1 : ℝ≥0∞) ≤ _ := htot
    _ = _ := by ring

end CollatzPosDens
