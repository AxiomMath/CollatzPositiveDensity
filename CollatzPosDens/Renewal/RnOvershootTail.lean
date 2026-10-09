/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnOccupation
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnOccupationValue
public import CollatzPosDens.Renewal.RnPascalTotal
public import CollatzPosDens.Renewal.RnTerminalSplit
public import CollatzPosDens.Renewal.RnVpgfTilt

/-!
# Overshoot tail of the first-passage law

For integers `s ≥ 64` and `X ≥ 1`, the mass that the first-passage law `F_s` puts on the points
whose second coordinate is at least `s + X` satisfies
`∑_{r ∈ ℤ} ∑_{ℓ ≥ s + X} F_s(r, ℓ) < 9 (25/27)^X`.

Let `y = 27/25`. By the terminal-step decomposition,
`F_s(r, ℓ) = ∑_{q ≥ 0} ∑_{p = 0}^{s} η(q + 1, ℓ - s + p) 𝒢(r - q - 1, s - p)` for `ℓ > s`.
Summing over `r ∈ ℤ` turns the Green's function into the renewal occupation `𝗎(s - p)`. On the
range `ℓ ≥ s + X` the letter `l = ℓ - s + p` is at least `X + p`, so
`η(q + 1, l) ≤ y^{-(X + p)} η(q + 1, l) y^l`, and summing over `q` and `ℓ` gives at most
`y^{-(X + p)} 𝖵(y)`. Hence the left side is at most `𝖵(y) y^{-X} ∑_{p = 0}^{s} 𝗎(s - p) y^{-p}`.
By the value of the occupation, `𝗎(m) ≤ 5/64 + [m = 0] + 3/16 [m = 4] + 1/8 [m = 5]`, so the last
sum is at most `135/128 + (25/27)^{64} (1 + (3/16) y^4 + (1/8) y^5) ≤ 135/128 + 9/128 = 9/8`.
With `𝖵(y) < 8` the left side is less than `9 (25/27)^X`.

## Main results

* `CollatzPosDens.tsum_firstPassageLaw_overshoot_lt`: the overshoot tail bound.

## Implementation notes

The double sum is a sum of nonnegative terms which might a priori diverge, so it is taken in
`[0, ∞]`: each value `F_s(r, ℓ) ≥ 0` is embedded by `ENNReal.ofReal`, the inner sum ranges over
the subtype `{ℓ : ℤ // s + X ≤ ℓ}`, and the bound is the embedding of the real number
`9 (25/27)^X`. The proof bounds the sum by `(9/8) (25/27)^X 𝖵(27/25)`; the slightly sharper
occupation bound keeping the term `3/64 [m = 6]` is not needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.4.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- `𝗎(m) ≤ 5/64 + [m = 0] + 3/16 [m = 4] + 1/8 [m = 5]`, as a real number. -/
private lemma occ_le (m : ℤ) :
    (if m = 0 then 1 else 0) + 3 / 16 * (if m = 4 then 1 else 0) +
      1 / 8 * (if m = 5 then 1 else 0) + 3 / 64 * (if 6 ≤ m then 1 else 0) +
      1 / 32 * (if 7 ≤ m then 1 else 0) ≤
    (5 / 64 : ℝ) + (if m = 0 then 1 else 0) + 3 / 16 * (if m = 4 then 1 else 0) +
      1 / 8 * (if m = 5 then 1 else 0) := by
  split_ifs <;> norm_num

/-- The real occupation value, `𝗎(m)` without the embedding into `[0, ∞]`. -/
private noncomputable def occVal (m : ℤ) : ℝ :=
  (if m = 0 then 1 else 0) + 3 / 16 * (if m = 4 then 1 else 0) +
    1 / 8 * (if m = 5 then 1 else 0) + 3 / 64 * (if 6 ≤ m then 1 else 0) +
    1 / 32 * (if 7 ≤ m then 1 else 0)

private lemma occVal_nonneg (m : ℤ) : 0 ≤ occVal m := by
  unfold occVal
  split_ifs <;> norm_num

/-- The weighted occupation sum: `∑_{p = 0}^{s} (25/27)^p 𝗎(s - p) ≤ 9/8` for `s ≥ 64`. -/
private lemma sum_occ_le (s : ℕ) (hs : 64 ≤ s) :
    ∑ p ∈ Finset.range (s + 1), (25 / 27 : ℝ) ^ p * occVal ((s : ℤ) - p) ≤ 9 / 8 := by
  set q : ℝ := 25 / 27
  have hq0 : 0 ≤ q := by norm_num [q]
  have hpt : ∀ p ∈ Finset.range (s + 1), q ^ p * occVal ((s : ℤ) - p) ≤
      5 / 64 * q ^ p + ((if p = s then q ^ p else 0) + 3 / 16 * (if p = s - 4 then q ^ p else 0) +
        1 / 8 * (if p = s - 5 then q ^ p else 0)) := by
    intro p hp
    rw [Finset.mem_range] at hp
    have h := occ_le ((s : ℤ) - p)
    have e0 : ((s : ℤ) - p = 0) ↔ p = s := by omega
    have e4 : ((s : ℤ) - p = 4) ↔ p = s - 4 := by omega
    have e5 : ((s : ℤ) - p = 5) ↔ p = s - 5 := by omega
    simp only [e0, e4, e5] at h
    unfold occVal
    simp only [e0, e4, e5]
    have := mul_le_mul_of_nonneg_left h (pow_nonneg hq0 p)
    split_ifs at this ⊢ <;> nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_range, show s < s + 1 by omega, show s - 4 < s + 1 by omega,
    show s - 5 < s + 1 by omega, ite_true]
  have hgeom : ∑ i ∈ Finset.range (s + 1), q ^ i ≤ 27 / 2 := by
    rw [geom_sum_eq (by norm_num [q])]
    have : 0 ≤ q ^ (s + 1) := pow_nonneg hq0 _
    rw [div_le_iff_of_neg (by norm_num [q])]
    norm_num [q] at this ⊢
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 64 := ⟨s - 64, by omega⟩
  rw [show t + 64 - 4 = t + 60 by omega, show t + 64 - 5 = t + 59 by omega, pow_add, pow_add,
    pow_add]
  have hqt : q ^ t ≤ 1 := pow_le_one₀ hq0 (by norm_num [q])
  have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
  have hc : q ^ 64 + 3 / 16 * q ^ 60 + 1 / 8 * q ^ 59 ≤ 9 / 128 := by norm_num [q]
  have hc0 : 0 ≤ q ^ 64 + 3 / 16 * q ^ 60 + 1 / 8 * q ^ 59 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc hqt0, mul_le_mul_of_nonneg_right hqt hc0]

/-- The weighted occupation sum in `[0, ∞]`:
`∑_{p = 0}^{s} (25/27)^{X + p} 𝗎(s - p) ≤ (9/8) (25/27)^X` for `s ≥ 64`. -/
private lemma sum_ofReal_mul_renewalOccupation_le (s X : ℕ) (hs : 64 ≤ s) :
    ∑ p ∈ Finset.range (s + 1),
        ENNReal.ofReal ((25 / 27 : ℝ) ^ (X + p)) * renewalOccupation ((s : ℤ) - p) ≤
      ENNReal.ofReal (9 / 8 * (25 / 27) ^ X) := by
  have hu : ∀ m : ℤ, renewalOccupation m = ENNReal.ofReal (occVal m) := fun m ↦
    renewalOccupation_eq m
  simp only [hu]
  rw [← Finset.sum_congr rfl fun p _ ↦ ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_sum_of_nonneg fun p _ ↦ mul_nonneg (by positivity) (occVal_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [pow_add, mul_assoc, ← Finset.mul_sum]
  rw [mul_comm (9 / 8 : ℝ)]
  exact mul_le_mul_of_nonneg_left (sum_occ_le s hs) (by positivity)

/-- The terminal-step decomposition, tilted by `(27/25)^l`: a pointwise bound on `F_s(r, ℓ)` for
`ℓ ≥ s + X`. -/
private lemma ofReal_firstPassageLaw_le_tsum (s X : ℕ) (hX : 1 ≤ X) (r : ℤ)
    (ℓ : {ℓ : ℤ // (s : ℤ) + X ≤ ℓ}) :
    ENNReal.ofReal (firstPassageLaw s (r, ℓ)) ≤
      ∑' q : ℕ, ∑ p ∈ Finset.range (s + 1), ENNReal.ofReal ((25 / 27 : ℝ) ^ (X + p)) *
        (ENNReal.ofReal (holdLaw (q + 1) (ℓ.1 - s + p) * (27 / 25 : ℝ) ^ (ℓ.1 - s + p)) *
          ENNReal.ofReal (green (r - q - 1) (s - p))) := by
  rw [firstPassageLaw_eq_tsum_sum_holdLaw_mul_green s r ℓ (by have := ℓ.2; omega)]
  refine (ofReal_tsum_le_tsum_ofReal fun q ↦ Finset.sum_nonneg fun p _ ↦
    mul_nonneg (holdLaw_nonneg _ _) (green_nonneg _ _)).trans (ENNReal.tsum_le_tsum fun q ↦ ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun p _ ↦ mul_nonneg (holdLaw_nonneg _ _) (green_nonneg _ _)]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  rw [← ENNReal.ofReal_mul (holdVpgf_term_nonneg (by norm_num) _ _),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hy : 1 ≤ (25 / 27 : ℝ) ^ (X + p) * (27 / 25 : ℝ) ^ (ℓ.1 - s + p) := by
    have : (25 / 27 : ℝ) ^ (X + p) = (27 / 25 : ℝ) ^ (-((X + p : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      norm_num
    rw [this, ← zpow_add₀ (by norm_num)]
    exact one_le_zpow₀ (by norm_num) (by have := ℓ.2; push_cast; omega)
  calc holdLaw (q + 1) (ℓ.1 - s + p) * green (r - q - 1) (s - p)
      ≤ ((25 / 27 : ℝ) ^ (X + p) * (27 / 25 : ℝ) ^ (ℓ.1 - s + p)) *
          (holdLaw (q + 1) (ℓ.1 - s + p) * green (r - q - 1) (s - p)) :=
        le_mul_of_one_le_left (mul_nonneg (holdLaw_nonneg _ _) (green_nonneg _ _)) hy
    _ = _ := by ring

/-- **Overshoot tail of the first-passage law.** For integers `s ≥ 64` and `X ≥ 1`,
`∑_{r ∈ ℤ} ∑_{ℓ ≥ s + X} F_s(r, ℓ) < 9 (25/27)^X`, the sum taken in `[0, ∞]`. -/
@[collatz_pos_dens "lem_rn_overshoot_tail"]
theorem tsum_firstPassageLaw_overshoot_lt (s X : ℕ) (hs : 64 ≤ s) (hX : 1 ≤ X) :
    ∑' r : ℤ, ∑' ℓ : {ℓ : ℤ // (s : ℤ) + X ≤ ℓ}, ENNReal.ofReal (firstPassageLaw s (r, ℓ)) <
      ENNReal.ofReal (9 * (25 / 27) ^ X) := by
  set y : ℝ := 27 / 25
  set w : ℕ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal ((25 / 27 : ℝ) ^ (X + p))
  set A : ℕ → ℕ → {ℓ : ℤ // (s : ℤ) + X ≤ ℓ} → ℝ≥0∞ := fun p q ℓ ↦
    ENNReal.ofReal (holdLaw (q + 1) (ℓ.1 - s + p) * y ^ (ℓ.1 - s + p))
  set B : ℕ → ℕ → ℤ → ℝ≥0∞ := fun p q r ↦ ENNReal.ofReal (green (r - q - 1) (s - p))
  have hB : ∀ p q, ∑' r, B p q r = renewalOccupation ((s : ℤ) - p) := by
    intro p q
    simp only [B, renewalOccupation_def, sub_sub]
    exact (Equiv.subRight ((q : ℤ) + 1)).tsum_eq (fun j ↦ ENNReal.ofReal (green j (s - p)))
  have hA : ∀ p, ∑' q, ∑' ℓ, A p q ℓ ≤ holdVpgf y := by
    intro p
    rw [holdVpgf_eq_tsum_succ, ENNReal.tsum_prod']
    exact ENNReal.tsum_le_tsum fun q ↦ ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun ℓ : {ℓ : ℤ // (s : ℤ) + X ≤ ℓ} ↦ ℓ.1 - s + p)
      (fun a b h ↦ Subtype.ext (by simpa using h))
      (fun l ↦ ENNReal.ofReal (holdLaw (q + 1) l * y ^ l))
  have hre : ∑' r : ℤ, ∑' ℓ : {ℓ : ℤ // (s : ℤ) + X ≤ ℓ},
      ∑' q : ℕ, ∑ p ∈ Finset.range (s + 1), w p * (A p q ℓ * B p q r) =
      ∑ p ∈ Finset.range (s + 1), w p * renewalOccupation ((s : ℤ) - p) *
        ∑' q, ∑' ℓ, A p q ℓ := by
    simp_rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp_rw [ENNReal.tsum_comm (α := {ℓ : ℤ // (s : ℤ) + X ≤ ℓ}), ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hB, ENNReal.tsum_mul_right]
    ring
  calc ∑' r : ℤ, ∑' ℓ : {ℓ : ℤ // (s : ℤ) + X ≤ ℓ}, ENNReal.ofReal (firstPassageLaw s (r, ℓ))
      ≤ ∑' r : ℤ, ∑' ℓ : {ℓ : ℤ // (s : ℤ) + X ≤ ℓ},
          ∑' q : ℕ, ∑ p ∈ Finset.range (s + 1), w p * (A p q ℓ * B p q r) :=
        ENNReal.tsum_le_tsum fun r ↦ ENNReal.tsum_le_tsum fun ℓ ↦
          ofReal_firstPassageLaw_le_tsum s X hX r ℓ
    _ = _ := hre
    _ ≤ ∑ p ∈ Finset.range (s + 1), w p * renewalOccupation ((s : ℤ) - p) * holdVpgf y :=
        Finset.sum_le_sum fun p _ ↦ by gcongr; exact hA p
    _ = (∑ p ∈ Finset.range (s + 1), w p * renewalOccupation ((s : ℤ) - p)) * holdVpgf y :=
        Finset.sum_mul _ _ _ |>.symm
    _ ≤ ENNReal.ofReal (9 / 8 * (25 / 27) ^ X) * holdVpgf y := by
        gcongr
        exact sum_ofReal_mul_renewalOccupation_le s X hs
    _ < ENNReal.ofReal (9 / 8 * (25 / 27) ^ X) * 8 := by
        rw [mul_comm _ (holdVpgf y), mul_comm _ (8 : ℝ≥0∞)]
        exact ENNReal.mul_lt_mul_left (by simp) ENNReal.ofReal_ne_top holdVpgf_tilt_lt
    _ = ENNReal.ofReal (9 * (25 / 27) ^ X) := by
        rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

end CollatzPosDens
